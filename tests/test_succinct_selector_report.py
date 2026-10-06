"""Adversarial checks for external limits, equivalence and report presentation."""
import contextlib
import hashlib
import io
import json
import math
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.reduction import contract_at
from s_only.root_selector import SelectorTable
from s_only.selector_parts.graph import Command
from s_only.succinct_selector import SuccinctSelectorTable, _DirectRow
from s_only.terms import App, S, nodes, prefix
from tools import succinct_selector_report as runner


DEADLINE = 100.0


def pair(rows, start=0):
    dense = SelectorTable(tuple(tuple(row) for row in rows), start)
    succinct = SuccinctSelectorTable(tuple(_DirectRow(q, row) for q, row in enumerate(dense.states)), start)
    return succinct, dense


def selecting(read_ticks=0):
    return pair([(Command('stay', q + 1),) * 6 for q in range(read_ticks)] +
                [(Command('Rdx', read_ticks + 1),) * 6, (Command('contracted'),) * 6])


def redex(z=S):
    return App(App(App(S, S), S), z)


def graph_digest(dense):
    digest = hashlib.sha256()
    for control, row in enumerate(dense.states):
        for observation, entry in enumerate(row):
            digest.update(f'{control}:{observation}:{entry.command}:{entry.next_state}\n'.encode('ascii'))
    return digest.hexdigest()


def fixture_for(term, paths, ticks):
    fixture = {'initial_prefix': prefix(term), 'steps': []}
    archived = []
    for index, (path, count) in enumerate(zip(paths, ticks), 1):
        term = contract_at(term, tuple(map(int, path)))
        digest = hashlib.sha256(prefix(term).encode('ascii')).hexdigest()
        fixture['steps'].append({'path': path, 'nodes': nodes(term), 'after_sha256': digest})
        archived.append({'contraction': index, 'address': path, 'selection_microticks': count,
                         'native_contractions': 1, 'after_nodes': nodes(term), 'after_sha256': digest})
    return fixture, archived


class SuccinctSelectorReportTests(unittest.TestCase):
    def setUp(self):
        clock = patch.object(runner.time, 'monotonic', return_value=0.0)
        clock.start()
        self.addCleanup(clock.stop)

    def select(self, table, term, **kwargs):
        limits = dict(max_ticks=10, max_total_ticks=100, used_ticks=0, deadline=DEADLINE)
        limits.update(kwargs)
        return runner.bounded_selection(table, term, **limits)

    def replay(self, table, fixture, archived, **kwargs):
        limits = dict(max_steps=2, max_ticks=10, max_total_ticks=100,
                      max_nodes=100, deadline=DEADLINE)
        limits.update(kwargs)
        return runner.replay(table, fixture, archived, **limits)

    def test_invalid_bounds_precede_both_compilations(self):
        cases = [{name: value} for name in ('max_states', 'max_metadata_records', 'max_steps',
                                            'max_ticks', 'max_total_ticks', 'max_nodes')
                 for value in (0, -1, True, 0.5, None)]
        cases += [{name: value} for name in ('max_seconds', 'max_compile_seconds')
                  for value in (0, -1, True, math.inf, math.nan, None)]
        cases += [{'max_appendant_bits': value} for value in (-1, 9, True, 1.0, None)]
        with patch.object(runner, 'compile_table') as succinct, patch.object(runner, 'selector_table') as dense:
            for arguments in cases:
                with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                    runner.report(**arguments)
            succinct.assert_not_called()
            dense.assert_not_called()

    def test_compile_limits_are_explicit(self):
        with patch.object(runner, 'compile_table', side_effect=RuntimeError('sentinel')) as compiler:
            with self.assertRaisesRegex(RuntimeError, 'sentinel'):
                runner.report()
        self.assertEqual(compiler.call_args.kwargs,
                         {'max_appendant_bits': 8, 'max_metadata_records': 100000,
                          'max_compile_seconds': 10})

    def test_graph_checks_all_entries_statuses_start_and_digest(self):
        compact, dense = selecting(2)
        result = runner.verify_graph(compact, dense, max_states=4, deadline=DEADLINE,
                                     expected_sha256=graph_digest(dense))
        self.assertFalse(hasattr(compact, 'states'))
        self.assertEqual(result['entries_checked'], 24)
        self.assertEqual(result['statuses_checked'], 4)
        self.assertEqual(result['status_counts'], {'read_only': 2, 'normal': 0, 'contracted': 1, 'Rdx': 1})
        self.assertEqual(result['control_table_sha256'], graph_digest(dense))

    def test_graph_cap_precedes_virtual_lookup_and_accepts_exact_boundary(self):
        compact, dense = selecting(2)
        with patch.object(SuccinctSelectorTable, 'transition', side_effect=AssertionError('enumerated')):
            with self.assertRaisesRegex(runner.ExperimentLimit, 'state bound'):
                runner.verify_graph(compact, dense, max_states=3, deadline=DEADLINE)
        runner.verify_graph(compact, dense, max_states=4, deadline=DEADLINE,
                            expected_sha256=graph_digest(dense))

    def test_invalid_graph_reference_mismatches_are_rejected(self):
        compact, dense = selecting(2)
        _, short = selecting(1)
        _, other_start = pair(dense.states, start=1)
        _, other_entry = pair(((Command('stay', 2),) * 6,) + dense.states[1:])
        _, other_status = pair(dense.states[:2] + ((Command('normal'),) * 6,) + dense.states[3:])
        for reference, message in ((short, 'state count'), (other_start, 'initial control'),
                                   (other_entry, 'entry mismatch'), (other_status, 'status mismatch')):
            with self.subTest(message=message), self.assertRaisesRegex(AssertionError, message):
                runner.verify_graph(compact, reference, max_states=4, deadline=DEADLINE)
        with self.assertRaisesRegex(AssertionError, 'archived text-row digest'):
            runner.verify_graph(compact, dense, max_states=4, deadline=DEADLINE, expected_sha256='0' * 64)
        with self.assertRaises(ValueError):
            pair(((Command('Rdx', 0),) * 6,))

    def test_graph_deadline_equality_stops_before_lookup(self):
        compact, dense = selecting()
        with patch.object(runner.time, 'monotonic', return_value=DEADLINE), \
             patch.object(SuccinctSelectorTable, 'transition', side_effect=AssertionError('enumerated')):
            with self.assertRaises(runner.ExperimentLimit):
                runner.verify_graph(compact, dense, max_states=2, deadline=DEADLINE)

    def test_per_invocation_and_cumulative_tick_caps_are_inclusive(self):
        table, _ = selecting(2)
        term = redex()
        state, ticks, digest = self.select(table, term, max_ticks=2, max_total_ticks=5, used_ticks=3)
        self.assertEqual((ticks, table.status(state.control)), (2, 'Rdx'))
        self.assertIs(state.cursor.focus, term)
        self.assertEqual(len(digest), 64)
        with patch.object(runner, 'step', wraps=runner.step) as step:
            with self.assertRaisesRegex(runner.ExperimentLimit, 'per-selection'):
                self.select(table, term, max_ticks=1)
            self.assertEqual(step.call_count, 1)
        with patch.object(runner, 'step', wraps=runner.step) as step:
            with self.assertRaisesRegex(runner.ExperimentLimit, 'cumulative'):
                self.select(table, term, max_total_ticks=4, used_ticks=3)
            self.assertEqual(step.call_count, 1)
        selected, _ = selecting()
        with patch.object(runner, 'step', side_effect=AssertionError('contracted early')):
            self.assertEqual(self.select(selected, term, max_total_ticks=1, used_ticks=1)[1], 0)

    def test_selection_resets_root_control_and_trace_each_invocation(self):
        table, _ = pair(((Command('L', 1),) * 6, (Command('Rdx', 2),) * 6,
                         (Command('contracted'),) * 6))
        term = App(redex(), S)
        with patch.object(runner, 'step', wraps=runner.step) as step:
            first = self.select(table, term)
            second = self.select(table, term)
        self.assertEqual(first, second)
        self.assertEqual(first[0].cursor.path, (0,))
        self.assertEqual(step.call_count, 2)
        for call in step.call_args_list:
            state = call.args[1]
            self.assertEqual((state.control, state.cursor.path), (table.start, ()))
            self.assertIs(state.cursor.focus, term)

    def test_selection_rejects_non_rdx_terminal_and_changed_tree(self):
        table, _ = pair(((Command('normal'),) * 6,))
        with self.assertRaisesRegex(AssertionError, 'unexpected terminal'):
            self.select(table, S)
        table, _ = selecting(1)
        with patch.object(runner, 'step', return_value=Configuration(1, Cursor.at(S))):
            with self.assertRaisesRegex(AssertionError, 'changed the current bare tree'):
                self.select(table, redex())

    def test_growth_limit_precedes_contraction_and_exact_limit_succeeds(self):
        table, _ = selecting()
        term = redex(redex())
        state = Configuration(table.start, Cursor.at(term))
        expected_nodes = nodes(term) + nodes(term.right) - 1
        with patch.object(runner, 'step', side_effect=AssertionError('contracted')):
            with self.assertRaisesRegex(runner.ExperimentLimit, 'next contraction'):
                runner.contract_once(table, state, term, max_nodes=expected_nodes - 1, deadline=DEADLINE)
        actual = runner.contract_once(table, state, term, max_nodes=expected_nodes, deadline=DEADLINE)
        self.assertEqual(nodes(actual), expected_nodes)
        self.assertEqual(actual, contract_at(term, ()))

    def test_exact_single_contraction_rejects_wrong_same_size_replacement(self):
        table, _ = selecting()
        term = redex()
        selected = Configuration(0, Cursor.at(term))
        # S S S S and its correct replacement both have seven nodes; mere
        # size checking would accept an unchanged tree pretending to contract.
        fake = Configuration(1, Cursor.at(term))
        self.assertEqual(nodes(term), nodes(contract_at(term, ())))
        with patch.object(runner, 'step', return_value=fake):
            with self.assertRaisesRegex(AssertionError, 'exact single-contraction'):
                runner.contract_once(table, selected, term, max_nodes=7, deadline=DEADLINE)

    def test_immediate_absorption_is_checked_by_object_identity(self):
        table, _ = selecting()
        term = redex()
        selected = Configuration(0, Cursor.at(term))
        real_step = runner.step
        calls = []

        def nonabsorbing(controller, state):
            calls.append(state)
            if controller.status(state.control) == 'contracted':
                return Configuration(state.control, state.cursor)
            return real_step(controller, state)

        with patch.object(runner, 'step', side_effect=nonabsorbing):
            with self.assertRaisesRegex(AssertionError, 'immediately absorbing'):
                runner.contract_once(table, selected, term, max_nodes=7, deadline=DEADLINE)
        self.assertEqual(len(calls), 2)

    def test_native_limit_stops_before_second_selection(self):
        table, _ = selecting(1)
        term = redex()
        fixture, archived = fixture_for(term, [''], [1])
        fixture['steps'] *= 2
        archived *= 2
        with patch.object(runner, 'encode', return_value=term), \
             patch.object(runner, 'bounded_selection', wraps=runner.bounded_selection) as select:
            with self.assertRaisesRegex(runner.ExperimentLimit, 'native-contraction'):
                self.replay(table, fixture, archived, max_steps=1)
            self.assertEqual(select.call_count, 1)

    def test_replay_checks_archive_only_after_independent_selection(self):
        table, _ = selecting(1)
        term = redex()
        fixture, archived = fixture_for(term, [''], [1])
        with patch.object(runner, 'encode', return_value=term):
            result = self.replay(table, fixture, archived, max_steps=1, max_ticks=1,
                                 max_total_ticks=1, max_nodes=7)
        self.assertEqual(result['native_contractions_checked'], 1)
        self.assertEqual(result['total_selection_microticks'], 1)
        self.assertEqual(result['peak_expanded_nodes'], 7)
        self.assertEqual(result['fixture_selections'][0]['address'], '')
        for key, value, message in (('path', '0', 'selected address'),
                                     ('nodes', 9, 'fixture output'),
                                     ('after_sha256', '0' * 64, 'fixture output')):
            corrupt = {'initial_prefix': fixture['initial_prefix'],
                       'steps': [dict(fixture['steps'][0], **{key: value})]}
            with self.subTest(key=key), patch.object(runner, 'encode', return_value=term), \
                 self.assertRaisesRegex(AssertionError, message):
                self.replay(table, corrupt, archived)
        with patch.object(runner, 'encode', return_value=term):
            with self.assertRaisesRegex(AssertionError, 'archived selection'):
                self.replay(table, fixture, [dict(archived[0], selection_microticks=2)])
            with self.assertRaisesRegex(AssertionError, 'initial term'):
                self.replay(table, dict(fixture, initial_prefix='S'), archived)
            with self.assertRaisesRegex(runner.ExperimentLimit, 'initial tree'):
                self.replay(table, fixture, archived, max_nodes=6)

    def test_deterministic_cli_omits_only_elapsed_durations_and_writes_same_bytes(self):
        result = {'compile_seconds': 1.25, 'elapsed_seconds': 2.5, 'finite_control_states': 7,
                  'external_bounds': {'soft_wall_seconds': 120, 'soft_compile_seconds': 10},
                  'external_process_envelope': {'hard_timeout_seconds': 180}}
        expected = {key: value for key, value in result.items()
                    if key not in ('compile_seconds', 'elapsed_seconds')}
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / 'result.json'
            stream = io.StringIO()
            with patch('sys.argv', ['report', '--deterministic', '--output', str(target)]), \
                 patch.object(runner, 'report', return_value=dict(result)), contextlib.redirect_stdout(stream):
                runner.main()
            self.assertEqual(json.loads(stream.getvalue()), expected)
            self.assertEqual(target.read_text(), stream.getvalue())
        stream = io.StringIO()
        with patch('sys.argv', ['report']), patch.object(runner, 'report', return_value=dict(result)), \
             contextlib.redirect_stdout(stream):
            runner.main()
        self.assertEqual(json.loads(stream.getvalue()), result)

    def test_failed_cli_does_not_write_success_artifact(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / 'result.json'
            with patch('sys.argv', ['report', '--output', str(target)]), \
                 patch.object(runner, 'report', side_effect=runner.ExperimentLimit('cap')), \
                 contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                runner.main()
            self.assertFalse(target.exists())


if __name__ == '__main__':
    unittest.main()
