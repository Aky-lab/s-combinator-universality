"""Bounded-driver checks plus independently specified marker/checkpoint timings."""
import contextlib
import io
import json
import math
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import Mock, patch

from s_only.cts import Program
from s_only.marker_observer import ObserverTable
from s_only.probes import Configuration, Cursor
from s_only.root_selector import SelectorTable
from s_only.selector_parts.graph import Command
from s_only.terms import App, S, nodes, prefix
from tools import marker_observer_report as runner


ROOT = Path(__file__).resolve().parents[1]


def row(command, target=None):
    return (Command(command, target),) * 6


def negative_observer():
    return ObserverTable((row('false'),), 0)


def root_selector():
    return SelectorTable((row('Rdx', 1), row('contracted')), 0)


def redex(z=S):
    return App(App(App(S, S), S), z)


class MarkerReportTests(unittest.TestCase):
    def test_invalid_bounds_precede_any_compilation(self):
        cases = [{name: value}
                 for name in ('max_states', 'max_steps', 'max_ticks', 'max_nodes')
                 for value in (0, -1, True, 0.5, None, '1')]
        cases += [{'max_seconds': value}
                  for value in (0, -1, True, math.inf, -math.inf, math.nan, None, '1')]
        with patch.object(runner, 'observer_table', side_effect=AssertionError('observer compiled')), \
             patch.object(runner, 'selector_table', side_effect=AssertionError('selector compiled')):
            for arguments in cases:
                with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                    runner.report(**arguments)

    def test_observer_tick_limit_is_inclusive_and_exact(self):
        table = ObserverTable((row('stay', 1), row('stay', 2), row('true')), 0)
        terminal, ticks = runner._observe(table, S, 2, time.monotonic() + 5)
        self.assertEqual(ticks, 2)
        self.assertTrue(table.answer(terminal.control))
        with patch.object(runner, 'observer_step', wraps=runner.observer_step) as step:
            with self.assertRaisesRegex(runner.ExperimentLimit, 'observer microtick'):
                runner._observe(table, S, 1, time.monotonic() + 5)
            self.assertEqual(step.call_count, 1)
        loop = ObserverTable((row('stay', 0),), 0)
        with patch.object(runner, 'observer_step', wraps=runner.observer_step) as step:
            with self.assertRaisesRegex(runner.ExperimentLimit, 'observer microtick'):
                runner._observe(loop, S, 7, time.monotonic() + 5)
            self.assertEqual(step.call_count, 7)

    def test_selection_tick_limit_stops_before_the_contraction(self):
        table = SelectorTable((row('stay', 1), row('stay', 2), row('Rdx', 3),
                               row('contracted')), 0)
        with patch.object(runner, 'step', wraps=runner.step) as step:
            selected, ticks = runner._select(table, redex(), 2, time.monotonic() + 5)
            self.assertEqual(ticks, 2)
            self.assertEqual(table.status(selected.control), 'Rdx')
            self.assertEqual(step.call_count, 2)
        with patch.object(runner, 'step', wraps=runner.step) as step:
            with self.assertRaisesRegex(runner.ExperimentLimit, 'selection microtick'):
                runner._select(table, redex(), 1, time.monotonic() + 5)
            self.assertEqual(step.call_count, 1)

    def test_both_boolean_terminals_absorb_without_mutation_or_ticks(self):
        term = App(S, App(S, S))
        before = prefix(term)
        for value in ('false', 'true'):
            table = ObserverTable((row(value),), 0)
            terminal, ticks = runner._observe(table, term, 1, time.monotonic() + 5)
            self.assertEqual(ticks, 0)
            self.assertIs(terminal.cursor.root, term)
            self.assertEqual(prefix(term), before)
            self.assertIs(runner.observer_step(table, terminal), terminal)
            runner._unchanged(term, terminal, before)

    def test_false_terminal_cannot_hide_a_replaced_focus(self):
        term = App(S, S)
        replaced = Configuration(0, Cursor.at(S))
        with self.assertRaisesRegex(AssertionError, 'changed its ambient tree'):
            runner._unchanged(term, replaced, prefix(term))

    def test_nonabsorbing_observer_terminal_is_rejected(self):
        with patch.object(runner, 'observer_step',
                          side_effect=lambda _, state: Configuration(state.control, state.cursor)):
            with self.assertRaisesRegex(AssertionError, 'absorbing'):
                runner._observe(negative_observer(), S, 1, time.monotonic() + 5)

    def test_soft_deadline_stops_before_runtime(self):
        with patch.object(runner, 'observer_step', side_effect=AssertionError('ran')):
            with self.assertRaisesRegex(runner.ExperimentLimit, 'wall-clock'):
                runner._observe(negative_observer(), S, 1, time.monotonic() - 1)
        with patch.object(runner, 'step', side_effect=AssertionError('ran')):
            with self.assertRaisesRegex(runner.ExperimentLimit, 'wall-clock'):
                runner._select(root_selector(), redex(), 1, time.monotonic() - 1)

    def test_initial_node_limit_precedes_observation(self):
        with patch.object(runner, 'encode', return_value=redex()), \
             patch.object(runner, 'observer_step', side_effect=AssertionError('observed')):
            with self.assertRaisesRegex(runner.ExperimentLimit, 'expanded-node'):
                runner.run_one(Program(runner.APPENDANTS), negative_observer(), root_selector(),
                               Mock(decode=lambda _: None), '', max_steps=1, max_ticks=1,
                               max_nodes=1, deadline=time.monotonic() + 5)

    def test_precontraction_growth_limit_precedes_any_native_tick(self):
        term = redex(redex())
        with patch.object(runner, 'encode', return_value=term), \
             patch.object(runner, 'step', side_effect=AssertionError('contracted')):
            with self.assertRaisesRegex(runner.ExperimentLimit, 'next contraction'):
                runner.run_one(Program(runner.APPENDANTS), negative_observer(), root_selector(),
                               Mock(decode=lambda _: None), '', max_steps=1, max_ticks=1,
                               max_nodes=nodes(term), deadline=time.monotonic() + 5)

    def test_exactly_one_contraction_and_two_fresh_samples(self):
        term = redex(redex())
        with patch.object(runner, 'encode', return_value=term), \
             patch.object(runner, 'erase', wraps=runner.erase) as erase, \
             patch.object(runner, 'step', wraps=runner.step) as step:
            run = runner.run_one(Program(runner.APPENDANTS), negative_observer(), root_selector(),
                                 Mock(decode=lambda _: None), '', max_steps=1, max_ticks=1,
                                 max_nodes=nodes(term) + nodes(term.right) - 1,
                                 deadline=time.monotonic() + 5)
        self.assertEqual(erase.call_count, 1)
        self.assertEqual(step.call_count, 2)  # One Rdx; one absorbing-terminal audit.
        self.assertEqual(run['native_contractions'], 1)
        self.assertEqual(run['exact_one_contraction_checks'], 1)
        self.assertEqual(run['samples_checked'], 2)
        self.assertEqual(run['exact_read_only_sample_checks'], 2)
        self.assertEqual(run['observer_absorbing_terminal_checks'], 2)
        self.assertEqual(run['observer_microticks'], 0)
        self.assertEqual(run['native_primitive_microticks'], 1)
        self.assertEqual([sample['observer_cursor_path'] for sample in run['samples']], ['', ''])
        self.assertEqual(run['peak_expanded_nodes'], nodes(term) + nodes(term.right) - 1)

    def test_same_size_wrong_native_result_fails_exact_rewrite_audit(self):
        term = redex()
        table = root_selector()
        selected = Configuration(0, Cursor.at(term))
        # An incorrect primitive that merely changes control can preserve size.
        def no_rewrite(_table, state):
            return Configuration(1, state.cursor) if state.control == 0 else state
        with patch.object(runner, 'step', side_effect=no_rewrite):
            with self.assertRaisesRegex(AssertionError, 'exactly one reference'):
                runner._contract(table, selected, term, max_nodes=nodes(term))

    def test_compiles_each_finite_graph_once_before_all_inputs(self):
        with patch.object(runner, 'observer_table', return_value=negative_observer()) as observer, \
             patch.object(runner, 'selector_table', return_value=root_selector()) as selector, \
             patch.object(runner, 'compile_reader', return_value=Mock(decode=lambda _: None)), \
             patch.object(runner, 'encode', return_value=redex()):
            result = runner.report(max_steps=1)
        observer.assert_called_once()
        selector.assert_called_once()
        self.assertEqual(observer.call_args.args, (Program(runner.APPENDANTS),))
        self.assertEqual(selector.call_args.args, (Program(runner.APPENDANTS),))
        self.assertEqual(result['samples_checked'], 8)
        self.assertEqual(result['native_contractions_checked'], 4)

    def test_literal_marker_shape_treats_payload_as_opaque(self):
        halt = App(App(S, S), App(App(S, S), S))
        for payload in (S, App(S, S), redex()):
            self.assertIs(runner._marker_payload(App(halt, payload)), payload)
        for other in (S, halt, App(S, halt), redex(), App(App(S, S), halt)):
            self.assertIsNone(runner._marker_payload(other))

    def test_deterministic_cli_writes_identical_stdout_and_file(self):
        result = {'elapsed_seconds': 4.5, 'run_count': 4}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'report.json'
            output = io.StringIO()
            with patch('sys.argv', ['report', '--deterministic', '--output', str(path)]), \
                 patch.object(runner, 'report', return_value=result), contextlib.redirect_stdout(output):
                runner.main()
            self.assertEqual(output.getvalue(), path.read_text())
            self.assertEqual(output.getvalue(), '{\n  "run_count": 4\n}\n')

    def test_recorded_timings_and_sample_contraction_invariants(self):
        report = json.loads((ROOT / 'results/marker_observer.json').read_text())
        self.assertNotIn('elapsed_seconds', report)
        self.assertEqual(report['appendants'], ['1', ''])
        self.assertEqual(report['graphs']['observer']['finite_control_states'], 257308)
        self.assertFalse(report['graphs']['observer']['euler_fallback'])
        self.assertTrue(report['graphs']['native_selector']['euler_fallback'])
        self.assertEqual(report['samples_checked'], 404)
        self.assertEqual(report['native_contractions_checked'], 400)
        self.assertEqual(report['true_samples'], 12)
        expected = {'': ([19, 41, 50, 69, 78], [0, 20, 79]),
                    '0': ([20, 43, 52, 72, 81], [0, 21, 82]),
                    '1': ([55, 86], [0, 22, 87]),
                    '101': ([], [0, 22, 85])}
        for run in report['runs']:
            with self.subTest(seed=run['seed']):
                markers, checkpoints = expected[run['seed']]
                self.assertEqual(run['true_samples'], markers)
                self.assertEqual([item['sample'] for item in run['checkpoints']], checkpoints)
                self.assertEqual([item['sample'] for item in run['samples']], list(range(101)))
                self.assertEqual([item['sample'] for item in run['native_selections']], list(range(100)))
                self.assertEqual([item['sample'] for item in run['samples'] if item['answer']], markers)
                self.assertEqual(run['false_samples'], 101 - len(markers))
                self.assertEqual(run['exact_read_only_sample_checks'], 101)
                self.assertEqual(run['observer_absorbing_terminal_checks'], 101)
                self.assertEqual(run['exact_one_contraction_checks'], 100)
                self.assertEqual(run['native_absorbing_terminal_checks'], 100)
                self.assertEqual(run['observer_microticks'],
                                 sum(item['observer_microticks'] for item in run['samples']))
                self.assertEqual(run['selection_microticks'],
                                 sum(item['selection_microticks'] for item in run['native_selections']))
                for checkpoint in run['checkpoints']:
                    self.assertRegex(checkpoint['prefix_sha256'], r'^[0-9a-f]{64}$')
                for marker in run['markers']:
                    n = marker['sample']
                    self.assertTrue(marker['native_selection_agrees'])
                    self.assertTrue(marker['contracted_in_this_run'])
                    self.assertEqual(marker['selected_cursor_path'], run['samples'][n]['observer_cursor_path'])
                    self.assertEqual(marker['selected_cursor_path'],
                                     run['native_selections'][n]['selected_cursor_path'])
                    self.assertEqual(marker['after_shape'], 'S payload (HALT_TAG payload)')
        original = next(run for run in report['runs'] if run['seed'] == '101')
        self.assertEqual(len(original['samples'][:86]), 86)
        self.assertFalse(any(sample['answer'] for sample in original['samples'][:86]))
        one = next(run for run in report['runs'] if run['seed'] == '1')
        first_empty_checkpoint = next(c['sample'] for c in one['checkpoints'] if not c['data'])
        self.assertEqual(first_empty_checkpoint, 87)
        self.assertLess(one['true_samples'][0], first_empty_checkpoint)


if __name__ == '__main__':
    unittest.main()
