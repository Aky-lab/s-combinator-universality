"""Adversarial independent review of the exact finite-control quotient.

These checks avoid large compiled tables: a cyclic family has a proved
closed-form equivalence relation, and deliberately unsafe hand-written tables
exercise the actual interpreter's failure and divergence boundaries.
"""
from contextlib import redirect_stderr, redirect_stdout
from hashlib import sha256
import io
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from s_only.control_minimization import (
    MinimizationResult, _main, graph_digest, minimize, quotient_report,
    verify_quotient,
)
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.root_selector import SelectorTable, erase, step
from s_only.selector_parts.graph import Command
from s_only.terms import App, S, prefix


def uniform(command, target=None):
    return (Command(command, target),) * 6


def all_cursors(term):
    pending = [Cursor.at(term)]
    while pending:
        cursor = pending.pop()
        yield cursor
        if cursor.kind == 'application':
            pending.extend((cursor.move('L'), cursor.move('R')))


class AdversarialQuotientReviewTests(unittest.TestCase):
    def test_uneven_cyclic_clones_have_exact_canonical_classes(self):
        # Phase 0 emits L only for observation 0; other phases emit stay.
        # Repeating observation 0 distinguishes every pair of phases within
        # period ticks, independently of the minimizer or any oracle code.
        # Each phase has an unequal number of cross-wired copies. Shuffling
        # old ids destroys adjacency and makes canonical numbering nontrivial.
        rng = random.Random(320918)
        period = 257
        labels = [(phase, copy) for phase in range(period)
                  for copy in range(1 + phase % 11)]
        rng.shuffle(labels)
        ids = {label: state for state, label in enumerate(labels)}
        rows = []
        strides = (1, 3, 17, 0, 128, 256)
        for phase, copy in labels:
            row = []
            for observation, stride in enumerate(strides):
                next_phase = (phase + stride) % period
                next_copy = (copy + 3 * observation + phase) % (1 + next_phase % 11)
                command = 'L' if phase == 0 and observation == 0 else 'stay'
                row.append(Command(command, ids[next_phase, next_copy]))
            rows.append(tuple(row))
        table = SelectorTable(tuple(rows), ids[193, 1])
        result = minimize(table)
        verify_quotient(table, result)
        canonical = {}
        expected = []
        for phase, _ in labels:
            canonical.setdefault(phase, len(canonical))
            expected.append(canonical[phase])
        self.assertEqual(len(result.table.states), period)
        self.assertEqual(result.state_map, tuple(expected))
        self.assertEqual(result.table.start, canonical[193])
        self.assertEqual(minimize(result.table).state_map, tuple(range(period)))
        self.assertEqual(minimize(table), result)

    def test_primitive_failures_contexts_terminals_and_divergence_match(self):
        table = SelectorTable((
            uniform('normal'), uniform('normal'),
            uniform('contracted'), uniform('contracted'),
            uniform('Rdx', 2), uniform('Rdx', 3),
            uniform('L', 0), uniform('L', 1),
            uniform('R', 0), uniform('R', 1),
            uniform('U', 0), uniform('U', 1),
            uniform('stay', 6), uniform('stay', 7),
            uniform('stay', 12), uniform('stay', 13),
            uniform('stay', 16), uniform('stay', 18), uniform('stay', 17),
        ), 15)
        result = minimize(table)
        verify_quotient(table, result)
        self.assertEqual(result.state_map[16], result.state_map[17])
        self.assertEqual(result.state_map[17], result.state_map[18])
        redex = App(App(App(S, S), S), S)
        cursors = [Cursor.at(S)] + list(all_cursors(App(redex, redex)))
        self.assertEqual({(c.kind, c.incoming) for c in cursors}, set(OBSERVATIONS))
        seen_failures = set()
        for old_state in range(len(table.states)):
            for cursor in cursors:
                with self.subTest(state=old_state, path=cursor.path):
                    old = Configuration(old_state, cursor)
                    new = Configuration(result.state_map[old_state], cursor)
                    for tick in range(9):
                        self.assertEqual(result.state_map[old.control], new.control)
                        self.assertEqual(old.cursor, new.cursor)
                        self.assertEqual(prefix(erase(old.cursor)), prefix(erase(new.cursor)))
                        command = table.transition(old.control, old.cursor.kind,
                                                   old.cursor.incoming).command
                        self.assertEqual(command, result.table.transition(
                            new.control, new.cursor.kind, new.cursor.incoming).command)
                        self.assertEqual(table.status(old.control), result.table.status(new.control))
                        outcomes = []
                        for machine, configuration in ((table, old), (result.table, new)):
                            try:
                                following = step(machine, configuration)
                            except ValueError as error:
                                outcomes.append(('error', type(error), str(error)))
                            else:
                                if machine.status(configuration.control) in ('normal', 'contracted'):
                                    self.assertIs(following, configuration)
                                outcomes.append(following)
                        if isinstance(outcomes[0], tuple):
                            self.assertEqual(outcomes[0], outcomes[1])
                            seen_failures.add(command)
                            if old_state in (14, 15) and cursor.kind == 'S':
                                self.assertEqual(tick, 2, 'two stay ticks must precede illegal descent')
                            break
                        self.assertIsInstance(outcomes[1], Configuration)
                        old, new = outcomes
        self.assertEqual(seen_failures, {'L', 'R', 'U', 'Rdx'})
        # An actual root zipper is unchanged through a nonterminating cycle.
        # The bound belongs only to this external test; no execute() hang.
        old = Configuration(17, Cursor.at(S))
        new = Configuration(result.state_map[17], old.cursor)
        for _ in range(4096):
            old, new = step(table, old), step(result.table, new)
            self.assertEqual(result.state_map[old.control], new.control)
            self.assertIs(old.cursor, new.cursor)
            self.assertIsNone(result.table.status(new.control))

    def test_unreachable_sixth_edge_cannot_be_hidden_by_witness(self):
        table = SelectorTable((uniform('normal'), uniform('contracted'),
                               uniform('stay', 0), uniform('stay', 0)), 0)
        result = minimize(table)
        self.assertEqual(result.state_map, (0, 1, 2, 2))
        # Reachable execution is already terminal, but changing an unreachable
        # state's last observation must still invalidate the full certificate.
        altered = result.table.states[:-1] + (
            result.table.states[-1][:-1] + (Command('stay', 1),),)
        with self.assertRaisesRegex(ValueError, 'successor'):
            verify_quotient(table, MinimizationResult(SelectorTable(altered, 0), result.state_map))
        unmapped = SelectorTable(result.table.states + (uniform('normal'),), 0)
        with self.assertRaisesRegex(ValueError, 'unmapped'):
            verify_quotient(table, MinimizationResult(unmapped, result.state_map))
        with self.assertRaisesRegex(ValueError, 'immutable'):
            verify_quotient(table, MinimizationResult(result.table, list(result.state_map)))
        # A faithful nonminimal certificate is valid: this validator deliberately
        # proves trace preservation, not minimality, and should accept identity.
        verify_quotient(table, MinimizationResult(table, tuple(range(4))))
        self.assertLess(len(result.table.states), len(table.states))

    def test_digest_encoding_covers_all_outputs_and_nonuniform_edges(self):
        table = SelectorTable((uniform('normal'), uniform('contracted'),
                               uniform('Rdx', 1), uniform('stay', 3),
                               uniform('L', 3), uniform('R', 4), uniform('U', 5),
                               tuple(Command(command, target) for command, target in
                                     zip(('stay', 'L', 'R', 'U', 'stay', 'L'),
                                         (0, 1, 2, 7, 3, 6)))), 7)
        # Independent byte assembly deliberately avoids struct and graph_digest.
        codes = {'normal': 0, 'contracted': 1, 'stay': 2, 'L': 3, 'R': 4, 'U': 5, 'Rdx': 6}
        payload = bytearray(b'selector-table-v1\x00')
        payload.extend(len(table.states).to_bytes(8, 'big'))
        payload.extend(table.start.to_bytes(8, 'big'))
        for row in table.states:
            for entry in row:
                payload.append(codes[entry.command])
                target = 2 ** 64 - 1 if entry.next_state is None else entry.next_state
                payload.extend(target.to_bytes(8, 'big'))
        self.assertEqual(graph_digest(table), sha256(payload).hexdigest())
        # Commands and their positions are significant, even on impossible
        # observation sequences or unsafe hand-written controller entries.
        rows = list(table.states)
        rows[-1] = rows[-1][1:] + rows[-1][:1]
        self.assertNotEqual(graph_digest(table), graph_digest(SelectorTable(tuple(rows), 7)))

    def test_cli_rejects_nonpositive_caps_before_either_compiler(self):
        for cap in ('0', '-1'):
            for program in ((), ('--program', '0', '10')):
                with self.subTest(cap=cap, program=program):
                    with patch('sys.argv', ['control-minimization', '--max-states', cap, *program]), \
                         patch('s_only.root_selector.selector_table') as legacy, \
                         patch('s_only.program_selector.selector_table') as generic, \
                         redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                        _main()
                    self.assertEqual(raised.exception.code, 2)
                    legacy.assert_not_called()
                    generic.assert_not_called()

    def test_cli_stdout_and_file_are_identical_deterministic_json(self):
        table = SelectorTable((uniform('normal'), uniform('normal'), uniform('stay', 0)), 2)
        with patch('s_only.root_selector.selector_table', return_value=table), \
             patch('sys.argv', ['control-minimization', '--max-states', '3']), \
             redirect_stdout(io.StringIO()) as captured:
            _main()
        expected = quotient_report(table)
        expected.update(compiler='root_selector', appendants=None)
        self.assertEqual(json.loads(captured.getvalue()), expected)
        self.assertEqual(captured.getvalue(), json.dumps(expected, indent=2, sort_keys=True) + '\n')
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / 'report.json'
            with patch('s_only.root_selector.selector_table', return_value=table), \
                 patch('sys.argv', ['control-minimization', '--max-states', '3', '--output', str(target)]), \
                 redirect_stdout(io.StringIO()) as quiet:
                _main()
            self.assertEqual(quiet.getvalue(), '')
            self.assertEqual(target.read_text(encoding='utf-8'), captured.getvalue())

    def test_report_is_independent_of_python_hash_seed(self):
        script = '''
import json
from s_only.control_minimization import quotient_report
from s_only.root_selector import SelectorTable
from s_only.selector_parts.graph import Command
rows = tuple((Command(name, target),) * 6 for name, target in (
    ('normal', None), ('contracted', None), ('stay', 3),
    ('stay', 2), ('Rdx', 1), ('stay', 0), ('stay', 0)))
print(json.dumps(quotient_report(SelectorTable(rows, 6)), sort_keys=True))
'''
        outputs = []
        root = str(Path(__file__).resolve().parents[1])
        for seed in ('0', '1', '938'):
            completed = subprocess.run([sys.executable, '-c', script], cwd=root,
                                       env={**os.environ, 'PYTHONHASHSEED': seed},
                                       capture_output=True, text=True, timeout=10, check=True)
            self.assertEqual(completed.stderr, '')
            outputs.append(completed.stdout)
        self.assertEqual(outputs, [outputs[0]] * len(outputs))


if __name__ == '__main__':
    unittest.main()
