"""Independent finite-state and bounded actual-tree checks of exact quotients."""
from dataclasses import FrozenInstanceError
from functools import lru_cache
from itertools import product
import gc
import random
import time
import unittest

from s_only.control_minimization import (
    MinimizationResult, graph_digest, minimize, quotient_report, verify_quotient,
)
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.root_selector import SelectorTable, erase, selector_table, step
from s_only.selector_parts.graph import Command
from s_only.terms import App, S, prefix


def uniform(command, target=None):
    return (Command(command, target),) * 6


def distinguishability_oracle(table):
    """Slow all-pairs greatest fixed point, independent of partition code."""
    relation = {(p, q) for p, row in enumerate(table.states)
                for q, other in enumerate(table.states)
                if tuple(entry.command for entry in row) ==
                tuple(entry.command for entry in other)}
    while True:
        refined = {(p, q) for p, q in relation
                   if all(a.next_state is None or (a.next_state, b.next_state) in relation
                          for a, b in zip(table.states[p], table.states[q]))}
        if refined == relation:
            return refined
        relation = refined


def abstract_trace(table, start, observations):
    outputs = []
    for observation in observations:
        entry = table.states[start][observation]
        outputs.append(entry.command)
        if entry.next_state is not None:
            start = entry.next_state
    return tuple(outputs)


@lru_cache(maxsize=None)
def small_terms(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for cut in range(1, leaves)
                 for left in small_terms(cut) for right in small_terms(leaves - cut))


def compare_invocation(test, original, result, term, *, max_ticks=2_000_000, seconds=15):
    """Lockstep complete command trace, including Rdx and terminal absorption."""
    quotient = result.table
    old = Configuration(original.start, Cursor.at(term))
    new = Configuration(quotient.start, Cursor.at(term))
    test.assertEqual(old.cursor.path, ())
    test.assertEqual(new.cursor.path, ())
    deadline = time.monotonic() + seconds
    mutations = 0
    for ticks in range(max_ticks + 1):
        test.assertEqual(result.state_map[old.control], new.control)
        test.assertEqual((old.cursor.kind, old.cursor.incoming),
                         (new.cursor.kind, new.cursor.incoming))
        old_command = original.transition(old.control, old.cursor.kind, old.cursor.incoming)
        new_command = quotient.transition(new.control, new.cursor.kind, new.cursor.incoming)
        test.assertEqual(old_command.command, new_command.command)
        status = original.status(old.control)
        test.assertEqual(status, quotient.status(new.control))
        if status in ('normal', 'contracted'):
            test.assertEqual(mutations, int(status == 'contracted'))
            test.assertEqual(old.cursor.path, new.cursor.path)
            test.assertEqual(prefix(erase(old.cursor)), prefix(erase(new.cursor)))
            test.assertIs(step(original, old), old)
            test.assertIs(step(quotient, new), new)
            return erase(old.cursor), status
        # Until the native contraction, both cursors focus on the very same
        # immutable occurrence, not just equal node kinds or equal term sizes.
        test.assertIs(old.cursor.focus, new.cursor.focus)
        if status == 'Rdx':
            mutations += 1
        if ticks % 1024 == 0:
            test.assertLess(time.monotonic(), deadline, 'external invocation time cap')
        old, new = step(original, old), step(quotient, new)
    raise AssertionError('external invocation microtick cap')


class FiniteQuotientTests(unittest.TestCase):
    def test_all_outputs_and_terminals_remain_distinct(self):
        table = SelectorTable((uniform('normal'), uniform('contracted'), uniform('Rdx', 1),
                               uniform('stay', 0), uniform('L', 0), uniform('R', 0),
                               uniform('U', 0), uniform('normal'), uniform('contracted'),
                               uniform('Rdx', 8)), 9)
        result = minimize(table)
        verify_quotient(table, result)
        self.assertEqual(len(result.table.states), 7)
        self.assertEqual(result.state_map[:7], tuple(range(7)))
        self.assertEqual(result.state_map[7:], (0, 1, 2))
        self.assertEqual(result.table.start, 2)
        with self.assertRaises(FrozenInstanceError):
            result.state_map = ()

    def test_cycles_duplicates_unreachable_states_and_stay_ticks(self):
        # Controls 2/3 have identical infinite stay traces; 4 requires one
        # stay to normal, 5 requires two, and must not be epsilon-collapsed.
        table = SelectorTable((uniform('normal'), uniform('contracted'), uniform('stay', 3),
                               uniform('stay', 2), uniform('stay', 0), uniform('stay', 4),
                               uniform('stay', 0)), 5)
        result = minimize(table)
        verify_quotient(table, result)
        self.assertEqual(result.state_map[2], result.state_map[3])
        self.assertEqual(result.state_map[4], result.state_map[6])
        self.assertNotEqual(result.state_map[4], result.state_map[5])
        self.assertEqual(len(result.table.states), 5)
        for start in range(len(table.states)):
            for observations in product(range(6), repeat=3):
                self.assertEqual(abstract_trace(table, start, observations),
                                 abstract_trace(result.table, result.state_map[start], observations))

    def test_sixth_observation_and_delayed_difference_are_not_ignored(self):
        states = [uniform('normal'), uniform('contracted')]
        states.extend((uniform('stay', 0), (Command('stay', 0),) * 5 + (Command('stay', 1),)))
        for _ in range(12):
            states.extend((uniform('stay', len(states) - 2), uniform('stay', len(states) - 1)))
        table = SelectorTable(tuple(states), len(states) - 1)
        result = minimize(table)
        verify_quotient(table, result)
        for state in range(2, len(states), 2):
            self.assertNotEqual(result.state_map[state], result.state_map[state + 1])

    def test_generated_graphs_match_independent_greatest_fixed_point(self):
        rng = random.Random(6317009)
        for case in range(100):
            count = rng.randrange(3, 22)
            rows = [uniform('normal'), uniform('contracted'), uniform('Rdx', 1)]
            palette = [tuple(rng.choice(('stay', 'L', 'R', 'U')) for _ in OBSERVATIONS)
                       for _ in range(rng.randrange(1, 5))]
            for state in range(3, count):
                if rng.randrange(4) == 0:
                    rows.append(rows[rng.randrange(state)])
                else:
                    rows.append(tuple(Command(command, rng.randrange(count))
                                      for command in rng.choice(palette)))
            table = SelectorTable(tuple(rows), rng.randrange(count))
            result = minimize(table)
            verify_quotient(table, result)
            equivalent = distinguishability_oracle(table)
            for p in range(count):
                for q in range(count):
                    self.assertEqual(result.state_map[p] == result.state_map[q],
                                     (p, q) in equivalent, (case, p, q))
            again = minimize(result.table)
            self.assertEqual(again.table, result.table)
            self.assertEqual(again.state_map, tuple(range(len(result.table.states))))
            self.assertEqual(minimize(table), result)

    def test_equivalent_cyclic_clones_with_different_successor_ids(self):
        rng = random.Random(931)
        base = SelectorTable((uniform('normal'), uniform('contracted'), uniform('Rdx', 1),
                              tuple(Command('stay', target) for target in (0, 1, 2, 4, 5, 6)),
                              uniform('L', 3), uniform('R', 3), uniform('U', 3)), 3)
        # Three independently wired copies of every state.  Corresponding
        # successors have different ids yet recursively equivalent behavior.
        rows = []
        for state in range(len(base.states) * 3):
            source = state // 3
            row = base.states[source]
            if row[0].command == 'Rdx':
                rows.append(uniform('Rdx', 3 + rng.randrange(3)))
            else:
                rows.append(tuple(Command(entry.command, None if entry.next_state is None else
                                          3 * entry.next_state + rng.randrange(3)) for entry in row))
        table = SelectorTable(tuple(rows), 10)
        result = minimize(table)
        verify_quotient(table, result)
        self.assertEqual(len(result.table.states), len(base.states))
        for state in range(len(base.states)):
            self.assertEqual(len(set(result.state_map[state * 3:state * 3 + 3])), 1)
        oracle = distinguishability_oracle(table)
        self.assertEqual({(p, q) for p in range(len(rows)) for q in range(len(rows))
                          if result.state_map[p] == result.state_map[q]}, oracle)

    def test_long_distinguishable_chain(self):
        # A global rescan-per-depth refinement would do quadratic work here.
        table = SelectorTable((uniform('normal'),) +
                              tuple(uniform('stay', index - 1) for index in range(1, 12_000)),
                              11_999)
        result = minimize(table)
        verify_quotient(table, result)
        self.assertEqual(result.table, table)

    def test_bad_limits_and_independent_witness_rejection(self):
        table = SelectorTable((uniform('normal'), uniform('contracted'), uniform('stay', 0)), 2)
        with self.assertRaises(TypeError):
            minimize(())
        for bound in (False, 0, -1, 1.5):
            with self.assertRaises(ValueError):
                minimize(table, max_states=bound)
        with self.assertRaisesRegex(ValueError, 'exceeds'):
            minimize(table, max_states=2)
        self.assertEqual(minimize(table, max_states=3).table, table)
        for mapping in ((0, 1), (0, 1, True), (0, 1, 3), (0, 0, 0), (1, 0, 2)):
            with self.assertRaises(ValueError):
                verify_quotient(table, MinimizationResult(table, mapping))
        changed_start = SelectorTable(table.states, 0)
        with self.assertRaisesRegex(ValueError, 'initial'):
            verify_quotient(table, MinimizationResult(changed_start, (0, 1, 2)))
        changed_edge = SelectorTable((table.states[0], table.states[1], uniform('stay', 1)), 2)
        with self.assertRaisesRegex(ValueError, 'successor'):
            verify_quotient(table, MinimizationResult(changed_edge, (0, 1, 2)))

    def test_reproducible_report_and_independently_encoded_digest(self):
        from hashlib import sha256
        table = SelectorTable((uniform('normal'), uniform('normal')), 1)
        # Encoding assembled independently without graph_digest or struct.
        payload = (b'selector-table-v1\0' + (2).to_bytes(8, 'big') +
                   (1).to_bytes(8, 'big') + (b'\0' + b'\xff' * 8) * 12)
        self.assertEqual(graph_digest(table), sha256(payload).hexdigest())
        self.assertNotEqual(graph_digest(table), graph_digest(SelectorTable(table.states, 0)))
        report = quotient_report(table)
        self.assertEqual(report, quotient_report(table))
        self.assertEqual((report['original_states'], report['quotient_states'],
                          report['removed_states'], report['verified_observation_entries']),
                         (2, 1, 1, 12))
        self.assertIs(report['all_states_witness_verified'], True)
        witness = b'selector-state-map-v1\0' + (2).to_bytes(8, 'big') + b'\0' * 16
        self.assertEqual(report['state_map_sha256'], sha256(witness).hexdigest())


class CompiledSelectorQuotientTests(unittest.TestCase):
    def test_legacy_and_generic_full_microtick_traces(self):
        from s_only.cts import Program
        from s_only.encoding import encode
        from s_only.program_selector import selector_table as program_table
        # One large table at a time.  Bounds and counters are only in this
        # test driver, and never become part of the finite runtime control.
        for appendants, factory, horizon in (
                (('1', ''), selector_table, 85),
                (('0', '10'), lambda: program_table(Program(('0', '10')), max_states=1_000_000), 40)):
            original = factory()
            result = minimize(original, max_states=1_000_000)
            verify_quotient(original, result)
            self.assertLess(len(result.table.states), len(original.states))
            # Outside the encoded domain as well as on the encoded path.
            for leaves in range(1, 7):
                for term in small_terms(leaves):
                    compare_invocation(self, original, result, term)
            term = encode(Program(appendants), '101')
            for _ in range(horizon):
                term, status = compare_invocation(self, original, result, term)
                self.assertEqual(status, 'contracted')
            # Reusing the table starts from its mapped initial state at root,
            # independently of the just-completed contracted configuration.
            compare_invocation(self, original, result, S)
            selector_table.cache_clear()
            program_table.cache_clear()
            del original, result, term
            gc.collect()


if __name__ == '__main__':
    unittest.main()
