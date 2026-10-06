"""Independent bounded checks of the fixed root-reset native controller."""
import hashlib
import json
from pathlib import Path
import time
import unittest
from functools import lru_cache

from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.queue_fixture import encode
from s_only.reduction import at, contract_at, root_arguments, select_path as preorder
from s_only.root_selector import (
    SelectorTable, _euler, erase, select_path, selector_table, step,
)
from s_only.selector_parts.graph import GraphBuilder
from s_only.terms import App, S, nodes, prefix

ROOT = Path(__file__).resolve().parents[1]


@lru_cache(maxsize=None)
def small_terms(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for cut in range(1, leaves)
                 for left in small_terms(cut) for right in small_terms(leaves - cut))


def bounded(table, term, max_ticks=2_000_000, seconds=20, contract=False):
    """Testing harness only: counters/time/source checks are not finite control."""
    state = Configuration(table.start, Cursor.at(term))
    deadline = time.monotonic() + seconds
    bound = min(max_ticks, table.linear_coefficient * (nodes(term) + 1))
    ticks, mutations = 0, 0
    while table.status(state.control) not in ('normal', 'contracted'):
        if table.status(state.control) == 'Rdx':
            if not contract:
                break
            mutations += 1
        if ticks >= bound:
            raise AssertionError(f'external microtick bound exceeded: {bound}')
        if ticks % 1024 == 0 and time.monotonic() > deadline:
            raise AssertionError(f'external runtime exceeded: {seconds}s')
        state = step(table, state)
        ticks += 1
    return state, ticks, mutations


def fallback_table():
    builder = GraphBuilder()
    normal = builder.uniform('normal')
    contracted = builder.uniform('contracted')
    selected = builder.uniform('Rdx', contracted)
    start = builder.root(_euler(builder, selected, normal))
    return SelectorTable(builder.finish(), start)


class RootSelectorTests(unittest.TestCase):
    def test_euler_matches_independent_preorder_on_small_terms(self):
        table = fallback_table()
        for size in range(1, 9):
            for term in small_terms(size):
                state, _, mutations = bounded(table, term)
                actual = state.cursor.path if table.status(state.control) == 'Rdx' else None
                self.assertEqual(actual, preorder(term))
                self.assertEqual(mutations, 0)

    def test_all_85_selections_and_result_digests_from_fresh_roots(self):
        table = selector_table()
        data = json.loads((ROOT / 'fixtures/queue_101_path.json').read_text())
        term = encode()
        self.assertEqual(prefix(term), data['initial_prefix'])
        for index, record in enumerate(data['steps'], 1):
            state, _, mutations = bounded(table, term, contract=False)
            with self.subTest(contraction=index):
                self.assertEqual(table.status(state.control), 'Rdx')
                self.assertEqual(state.cursor.path, tuple(map(int, record['path'])))
                self.assertIs(state.cursor.root, term)
                self.assertEqual(mutations, 0)
                contracted = step(table, state)
                self.assertEqual(table.status(contracted.control), 'contracted')
                self.assertIs(step(table, contracted), contracted)
                term = erase(contracted.cursor)
                self.assertEqual(nodes(term), record['nodes'])
                self.assertEqual(hashlib.sha256(prefix(term).encode('ascii')).hexdigest(),
                                 record['after_sha256'])
        self.assertEqual(index, 85)

    def test_all_small_malformed_trees_progress_or_certify_normality(self):
        table = selector_table()
        checked = 0
        for size in range(1, 9):
            for term in small_terms(size):
                expected = preorder(term)
                state, _, mutations = bounded(table, term, contract=True)
                status = table.status(state.control)
                with self.subTest(leaves=size, case=checked):
                    self.assertEqual(status == 'normal', expected is None)
                    self.assertEqual(mutations, int(expected is not None))
                    if expected is not None:
                        self.assertIsNotNone(root_arguments(at(term, state.cursor.path)))
                        self.assertEqual(prefix(erase(state.cursor)),
                                         prefix(contract_at(term, state.cursor.path)))
                    else:
                        self.assertEqual(prefix(erase(state.cursor)), prefix(term))
                    self.assertIs(step(table, state), state)
                checked += 1
        self.assertEqual(checked, 626)

    def test_tiny_empty_and_nonempty_initial_terms(self):
        table = selector_table()
        for word in ((), (0,), (1,), (0, 0), (0, 1), (1, 0), (1, 1)):
            term = encode(word)
            # Initial CLOCK microprogram is independent of the input payload.
            for expected in ((0,), (0,), (0, 1), ()):
                state, _, _ = bounded(table, term)
                self.assertEqual(state.cursor.path, expected, (word, expected))
                term = erase(step(table, state).cursor)
            # Continue without a saved schedule to exercise EMPTY/ordinary forks.
            for _ in range(24):
                state, _, mutations = bounded(table, term, contract=True)
                self.assertEqual(table.status(state.control), 'contracted')
                self.assertEqual(mutations, 1)
                term = erase(state.cursor)

    def test_pattern_shaped_malformed_trees_with_unrelated_holes(self):
        from itertools import cycle
        from s_only.selector_parts import patterns as p
        from s_only.fuel_probe import fuel_rows
        from s_only.selector_parts.clock import HEAD_PATTERN

        def instantiate(pattern, values):
            if pattern == p.H:
                return next(values)
            if pattern == p.S:
                return S
            return App(instantiate(pattern[0], values), instantiate(pattern[1], values))

        families = ((p.base_pattern(), p.pending_pattern(), HEAD_PATTERN)
                    + p.local_patterns('fresh') + p.local_patterns('marked')
                    + tuple(pattern for pattern, _ in p.frame_head_rows())
                    + tuple(pattern for _, pattern, _ in fuel_rows())
                    + tuple(pattern for pattern, _ in p.selected_action_rows()))
        table = selector_table()
        hole_values = (S, App(S, S), App(App(App(S, S), S), S))
        cases = 0
        for pattern in families:
            for offset in range(len(hole_values)):
                values = cycle(hole_values[offset:] + hole_values[:offset])
                candidate = instantiate(pattern, values)
                for term in (candidate, App(S, candidate), App(candidate, S)):
                    expected = preorder(term)
                    state, _, mutations = bounded(table, term, contract=True)
                    self.assertEqual(table.status(state.control) == 'normal', expected is None)
                    self.assertEqual(mutations, int(expected is not None))
                    if expected is not None:
                        self.assertIsNotNone(root_arguments(at(term, state.cursor.path)))
                    cases += 1
        self.assertEqual(cases, 198)

    def test_table_is_fixed_and_has_only_local_observations(self):
        table = selector_table()
        self.assertIs(table, selector_table())
        for control, row in enumerate(table.states):
            self.assertIsInstance(row, tuple)
            self.assertEqual(len(row), 6)
            for observation, entry in zip(OBSERVATIONS, row):
                self.assertIs(table.transition(control, *observation), entry)
                self.assertIn(entry.command, ('stay', 'L', 'R', 'U', 'Rdx', 'normal', 'contracted'))
        # No runtime term/source/pattern field is retained in the table.
        self.assertEqual(tuple(SelectorTable.__dataclass_fields__), ('states', 'start'))
        self.assertEqual(tuple(Configuration.__dataclass_fields__), ('control', 'cursor'))


if __name__ == '__main__':
    unittest.main()
