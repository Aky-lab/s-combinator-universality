"""Independent model-fidelity regressions for the fixed root-reset table.

The oracles, counters, saved samples, file access and hashes in this module
belong to the reviewer, never to the selection machine.  Finite test sets do
not establish all-input termination or generic CTS universality.
"""
from contextlib import ExitStack
from functools import lru_cache
from itertools import cycle
from pathlib import Path
import builtins
import hashlib
import io
import json
import os
import random
import unittest
from unittest.mock import patch

from s_only import cts, encoding, fuel_probe, probes, queue_fixture, reduction
from s_only import root_selector as selector
from s_only import terms, walkers
from s_only.probes import Configuration, Cursor
from s_only.selector_parts import active, clock, graph, patterns, priority
from s_only.terms import App, S


ROOT = Path(__file__).resolve().parents[1]


def arguments(term):
    """Independent bounded root-shape oracle; never call reducer helpers."""
    if (isinstance(term, App) and isinstance(term.left, App)
            and isinstance(term.left.left, App) and term.left.left.left is S):
        return term.left.left.right, term.left.right, term.right
    return None


def first_redex(term):
    pending = [(term, ())]
    while pending:
        term, address = pending.pop()
        if arguments(term) is not None:
            return address
        if isinstance(term, App):
            pending.extend(((term.right, address + (1,)),
                            (term.left, address + (0,))))
    return None


def contract(term, address):
    """Independent occurrence replacement, used only as an output oracle."""
    frames = []
    for side in address:
        frames.append((term, side))
        term = term.left if side == 0 else term.right
    x, y, z = arguments(term)
    result = App(App(x, z), App(y, z))
    for parent, side in reversed(frames):
        result = App(result, parent.right) if side == 0 else App(parent.left, result)
    return result


@lru_cache(maxsize=None)
def trees(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for cut in range(1, leaves)
                 for left in trees(cut) for right in trees(leaves - cut))


def bounded(table, term, max_ticks=500_000):
    """The fixed reviewer cap must never determine a selected occurrence."""
    state = Configuration(table.start, Cursor.at(term))
    for _ in range(max_ticks):
        if table.status(state.control) in ('normal', 'Rdx'):
            return state
        state = selector.step(table, state)
    raise AssertionError('external review microtick allowance exceeded')


def denied(*args, **kwargs):
    raise AssertionError('selector consulted a forbidden auxiliary operation')


def instantiate(pattern, holes):
    if pattern == patterns.S:
        return S
    if pattern == patterns.H:
        return next(holes)
    return App(instantiate(pattern[0], holes), instantiate(pattern[1], holes))


def replace(term, address, replacement):
    if not address:
        return replacement
    if address[0] == 0:
        return App(replace(term.left, address[1:], replacement), term.right)
    return App(term.left, replace(term.right, address[1:], replacement))


class RootSelectorIndependentReviewTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Input-free compilation precedes creation of every reviewed term.
        cls.table = selector.selector_table()

    def assert_sound_selection(self, term):
        state = bounded(self.table, term)
        normal = first_redex(term) is None
        self.assertEqual(self.table.status(state.control) == 'normal', normal)
        if not normal:
            self.assertIsNotNone(arguments(state.cursor.focus))
            result = selector.step(self.table, state)
            self.assertEqual(self.table.status(result.control), 'contracted')
            self.assertIs(selector.step(self.table, result), result)
            expected = contract(term, state.cursor.path)
            self.assertEqual(terms.prefix(selector.erase(result.cursor)), terms.prefix(expected))
        else:
            self.assertIs(selector.step(self.table, state), state)
            self.assertIs(state.cursor.root, term)

    def test_85_reverse_order_samples_with_auxiliary_runtime_access_disabled(self):
        data = json.loads((ROOT / 'fixtures/queue_101_path.json').read_text())
        term = queue_fixture.encode()
        samples = []
        for record in data['steps']:
            address = tuple(map(int, record['path']))
            samples.append((term, address, record['after_sha256']))
            term = contract(term, address)
        states_before = self.table.states
        # Reverse invocation order rules out dependence on prior fixture steps.
        # Open/hash/decoder/compiler failures also rule out hidden lookup aids.
        with ExitStack() as stack:
            for module in (queue_fixture, cts, encoding, fuel_probe,
                           patterns, active, priority, clock):
                for name, value in tuple(vars(module).items()):
                    if callable(value) and getattr(value, '__module__', None) == module.__name__:
                        stack.enter_context(patch.object(module, name, denied))
            forbidden = (
                (reduction, ('select_path', 'redex_paths', 'reduce', 'at', 'contract_at')),
                (probes, ('compile_pattern', 'compile_rows', 'execute')),
                (walkers, ('compile_inverse_rows', 'compile_descent', 'compile_ascent', 'execute')),
                (terms, ('nodes', 'prefix', 'format_term', 'parse')),
                (hashlib, ('sha256', 'sha1', 'md5', 'new')),
                (builtins, ('open',)), (io, ('open',)), (os, ('open',)),
            )
            for module, names in forbidden:
                for name in names:
                    stack.enter_context(patch.object(module, name, denied))
            stack.enter_context(patch.object(graph.GraphBuilder, '__init__', denied))
            stack.enter_context(patch.object(App, '__eq__', denied))
            stack.enter_context(patch.object(App, '__hash__', denied))
            stack.enter_context(patch.object(Cursor, 'root', property(denied)))
            stack.enter_context(patch.object(Cursor, 'path', property(denied)))
            stack.enter_context(patch.object(selector.SelectorTable, 'linear_coefficient', property(denied)))
            results = [selector.execute(source) for source, _, _ in reversed(samples)]
            normal = selector.execute(S)
            repeated = selector.execute(samples[0][0])
        self.assertEqual(len(results), 85)
        self.assertEqual(self.table.status(normal.control), 'normal')
        self.assertEqual(repeated.cursor.path, samples[0][1])
        self.assertIs(self.table.states, states_before)
        for actual, (source, address, digest) in zip(results, reversed(samples)):
            with self.subTest(address=address, digest=digest):
                self.assertEqual(self.table.status(actual.control), 'contracted')
                self.assertEqual(actual.cursor.path, address)
                output = terms.prefix(selector.erase(actual.cursor))
                self.assertEqual(hashlib.sha256(output.encode('ascii')).hexdigest(), digest)
                self.assertEqual(output, terms.prefix(contract(source, address)))

    def test_all_6918_closed_trees_through_ten_leaves(self):
        count = 0
        for leaves in range(1, 11):
            for term in trees(leaves):
                self.assert_sound_selection(term)
                count += 1
        self.assertEqual(count, 6918)

    def test_500_adversarial_carriers_and_unrelated_contexts(self):
        rng = random.Random(271828)
        family = ((patterns.base_pattern(), patterns.pending_pattern())
                  + patterns.local_patterns('fresh') + patterns.local_patterns('marked')
                  + tuple(pattern for pattern, _ in patterns.frame_head_rows())
                  + tuple(pattern for _, pattern, _ in fuel_probe.fuel_rows()))
        seeds = list(trees(4)) + [instantiate(pattern, cycle((S,))) for pattern in family]
        for case in range(500):
            holes = (rng.choice(seeds) for _ in iter(int, 1))
            term = instantiate(rng.choice(family), holes)
            for _ in range(rng.randrange(5)):
                kind = rng.randrange(6)
                if kind == 0:
                    term = App(S, term)
                elif kind == 1:
                    term = App(term, S)
                elif kind == 2:
                    term = App(App(App(S, S), S), term)
                elif kind == 3:
                    term = replace(instantiate(patterns.pending_pattern(), cycle((S,))), (1,), term)
                else:
                    pattern, accumulator = rng.choice(patterns.local_rows('fresh' if kind == 4 else 'marked'))
                    outer = instantiate(pattern, cycle((S,)))
                    address = (1, 0) if rng.randrange(2) else accumulator
                    term = replace(outer, address, term)
            with self.subTest(case=case):
                self.assert_sound_selection(term)

    def test_deep_term_needs_no_recursive_runtime_stack(self):
        term = S
        for _ in range(2000):
            term = App(S, term)
        self.assert_sound_selection(term)
        # The same deep context with one reducible occurrence stays legal.
        term = App(term, App(App(App(S, S), S), S))
        self.assert_sound_selection(term)

    def test_compilation_is_fixed_after_unrelated_invocations(self):
        states = self.table.states
        for source in (S, queue_fixture.encode(()), queue_fixture.encode((1, 1, 0))):
            bounded(self.table, source)
        separately_compiled = selector.selector_table.__wrapped__()
        self.assertEqual(len(states), 257299)
        self.assertEqual(separately_compiled, self.table)
        self.assertIs(self.table.states, states)
        self.assertEqual(tuple(selector.SelectorTable.__dataclass_fields__), ('states', 'start'))
        self.assertEqual(tuple(Configuration.__dataclass_fields__), ('control', 'cursor'))
        self.assertEqual(tuple(Cursor.__dataclass_fields__), ('focus', 'parents'))
        for row in states:
            self.assertIs(type(row), tuple)
            self.assertEqual(len(row), 6)
            for entry in row:
                self.assertIs(type(entry), graph.Command)
                self.assertIn(entry.command, ('stay', 'L', 'R', 'U', 'Rdx', 'normal', 'contracted'))
                if entry.next_state is not None:
                    self.assertIs(type(entry.next_state), int)
                    self.assertTrue(0 <= entry.next_state < len(states))


if __name__ == '__main__':
    unittest.main()
