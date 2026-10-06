"""Synthetic structural checks for active-endpoint finite-table assembly.

The constructors/oracles here are test-only.  Execution observes the six
allowed local inputs; the test driver supplies an external timeout.
"""
from itertools import cycle
import unittest

from s_only import App, S
from s_only.probes import Cursor, OBSERVATIONS
from s_only.queue_fixture import apply, LIVE
from s_only.reduction import contract_at, root_arguments
from s_only.selector_parts import patterns as p
from s_only.selector_parts.active import (
    compile_base, compile_dispatcher, compile_frame, compile_frontend,
    compile_pending_base,
)
from s_only.selector_parts.graph import GraphBuilder


def instantiate(pattern, values=None):
    values = cycle((S, App(S, S), App(S, App(S, S)))) if values is None else values
    if pattern == p.H:
        return next(values)
    if pattern == p.S:
        return S
    return App(instantiate(pattern[0], values), instantiate(pattern[1], values))


def replace(term, path, value):
    if not path:
        return value
    if path[0] == 0:
        return App(replace(term.left, path[1:], value), term.right)
    return App(term.left, replace(term.right, path[1:], value))


def compile_worker(compiler):
    builder = GraphBuilder()
    yes, no = builder.uniform("true"), builder.uniform("false")
    start = compiler(builder, yes, no)
    return builder.finish(), start


def run(table, cursor):
    states, control = table
    # This instrumentation is outside the emitted controller.
    for _ in range(200000):
        command = states[control][OBSERVATIONS.index((cursor.kind, cursor.incoming))]
        if command.command in ("true", "false"):
            return command.command == "true", cursor
        if command.command != "stay":
            cursor = cursor.move(command.command)
        control = command.next_state
    raise AssertionError("synthetic test exceeded external microtick allowance")


class ActiveEndpointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.frame = compile_worker(compile_frame)
        cls.frontend = compile_worker(compile_frontend)
        cls.base = compile_worker(compile_base)
        cls.pending_base = compile_worker(compile_pending_base)
        cls.dispatcher = compile_worker(compile_dispatcher)
        cls.action = compile_worker(lambda b, y, n: b.rows(p.selected_action_rows(), y, n))

    def assert_selected(self, table, term, origin, expected):
        answer, cursor = run(table, Cursor.at(term, origin))
        self.assertTrue(answer)
        self.assertEqual(cursor.path, expected)
        self.assertIs(cursor.root, term)
        self.assertIsNotNone(root_arguments(cursor.focus))

    def assert_declined(self, table, term, origin):
        answer, cursor = run(table, Cursor.at(term, origin))
        self.assertFalse(answer)
        self.assertEqual(cursor.path, origin)
        self.assertIs(cursor.root, term)

    def test_frame_heads_below_pending_spines(self):
        for pattern, address in p.frame_head_rows():
            for depth in range(5):
                current = instantiate(pattern)
                for _ in range(depth):
                    current = apply(S, App(S, S), S, current)
                ambient = App(S, App(current, S))
                with self.subTest(address=address, depth=depth):
                    self.assert_selected(self.frame, ambient, (1, 0),
                                         (1, 0) + (1,) * depth + address)

    def test_frame_miss_restores_nested_left_boundary(self):
        for depth in range(6):
            current = App(S, S)
            for _ in range(depth):
                current = apply(S, S, App(S, S), current)
            self.assert_declined(self.frame, App(S, App(current, S)), (1, 0))

    def test_marked_local_uses_continuation_and_excludes_audit(self):
        term = instantiate(p.local_patterns("marked")[0])
        term = replace(term, (1, 0), S)
        audit = instantiate(p.frame_head_rows()[0][0])
        term = replace(term, (1, 1), audit)
        answer, cursor = run(self.frontend, Cursor.at(term))
        self.assertFalse(answer)
        self.assertEqual(cursor.path, (1, 0))
        self.assertIs(cursor.focus, S)
        self.assertIs(cursor.root, term)

    def test_fresh_local_requires_nonempty_before_continuation(self):
        pattern, accumulator = p.local_rows("fresh")[0]
        empty = replace(instantiate(pattern), accumulator, S)
        empty = replace(empty, (1, 0), S)
        self.assert_declined(self.frontend, empty, ())
        live = replace(empty, accumulator, App(LIVE[1], S))
        answer, cursor = run(self.frontend, Cursor.at(live))
        self.assertFalse(answer)
        self.assertEqual(cursor.path, (1, 0))
        self.assertIs(cursor.root, live)

    def test_base_oldest_then_odd_handoff_and_scope(self):
        pattern, queue_address = p.base_row()
        base = replace(instantiate(pattern), queue_address, App(LIVE[1], S))
        pending = replace(instantiate(p.pending_pattern()), (1,), base)
        expected = (1,) + queue_address
        self.assert_selected(self.base, pending, (1,), expected)
        self.assert_selected(self.pending_base, pending, (), expected)
        deleted = contract_at(pending, expected)
        self.assert_selected(self.base, deleted, (1,), ())
        self.assert_selected(self.pending_base, deleted, (), ())
        self.assert_declined(self.base, App(S, base), (1,))
        self.assert_declined(self.pending_base, App(S, base), ())

    def test_empty_base_hands_off_only_with_pending_parent(self):
        pattern, queue_address = p.base_row()
        base = replace(instantiate(pattern), queue_address, S)
        self.assert_declined(self.base, base, ())
        pending = replace(instantiate(p.pending_pattern()), (1,), base)
        self.assert_selected(self.base, pending, (1,), ())

    def test_all_dispatcher_stages_and_recovered_labels(self):
        for phase in (0, 1):
            if phase == 0:
                carrier_root = instantiate(p.base_pattern())
            else:
                # A completed phase-zero Local supplies successor phase one.
                carrier_root = instantiate(p.local_patterns("fresh")[0])
            for bit in (0, 1):
                # Cell descent recovers phase from its predecessor; the
                # deleted-bit scan reads this independent tombstone tag.
                carrier = apply(S, carrier_root,
                                App(instantiate(p.VALUES[bit]), App(S, S)))
                for index, (pattern, address) in enumerate(p.dispatcher_rows((phase, bit))):
                    term = replace(instantiate(pattern), (0, 0, 0, 1), carrier)
                    ambient = App(S, App(term, S))
                    with self.subTest(phase=phase, bit=bit, stage=index):
                        self.assert_selected(self.dispatcher, ambient, (1, 0), (1, 0) + address)

    def test_selected_action_and_push_with_independent_audits(self):
        for pattern, address in p.selected_action_rows():
            term = instantiate(pattern)
            self.assert_selected(self.action, App(S, App(term, S)), (1, 0), (1, 0) + address)

    def test_dispatcher_failed_phase_restores_exact_origin(self):
        term = instantiate(p.local_pattern("fresh"))
        term = replace(term, (0, 0, 0, 1), S)
        ambient = App(S, App(term, S))
        self.assert_declined(self.dispatcher, ambient, (1, 0))


if __name__ == "__main__":
    unittest.main()
