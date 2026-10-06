"""Independent synthetic checks of the compiled priority-pass fragments.

Fixture constructors below use closed S terms, not the patterns being tested.
The bounded interpreter executes only emitted six-observation primitive rows;
it never calls a carrier decoder, pattern matcher, or source-machine schedule.
"""
from dataclasses import dataclass
from functools import lru_cache
import random
import unittest

from s_only.probes import OBSERVATIONS
from s_only.queue_fixture import (
    ACT, APPENDANTS, B, DISPATCH, HALT, HALT_TAG, LIVE, PI, VALUES, apply,
)
from s_only.selector_parts import priority
from s_only.selector_parts.graph import GraphBuilder
from s_only.terms import App, S


@dataclass(frozen=True)
class RunResult:
    answer: bool
    focus: object
    parents: tuple
    ticks: int

    @property
    def path(self):
        return tuple(side for _, side in self.parents)

    @property
    def root(self):
        return self.parents[0][0] if self.parents else self.focus


def checked_run(compiled, source, origin=(), *, bound=100_000):
    """Test-only primitive interpreter with an external microtick budget."""
    rows, control = compiled
    focus, parents = source, []
    for side in origin:
        if not isinstance(focus, App):
            raise AssertionError("invalid test invocation address")
        parents.append((focus, side))
        focus = focus.left if side == 0 else focus.right
    for ticks in range(bound + 1):
        kind = "application" if isinstance(focus, App) else "S"
        incoming = "root" if not parents else ("L" if parents[-1][1] == 0 else "R")
        row = rows[control]
        instruction = row[OBSERVATIONS.index((kind, incoming))]
        command = instruction.command
        if command in ("true", "false"):
            if any(entry != instruction for entry in row):
                raise AssertionError("answer depends on observation")
            return RunResult(command == "true", focus, tuple(parents), ticks)
        if command in ("L", "R"):
            if not isinstance(focus, App):
                raise AssertionError("graph attempted to descend from S")
            side = int(command == "R")
            parents.append((focus, side))
            focus = focus.left if side == 0 else focus.right
        elif command == "U":
            if not parents:
                raise AssertionError("graph attempted to ascend from root")
            focus, _ = parents.pop()
        elif command != "stay":
            raise AssertionError("unexpected primitive in read-only graph")
        control = instruction.next_state
    raise AssertionError("priority fragment exceeded external microtick budget")


@lru_cache(maxsize=None)
def compiled(name, *arguments):
    builder = GraphBuilder()
    yes = builder.uniform("true")
    no = builder.uniform("false")
    compiler = getattr(priority, "compile_" + name)
    entry = compiler(builder, *arguments, yes, no)
    return builder.finish(), entry


def _dispatch_response(specification, label, accumulator, audit):
    code, left, right, leaf = specification
    if leaf is not None:
        if leaf != label:
            return None
        response = App(PI, accumulator)
        retained = len(APPENDANTS[label[0]]) if label[1] else 0
        for _ in range(retained):
            response = App(response, audit)
        return apply(S, audit, response), (1,) + (0,) * retained + (1,)
    found = _dispatch_response(left, label, accumulator, audit)
    if found is not None:
        response, address = found
        return apply(S, audit, App(response, App(right[0], audit))), (1, 0) + address
    found = _dispatch_response(right, label, accumulator, audit)
    if found is None:
        return None
    response, address = found
    return apply(S, audit, App(App(left[0], audit), response)), (1, 1) + address


def completed_local(status, accumulator, *, label=(0, 0), audit=S):
    """Construct a completed response and independently locate its carrier."""
    dispatch, address = _dispatch_response(DISPATCH, label, accumulator, audit)
    halt = (App(HALT, audit) if status == "fresh"
            else apply(S, audit, App(HALT_TAG, audit)))
    local = apply(halt, dispatch, apply(S, audit, audit), App(S, audit))
    return local, (0, 0, 1) + address


def tombstone(bit, predecessor, audit=S):
    return apply(S, predecessor, App(VALUES[bit], audit))


def environment(carrier):
    return App(S, apply(S, ACT, App(S, carrier)))


def pending(child, audit=S):
    return apply(environment(S), audit, child)


def base(carrier):
    # Active and dormant environments deliberately carry different data.
    alpha = apply(environment(carrier), App(B, environment(App(S, S))), S)
    return apply(S, alpha, App(S, S))


def positions(source, address=()):
    yield address
    if isinstance(source, App):
        yield from positions(source.left, address + (0,))
        yield from positions(source.right, address + (1,))


class PriorityFragmentTests(unittest.TestCase):
    def assert_result(self, name, source, expected_answer, expected_path,
                      origin=(), arguments=()):
        result = checked_run(compiled(name, *arguments), source, origin)
        self.assertEqual((result.answer, result.path), (expected_answer, expected_path))
        self.assertIs(result.root, source)
        focus = source
        for parent_index, side in enumerate(expected_path):
            self.assertIs(result.parents[parent_index][0], focus)
            self.assertEqual(result.parents[parent_index][1], side)
            focus = focus.left if side == 0 else focus.right
        self.assertIs(result.focus, focus)
        return result

    def test_nonempty_restores_all_local_routes_and_valid_boundaries(self):
        for status in ("fresh", "marked"):
            for label in ((0, 0), (0, 1), (1, 0), (1, 1)):
                for carrier in (S, App(LIVE[0], S), App(LIVE[1], App(LIVE[0], S))):
                    local, _ = completed_local(status, carrier, label=label,
                                               audit=App(S, App(S, S)))
                    for source, origin in ((local, ()), (App(local, S), (0,)),
                                           (pending(local), (1,))):
                        with self.subTest(status=status, label=label, origin=origin):
                            self.assert_result("nonempty", source, carrier is not S,
                                               origin, origin)

    def test_parity_starts_true_and_only_local_tombstone_nodes_toggle(self):
        fresh, _ = completed_local("fresh", S)
        marked, _ = completed_local("marked", S)
        twice, _ = completed_local("fresh", marked)
        deleted = tombstone(0, S)
        local_deleted, _ = completed_local("fresh", deleted)
        fresh_through_live, _ = completed_local("fresh", App(LIVE[1], deleted))
        cases = ((S, True), (App(LIVE[0], S), True), (base(S), True),
                 (fresh, False), (marked, False), (deleted, False),
                 (twice, True), (local_deleted, True), (fresh_through_live, True),
                 (base(fresh), False))
        for source, answer in cases:
            with self.subTest(answer=answer):
                self.assert_result("parity", source, answer, ())
                self.assert_result("parity", pending(source), answer, (1,), (1,))

    def test_oldest_live_uses_complete_descent_then_first_live_ancestor(self):
        for status in ("fresh", "marked"):
            for label in ((0, 0), (0, 1), (1, 0), (1, 1)):
                for length in (0, 1, 2, 4):
                    carrier = S
                    for index in range(length):
                        carrier = App(LIVE[index % 2], carrier)
                    local, address = completed_local(status, carrier, label=label)
                    expected = address + (1,) * (length - 1) if length else ()
                    self.assert_result("oldest", local, bool(length), expected)
        carrier = App(LIVE[1], tombstone(0, App(LIVE[0], S)))
        local, address = completed_local("fresh", carrier)
        self.assert_result("oldest", local, True, address + (1, 0, 1))

    def test_empty_origin_stops_before_marked_local_and_tombstone(self):
        deleted = tombstone(1, S)
        fresh_deleted, _ = completed_local("fresh", deleted)
        marked_deleted, _ = completed_local("marked", deleted)
        for carrier, answer in ((S, True), (deleted, False),
                                (App(LIVE[0], deleted), False),
                                (fresh_deleted, False), (marked_deleted, True)):
            local, _ = completed_local("fresh", carrier)
            self.assert_result("empty_origin", local, answer, ())
            self.assert_result("empty_origin", pending(local), answer, (1,), (1,))

    def test_nonpending_completed_response_commits_only_empty_fresh_local(self):
        for label in ((0, 0), (0, 1), (1, 0), (1, 1)):
            for status in ("fresh", "marked"):
                for carrier in (S, App(LIVE[0], S)):
                    local, _ = completed_local(status, carrier, label=label)
                    ready = status == "fresh" and carrier is S
                    selected = (0, 0, 0) if ready else ()
                    self.assert_result("scoped_completed", local, ready, selected)
                    self.assert_result("scoped_completed", App(local, S), ready,
                                       (0,) + selected, (0,))

    def test_pending_response_empty_override_handoff_and_oldest_live(self):
        empty, _ = completed_local("fresh", S)
        self.assert_result("scoped_completed", pending(empty), True, (1, 0, 0, 0), (1,))
        live, _ = completed_local("fresh", App(LIVE[0], S))
        self.assert_result("scoped_completed", pending(live), True, (), (1,))
        deleted_empty, _ = completed_local("fresh", tombstone(0, S))
        self.assert_result("scoped_completed", pending(deleted_empty), True,
                           (1, 0, 0, 0), (1,))
        deleted_live, address = completed_local("fresh", tombstone(1, App(LIVE[0], S)))
        self.assert_result("scoped_completed", pending(deleted_live), True,
                           (1,) + address + (0, 1), (1,))
        marked_empty, _ = completed_local("marked", S)
        fresh_marked, _ = completed_local("fresh", marked_empty)
        self.assert_result("scoped_completed", pending(fresh_marked), True,
                           (1, 0, 0, 0), (1,))

    def test_registered_parent_guard_is_stricter_than_generic_handoff(self):
        local, _ = completed_local("fresh", S)
        generic = apply(S, S, S, local)
        for ambient in (App(S, local), generic):
            self.assert_result("pending_parent", ambient, False, (1,), (1,))
            self.assert_result("scoped_completed", ambient, False, (1,), (1,))
        self.assert_result("handoff", generic, True, (), (1,))
        registered = pending(local)
        self.assert_result("pending_parent", registered, True, (1,), (1,))
        self.assert_result("pending_parent", registered, False, (), ())
        self.assert_result("pending_parent", registered, False, (0,), (0,))

    def test_nearest_local_ancestor_includes_initial_occurrence(self):
        inner, inner_address = completed_local("fresh", S, label=(0, 1))
        middle, middle_address = completed_local("marked", inner, label=(1, 1))
        outer, outer_address = completed_local("fresh", middle, label=(1, 0))
        origin = outer_address + middle_address + inner_address
        self.assert_result("local_ancestor", outer, True, outer_address + middle_address,
                           origin, ("fresh",))
        self.assert_result("local_ancestor", outer, True, outer_address,
                           origin, ("marked",))
        self.assert_result("local_ancestor", outer, True, (), (), ("fresh",))
        self.assert_result("local_ancestor", S, False, (), (), ("marked",))

    def test_pending_ancestor_selects_nearest_registered_parent(self):
        local, _ = completed_local("marked", S)
        inner = pending(App(S, local))
        ambient = pending(App(S, inner))
        # Descend through the nearest pending child and its intermediate app.
        self.assert_result("pending_ancestor", ambient, True, (1, 1),
                           (1, 1, 1, 1))
        self.assert_result("pending_ancestor", ambient, True, (), (1, 1))
        self.assert_result("pending_ancestor", ambient, False, (), ())

    def test_random_small_syntax_rejects_and_scope_failure_restores(self):
        rng = random.Random(476)

        def tree(applications):
            if applications == 0:
                return S
            left = rng.randrange(applications)
            return App(tree(left), tree(applications - 1 - left))

        starts = 0
        for _ in range(100):
            source = tree(rng.randrange(24))
            for origin in positions(source):
                starts += 1
                self.assert_result("scoped_completed", source, False, origin, origin)
                self.assert_result("pending_ancestor", source, False, (), origin)
        self.assertGreater(starts, 1_000)

    def test_compiled_fragments_have_only_finite_readonly_primitive_rows(self):
        for name in ("nonempty", "parity", "oldest", "empty_origin",
                     "scoped_completed", "pending_parent", "pending_ancestor",
                     "fresh", "marked"):
            rows, start = compiled(name)
            self.assertIsInstance(start, int)
            self.assertIsInstance(rows, tuple)
            for row in rows:
                self.assertEqual(len(row), 6)
                for instruction in row:
                    self.assertIn(instruction.command, ("stay", "L", "R", "U", "true", "false"))
                    if instruction.command in ("true", "false"):
                        self.assertIsNone(instruction.next_state)
                    else:
                        self.assertIs(type(instruction.next_state), int)
                        self.assertTrue(0 <= instruction.next_state < len(rows))
            self.assert_result(name, S, name in ("parity", "empty_origin"), ())


if __name__ == "__main__":
    unittest.main()
