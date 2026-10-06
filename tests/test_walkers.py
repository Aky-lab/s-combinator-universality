"""Independent structural oracles for finite looping spine tables."""
from dataclasses import FrozenInstanceError, fields
from functools import lru_cache
import inspect
import unittest
from unittest.mock import PropertyMock, patch

from s_only.probes import (
    HOLE, OBSERVATIONS, Configuration, Cursor, Instruction, ProbeResult,
    ProbeTable, compile_rows,
)
from s_only.terms import App, S
from s_only.walkers import (
    WalkerTable, compile_ascent, compile_descent, compile_inverse_rows,
    execute, step,
)


@lru_cache(maxsize=None)
def trees(leaves):
    if leaves == 1:
        return ("S",)
    return tuple((left, right) for split in range(1, leaves)
                 for left in trees(split) for right in trees(leaves - split))


def positions(tree, path=()):
    yield path
    if tree != "S":
        yield from positions(tree[0], path + (0,))
        yield from positions(tree[1], path + (1,))


def subtree(tree, path):
    for direction in path:
        tree = tree[direction]
    return tree


def matches(pattern, tree):
    if pattern is None:
        return True
    if pattern == "S":
        return tree == "S"
    return (tree != "S" and matches(pattern[0], tree[0])
            and matches(pattern[1], tree[1]))


def term(tree):
    return S if tree == "S" else App(term(tree[0]), term(tree[1]))


def pattern(tree):
    if tree is None:
        return HOLE
    return "S" if tree == "S" else (pattern(tree[0]), pattern(tree[1]))


def prepared(rows):
    return tuple((pattern(source), address) for source, address in rows)


def forward(rows, tree, path):
    for source, address in rows:
        if matches(source, subtree(tree, path)):
            return path + address
    return None


def backward(rows, tree, path):
    # Pure structural specification. No production compiler/cursor machinery.
    for source, address in rows:
        count = len(address)
        if len(path) >= count and path[-count:] == address:
            ancestor = path[:-count]
            if matches(source, subtree(tree, ancestor)):
                return ancestor
    return None


def walk(choose, rows, tree, path):
    while True:
        after = choose(rows, tree, path)
        if after is None:
            return path
        path = after


def checked_run(table, cursor, bound):
    """External resource instrumentation; never part of runtime control."""
    configuration = Configuration(table.start, cursor)
    for ticks in range(bound + 1):
        answer = table.answer(configuration.control)
        if answer is not None:
            if step(table, configuration) is not configuration:
                raise AssertionError("terminal is not absorbing")
            return ProbeResult(answer, configuration.cursor), ticks
        configuration = step(table, configuration)
    raise AssertionError("execution exceeded its proved microtick bound")


ROW_SETS = (
    (),
    (((None, None), (0,)),),
    (((None, None), (1,)),),
    ((("S", None), (1,)), ((None, None), (0,))),
    ((((None, None), None), (0, 1)),
     ((None, ("S", None)), (1, 0)), ((None, None), (1,))),
    ((("S", None), (1,)), (((None, None), None), (0, 1))),
)


class CursorAssertions:
    def assert_occurrence(self, actual, expected):
        self.assertIs(actual.focus, expected.focus)
        self.assertIs(actual.root, expected.root)
        self.assertEqual(actual.path, expected.path)
        self.assertEqual(len(actual.parents), len(expected.parents))
        for got, wanted in zip(actual.parents, expected.parents):
            self.assertIs(got.parent, wanted.parent)
            self.assertEqual(got.side, wanted.side)


class StructuralOracleTests(CursorAssertions, unittest.TestCase):
    def test_all_626_trees_and_all_8788_nested_starts(self):
        self.assertEqual(sum(len(trees(n)) for n in range(1, 9)), 626)
        programs = [(rows, compile_descent(prepared(rows)),
                     compile_inverse_rows(prepared(rows)), compile_ascent(prepared(rows)))
                    for rows in ROW_SETS]
        starts = invocations = 0
        for leaves in range(1, 9):
            for source in trees(leaves):
                ambient = term(source)
                for path in positions(source):
                    starts += 1
                    cursor = Cursor.at(ambient, path)
                    focus_size = sum(1 for _ in positions(subtree(source, path)))
                    for rows, descent, inverse, ascent in programs:
                        result, _ = checked_run(descent, cursor,
                                                descent.coefficient * focus_size)
                        self.assertFalse(result.answer)
                        expected_path = walk(forward, rows, source, path)
                        self.assert_occurrence(result.cursor, Cursor.at(ambient, expected_path))
                        result, _ = checked_run(inverse, cursor, inverse.tick_bound)
                        expected_path = backward(rows, source, path)
                        self.assertEqual(result.answer, expected_path is not None)
                        self.assert_occurrence(result.cursor, Cursor.at(
                            ambient, path if expected_path is None else expected_path))
                        result, _ = checked_run(ascent, cursor,
                                                ascent.coefficient * (len(path) + 1))
                        self.assertFalse(result.answer)
                        expected_path = walk(backward, rows, source, path)
                        self.assert_occurrence(result.cursor, Cursor.at(ambient, expected_path))
                        invocations += 3
        self.assertEqual(starts, 8788)
        self.assertEqual(invocations, 158184)

    def test_failed_inverse_restores_on_every_reversed_address_prefix(self):
        source_pattern = (((HOLE, HOLE), (HOLE, HOLE)), "S")
        table = compile_inverse_rows(((source_pattern, (0, 1, 0)),))
        deep = App(App(App(S, S), App(S, S)), App(S, S))
        ambient = App(deep, deep)
        cases = (
            (),             # No first parent.
            (1,),           # First incoming side differs from L.
            (0,),           # One ascent, then root instead of R.
            (0, 0),         # One ascent, then L instead of R.
            (1, 0),         # Two ascents, then root instead of L.
            (1, 1, 0),      # Two ascents, then R instead of L.
            (0, 1, 0),      # All directions match, but ancestor pattern fails.
        )
        for path in cases:
            with self.subTest(path=path):
                cursor = Cursor.at(ambient, path)
                result, _ = checked_run(table, cursor, table.tick_bound)
                self.assertFalse(result.answer)
                self.assert_occurrence(result.cursor, cursor)

    def test_late_pattern_failure_restores_before_later_candidate(self):
        # Row 1 climbs twice and fails late in the ancestor's right subtree.
        # Row 2 must start again at the original leaf, not the candidate root.
        rows = (
            (((HOLE, HOLE), (HOLE, "S")), (0, 1)),
            (("S", "S"), (1,)),
        )
        ambient = App(App(S, S), App(S, App(S, S)))
        table = compile_inverse_rows(rows)
        result = execute(table, Cursor.at(ambient, (0, 1)))
        self.assertTrue(result.answer)
        self.assert_occurrence(result.cursor, Cursor.at(ambient, (0,)))

    def test_one_inverse_row_undoes_its_successful_forward_edge(self):
        for rows in ROW_SETS[1:]:
            for row in rows:
                inverse = compile_inverse_rows(prepared((row,)))
                for leaves in range(1, 7):
                    for source in trees(leaves):
                        if matches(row[0], source):
                            ambient = App(S, term(source))
                            cursor = Cursor.at(ambient, (1,))
                            endpoint = Cursor.at(ambient, (1,) + row[1])
                            result = execute(inverse, endpoint)
                            self.assertTrue(result.answer)
                            self.assert_occurrence(result.cursor, cursor)

    def test_suffix_free_addresses_reconstruct_root_started_paths(self):
        families = (
            ROW_SETS[3],
            ((("S", None), (0,)), (((None, None), None), (0, 1))),
            ((((None, None), None), (0, 1)),
             ((None, (None, None)), (1, 0))),
        )
        for rows in families:
            descent, ascent = compile_descent(prepared(rows)), compile_ascent(prepared(rows))
            for leaves in range(1, 9):
                for source in trees(leaves):
                    cursor = Cursor.at(term(source))
                    down = execute(descent, cursor)
                    up = execute(ascent, down.cursor)
                    self.assert_occurrence(up.cursor, cursor)


class InverseAdmissibilityTests(CursorAssertions, unittest.TestCase):
    def test_inverse_can_accept_a_row_shadowed_by_forward_priority(self):
        rows = (((HOLE, HOLE), (0,)), ((HOLE, HOLE), (1,)))
        ambient = App(S, S)
        inverse = execute(compile_inverse_rows(rows), Cursor.at(ambient, (1,)))
        self.assertTrue(inverse.answer)
        self.assertEqual(inverse.cursor.path, ())
        forward_result = execute(compile_rows(rows), inverse.cursor)
        self.assertEqual(forward_result.cursor.path, (0,))

    def test_ambiguous_ancestor_candidates_break_descent_round_trip(self):
        rows = ((("S", HOLE), (1,)), (((HOLE, HOLE), HOLE), (0, 1)))
        ambient = App(App(S, S), S)
        down = execute(compile_descent(rows), Cursor.at(ambient))
        self.assertEqual(down.cursor.path, (0, 1))
        up = execute(compile_ascent(rows), down.cursor)
        # The first row recognizes the nearer (S S), although the descending
        # edge used the second row at the root.
        self.assertEqual(up.cursor.path, (0,))
        self.assertIs(up.cursor.focus, ambient.left)

    def test_nested_start_requires_an_inverse_boundary(self):
        rows = (((HOLE, HOLE), (1,)),)
        ambient = App(S, App(S, S))
        original = Cursor.at(ambient, (1,))
        down = execute(compile_descent(rows), original)
        up = execute(compile_ascent(rows), down.cursor)
        self.assertEqual(down.cursor.path, (1, 1))
        self.assertEqual(up.cursor.path, ())
        self.assertNotEqual(up.cursor.path, original.path)


class RuntimeAndBoundaryTests(CursorAssertions, unittest.TestCase):
    def test_empty_addresses_rejected_even_in_shadowed_rows(self):
        for compiler in (compile_descent, compile_inverse_rows, compile_ascent):
            for rows in (((HOLE, ()),), (((HOLE, HOLE), (0,)), (HOLE, ()))):
                with self.subTest(compiler=compiler.__name__, rows=rows):
                    with self.assertRaisesRegex(ValueError, "nonempty"):
                        compiler(rows)
        for compiler in (compile_descent, compile_ascent):
            table = compiler(())
            result, ticks = checked_run(table, Cursor.at(S), table.coefficient)
            self.assertFalse(result.answer)
            self.assertEqual(ticks, 0)

    def test_input_patterns_rows_and_scope_remain_checked(self):
        invalid = (
            (None,), (("S",),), (["S", (0,)],),
            ((None, (0,)),), (("S", []),), ((HOLE, (True,)),),
            ((HOLE, (0,)),), (((HOLE, HOLE), (0, 0)),),
        )
        for compiler in (compile_descent, compile_inverse_rows, compile_ascent):
            for rows in invalid:
                with self.subTest(compiler=compiler.__name__, rows=rows):
                    with self.assertRaises(ValueError):
                        compiler(rows)

    def test_static_state_counts_and_coarse_microtick_bounds(self):
        def counts(source):
            if source is None:
                return 0, 0
            if source == "S":
                return 0, 1
            la, ls = counts(source[0])
            ra, rs = counts(source[1])
            return 1 + la + ra, ls + rs

        for rows in ROW_SETS:
            descent = compile_descent(prepared(rows))
            inverse = compile_inverse_rows(prepared(rows))
            ascent = compile_ascent(prepared(rows))
            forward_states = inverse_states = 2
            forward_bound = inverse_bound = 0
            for source, address in rows:
                applications, literals = counts(source)
                forward_states += 6 * applications + literals + len(address)
                inverse_states += 6 * applications + literals + 3 * len(address)
                forward_bound += 5 * applications + literals + len(address)
                inverse_bound += 5 * applications + literals + 3 * len(address)
            self.assertEqual(len(descent.states), forward_states)
            self.assertEqual(len(inverse.states), inverse_states)
            self.assertEqual(len(ascent.states), inverse_states)
            self.assertLessEqual(descent.pass_bound, forward_bound)
            self.assertLessEqual(inverse.tick_bound, inverse_bound)
            self.assertEqual(ascent.pass_bound, inverse.tick_bound)

    def test_tables_are_total_immutable_and_have_only_designated_feedback(self):
        for rows in ROW_SETS:
            for compiler in (compile_descent, compile_ascent):
                table = compiler(prepared(rows))
                self.assertEqual(table.coefficient, table.pass_bound + 1)
                for state, row in enumerate(table.states):
                    self.assertEqual(len(row), 6)
                    for observation, instruction in zip(OBSERVATIONS, row):
                        self.assertIs(table.transition(state, *observation), instruction)
                        if state == table.feedback:
                            self.assertEqual(instruction, Instruction("stay", table.start))
                        elif instruction.next_state is not None:
                            self.assertLess(instruction.next_state, state)
                with self.assertRaises(FrozenInstanceError):
                    table.start = 0
                with self.assertRaises(FrozenInstanceError):
                    table.states[0][0].command = "true"
                with self.assertRaises(TypeError):
                    table.states[0][0] = Instruction("true")
                if rows:
                    with self.assertRaises(ValueError):
                        ProbeTable(table.states, table.start)
        self.assertEqual([f.name for f in fields(WalkerTable)], ["states", "start", "feedback"])
        self.assertEqual([f.name for f in fields(Configuration)], ["control", "cursor"])
        self.assertEqual([f.name for f in fields(Cursor)], ["focus", "parents"])
        self.assertEqual(list(inspect.signature(WalkerTable.transition).parameters),
                         ["self", "control", "kind", "incoming"])

    def test_invalid_tables_and_local_observations_are_rejected(self):
        false = (Instruction("false"),) * 6
        restart = (Instruction("stay", 2),) * 6
        entry = (Instruction("stay", 0),) * 6
        valid = (false, restart, entry)
        for states, start, feedback in (
            ((), 0, 1), ([false, restart, entry], 2, 1),
            (valid, True, 1), (valid, -1, 1), (valid, 3, 1),
            (valid, 2, True), (valid, 2, -1), (valid, 2, 3),
            (valid, 1, 1), ((false, restart[:5], entry), 2, 1),
            ((false, list(restart), entry), 2, 1),
            ((false, ("stay",) * 6, entry), 2, 1),
            ((false, (Instruction("stay", 0),) * 6, entry), 2, 1),
            ((false, restart, (Instruction("stay", 2),) * 6), 2, 1),
            ((false, restart, (Instruction("stay", 99),) * 6), 2, 1),
            ((false, restart, entry[:5] + (Instruction("true"),)), 2, 1),
            ((false[:5] + (Instruction("true"),), restart, entry), 2, 1),
        ):
            with self.subTest(states=states, start=start, feedback=feedback):
                with self.assertRaises(ValueError):
                    WalkerTable(states, start, feedback)
        table = WalkerTable(valid, 2, 1)
        for control in (-1, 3, True, None):
            with self.assertRaises(ValueError):
                table.transition(control, "S", "root")
        for kind, incoming in (("leaf", "L"), ("S", "U"), (None, "root")):
            with self.assertRaises(ValueError):
                table.transition(2, kind, incoming)

    def test_shared_subtree_occurrences_remain_distinct(self):
        shared = App(S, S)
        ambient = App(shared, shared)
        inverse = compile_inverse_rows(((("S", "S"), (0,)),))
        for branch in (0, 1):
            cursor = Cursor.at(ambient, (branch, 0))
            result = execute(inverse, cursor)
            self.assertTrue(result.answer)
            self.assertEqual(result.cursor.path, (branch,))
            self.assertIs(result.cursor.focus, shared)
        # Scoped two-edge address with late mismatching ancestor pattern.
        failed = compile_inverse_rows(((((HOLE, HOLE), "S"), (0, 0)),))
        original = Cursor.at(ambient, (0, 0))
        self.assert_occurrence(execute(failed, original).cursor, original)

    def test_long_spines_without_runtime_patterns_equality_paths_or_counters(self):
        ambient = S
        depth = 2000
        for _ in range(depth):
            ambient = App(S, ambient)
        origin = Cursor.at(ambient)
        bottom = Cursor.at(ambient, (1,) * depth)
        rows = (((HOLE, HOLE), (1,)),)
        descent, ascent = compile_descent(rows), compile_ascent(rows)
        # Patches detect hidden structural matching, inspection, serialization,
        # and recompilation. Only kind/incoming and cursor moves are available.
        with patch.object(App, "__eq__", side_effect=AssertionError("term equality")), \
             patch.object(type(S), "__eq__", side_effect=AssertionError("term equality")), \
             patch.object(Cursor, "path", new_callable=PropertyMock, side_effect=AssertionError("path register")), \
             patch.object(Cursor, "root", new_callable=PropertyMock, side_effect=AssertionError("root observation")), \
             patch("s_only.walkers.compile_pattern", side_effect=AssertionError("runtime compiler")), \
             patch("s_only.walkers.compile_rows", side_effect=AssertionError("runtime compiler")), \
             patch("s_only.terms.format_term", side_effect=AssertionError("serialization")):
            down, down_ticks = checked_run(descent, origin, descent.coefficient * (2 * depth + 1))
            up, up_ticks = checked_run(ascent, bottom, ascent.coefficient * (depth + 1))
        self.assertEqual(down_ticks, 7 * depth + 1)
        self.assertEqual(up_ticks, 8 * depth + 1)
        self.assert_occurrence(down.cursor, bottom)
        self.assert_occurrence(up.cursor, origin)

    def test_feedback_boundaries_strictly_progress_and_preserve_term_each_tick(self):
        ambient = App(App(S, App(S, S)), App(App(S, S), S))
        rows = prepared(ROW_SETS[4])
        for table, cursor, descending in (
            (compile_descent(rows), Cursor.at(ambient), True),
            (compile_ascent(rows), Cursor.at(ambient, (1, 0, 1)), False),
        ):
            configuration = Configuration(table.start, cursor)
            previous_depth = len(cursor.parents)
            while table.answer(configuration.control) is None:
                self.assertIs(configuration.cursor.root, ambient)
                if configuration.control == table.feedback:
                    depth = len(configuration.cursor.parents)
                    if descending:
                        self.assertGreater(depth, previous_depth)
                    else:
                        self.assertLess(depth, previous_depth)
                    previous_depth = depth
                configuration = step(table, configuration)
            self.assertIs(configuration.cursor.root, ambient)


if __name__ == "__main__":
    unittest.main()
