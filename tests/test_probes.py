"""Independent tuple oracles for finite read-only pattern tables."""
from dataclasses import FrozenInstanceError, fields
from functools import lru_cache
import unittest
from unittest.mock import patch

from s_only.probes import (
    HOLE, LITERAL_S, OBSERVATIONS, Configuration, Cursor, Instruction,
    InvalidMove, ProbeResult, ProbeTable, compile_pattern, compile_rows,
    execute, pattern_budget, step,
)
from s_only.terms import App, S


@lru_cache(maxsize=None)
def trees(leaves):
    if leaves == 1:
        return ("S",)
    return tuple(
        (left, right)
        for split in range(1, leaves)
        for left in trees(split)
        for right in trees(leaves - split)
    )


@lru_cache(maxsize=None)
def patterns(leaves):
    # None is the independent oracle's wildcard, not the compiler's marker.
    if leaves == 1:
        return (None, "S")
    return tuple(
        (left, right)
        for split in range(1, leaves)
        for left in patterns(split)
        for right in patterns(leaves - split)
    )


def matches(pattern, tree):
    if pattern is None:
        return True
    if pattern == "S":
        return tree == "S"
    return (tree != "S" and matches(pattern[0], tree[0])
            and matches(pattern[1], tree[1]))


def positions(tree, path=()):
    yield path
    if tree != "S":
        yield from positions(tree[0], path + (0,))
        yield from positions(tree[1], path + (1,))


def subtree(tree, path):
    for direction in path:
        tree = tree[direction]
    return tree


def term_from_tuple(tree):
    if tree == "S":
        return S
    return App(term_from_tuple(tree[0]), term_from_tuple(tree[1]))


def pattern_from_tuple(pattern):
    if pattern is None:
        return HOLE
    if pattern == "S":
        return LITERAL_S
    return (pattern_from_tuple(pattern[0]), pattern_from_tuple(pattern[1]))


def pattern_counts(pattern):
    if pattern is None:
        return 0, 0, 1
    if pattern == "S":
        return 0, 1, 0
    la, ls, lh = pattern_counts(pattern[0])
    ra, rs, rh = pattern_counts(pattern[1])
    return 1 + la + ra, ls + rs, lh + rh


def choose_row(rows, tree):
    for pattern, address in rows:
        if matches(pattern, tree):
            return address
    return None


def checked_run(table, cursor):
    """External test instrumentation, not part of the controller's state."""
    configuration = Configuration(table.start, cursor)
    bound = table.tick_bound
    for ticks in range(bound + 1):
        answer = table.answer(configuration.control)
        if answer is not None:
            if step(table, configuration) is not configuration:
                raise AssertionError("terminal state is not absorbing")
            return ProbeResult(answer, configuration.cursor), ticks
        configuration = step(table, configuration)
    raise AssertionError("table exceeded its static finite-state bound")


class CursorAssertions:
    def assert_restored(self, before, after):
        self.assertIs(after.focus, before.focus)
        self.assertEqual(after.path, before.path)
        self.assertIs(after.root, before.root)
        self.assertEqual(len(after.parents), len(before.parents))
        for actual, original in zip(after.parents, before.parents):
            self.assertIs(actual, original)


class RestoringPatternTests(CursorAssertions, unittest.TestCase):
    def test_exhaustive_corpus_sizes(self):
        self.assertEqual([len(trees(n)) for n in range(1, 9)],
                         [1, 1, 2, 5, 14, 42, 132, 429])
        self.assertEqual(sum(len(trees(n)) for n in range(1, 9)), 626)
        self.assertEqual([len(patterns(n)) for n in range(1, 5)], [2, 4, 16, 80])
        occurrences = sum(
            sum(1 for _ in positions(tree))
            for size in range(1, 9) for tree in trees(size)
        )
        self.assertEqual(occurrences, 8788)

    def test_all_102_patterns_on_all_626_rooted_trees(self):
        compiled = [
            (pattern, compile_pattern(pattern_from_tuple(pattern)))
            for size in range(1, 5) for pattern in patterns(size)
        ]
        checks = 0
        for size in range(1, 9):
            for tree in trees(size):
                original = term_from_tuple(tree)
                cursor = Cursor.at(original)
                for pattern, table in compiled:
                    result, ticks = checked_run(table, cursor)
                    self.assertEqual(result.answer, matches(pattern, tree),
                                     (pattern, tree))
                    self.assert_restored(cursor, result.cursor)
                    applications, literals, holes = pattern_counts(pattern)
                    self.assertEqual(len(table.states), 2 + 6 * applications + literals)
                    self.assertEqual(table.tick_bound, 5 * applications + literals)
                    self.assertLess(ticks, 6 * applications + 2 * literals + holes)
                    checks += 1
        self.assertEqual(checks, 63852)

    def test_all_22_small_patterns_at_every_occurrence_of_all_626_trees(self):
        compiled = [
            (pattern, compile_pattern(pattern_from_tuple(pattern)))
            for size in range(1, 4) for pattern in patterns(size)
        ]
        checks = 0
        for size in range(1, 9):
            for tree in trees(size):
                original = term_from_tuple(tree)
                for path in positions(tree):
                    cursor = Cursor.at(original, path)
                    focus = subtree(tree, path)
                    for pattern, table in compiled:
                        result, _ = checked_run(table, cursor)
                        self.assertEqual(result.answer, matches(pattern, focus),
                                         (pattern, tree, path))
                        self.assert_restored(cursor, result.cursor)
                        checks += 1
        self.assertEqual(checks, 193336)

    def test_late_right_mismatch_restores_nested_left_and_right_starts(self):
        pattern = ((HOLE, HOLE), (HOLE, LITERAL_S))
        table = compile_pattern(pattern)
        mismatching = App(App(S, S), App(S, App(S, S)))
        ambient = App(mismatching, mismatching)
        for path in ((), (0,), (1,), (0, 1), (1, 0)):
            cursor = Cursor.at(ambient, path)
            result, _ = checked_run(table, cursor)
            self.assertFalse(result.answer)
            self.assert_restored(cursor, result.cursor)

    def test_all_success_shapes_attain_the_exact_tick_bound(self):
        def fill_holes(pattern):
            if pattern is None or pattern == "S":
                return "S"
            return (fill_holes(pattern[0]), fill_holes(pattern[1]))
        for size in range(1, 5):
            for pattern in patterns(size):
                table = compile_pattern(pattern_from_tuple(pattern))
                cursor = Cursor.at(term_from_tuple(fill_holes(pattern)))
                result, ticks = checked_run(table, cursor)
                self.assertTrue(result.answer)
                self.assertEqual(ticks, table.tick_bound)
                self.assert_restored(cursor, result.cursor)

    def test_shared_subterms_are_distinct_occurrences(self):
        shared = App(S, S)
        ambient = App(shared, shared)
        table = compile_pattern((LITERAL_S, LITERAL_S))
        for path in ((0,), (1,)):
            cursor = Cursor.at(ambient, path)
            self.assertIs(cursor.focus, shared)
            result = execute(table, cursor)
            self.assertTrue(result.answer)
            self.assert_restored(cursor, result.cursor)

    def test_runtime_is_nonrecursive_and_does_not_use_term_equality(self):
        table = compile_pattern(((HOLE, LITERAL_S), LITERAL_S))
        focused = App(App(S, S), S)
        ambient = focused
        for _ in range(2000):
            ambient = App(S, ambient)
        cursor = Cursor.at(ambient, (1,) * 2000)
        # An equality-based matcher, hidden recursive source matcher, or
        # whole-tree serializer would fail this test.
        with patch.object(App, "__eq__", side_effect=AssertionError("term equality")), \
             patch.object(type(S), "__eq__", side_effect=AssertionError("term equality")), \
             patch("s_only.probes._Builder.match", side_effect=AssertionError("compiler at runtime")), \
             patch("s_only.terms.format_term", side_effect=AssertionError("term serialization")):
            result = execute(table, cursor)
            self.assertTrue(result.answer)
            self.assert_restored(cursor, result.cursor)
        self.assertEqual([field.name for field in fields(Configuration)], ["control", "cursor"])
        self.assertEqual([field.name for field in fields(Cursor)], ["focus", "parents"])
        self.assertEqual([field.name for field in fields(ProbeTable)], ["states", "start"])


class PrioritizedRowsTests(CursorAssertions, unittest.TestCase):
    def test_prioritized_rows_at_every_occurrence(self):
        row_sets = (
            (),
            (("S", ()),),
            ((("S", None), (1,)), ((None, None), (0,))),
            ((((None, "S"), None), (0, 1)),
             ((None, ("S", None)), (1, 0)), ((None, None), (1,)), (None, ())),
        )
        compiled = [
            (rows, compile_rows(tuple((pattern_from_tuple(pattern), address)
                                     for pattern, address in rows)))
            for rows in row_sets
        ]
        checks = 0
        for size in range(1, 9):
            for tree in trees(size):
                original = term_from_tuple(tree)
                for path in positions(tree):
                    cursor = Cursor.at(original, path)
                    focus = subtree(tree, path)
                    for rows, table in compiled:
                        selected = choose_row(rows, focus)
                        result, ticks = checked_run(table, cursor)
                        self.assertEqual(result.answer, selected is not None,
                                         (rows, tree, path))
                        self.assertIs(result.cursor.root, original)
                        if selected is None:
                            self.assert_restored(cursor, result.cursor)
                        else:
                            self.assertEqual(result.cursor.path, path + selected)
                            expected = Cursor.at(original, path + selected)
                            self.assertIs(result.cursor.focus, expected.focus)
                        forward_bound = sum(
                            pattern_budget(pattern_from_tuple(pattern)) + len(address)
                            for pattern, address in rows
                        )
                        self.assertLessEqual(ticks, forward_bound)
                        checks += 1
        self.assertEqual(checks, 35152)

    def test_first_match_wins_even_when_later_rows_overlap(self):
        tree = App(App(S, S), App(S, S))
        pattern = (HOLE, HOLE)
        for first, second in (((0,), (1,)), ((1,), (0,)), ((), (1,))):
            table = compile_rows(((pattern, first), (pattern, second)))
            result = execute(table, Cursor.at(tree))
            self.assertTrue(result.answer)
            self.assertEqual(result.cursor.path, first)
        table = compile_rows(((HOLE, ()), (pattern, (1,))))
        self.assertEqual(execute(table, Cursor.at(tree)).cursor.path, ())

    def test_failed_late_probe_restores_before_next_row(self):
        tree = App(App(S, S), App(S, App(S, S)))
        rows = (
            (((HOLE, HOLE), (HOLE, LITERAL_S)), (0, 0)),
            ((HOLE, HOLE), (1,)),
        )
        table = compile_rows(rows)
        result = execute(table, Cursor.at(tree))
        self.assertTrue(result.answer)
        self.assertEqual(result.cursor.path, (1,))
        self.assertIs(result.cursor.focus, tree.right)

    def test_addresses_are_checked_against_each_pattern(self):
        for pattern, address in (
            (HOLE, (0,)), (LITERAL_S, (1,)),
            ((HOLE, LITERAL_S), (0, 0)),
            ((HOLE, LITERAL_S), (1, 0)),
        ):
            with self.subTest(pattern=pattern, address=address):
                with self.assertRaisesRegex(ValueError, "guaranteed"):
                    compile_rows(((pattern, address),))
        # A row may select a hole itself, but cannot descend inside it.
        compile_rows((((HOLE, LITERAL_S), (0,)),))
        compile_rows((((HOLE, LITERAL_S), (1,)),))

    def test_row_state_count_and_bound(self):
        patterns_and_addresses = (
            ((None, "S"), (1,)),
            (((None, None), "S"), (0, 1)),
            ("S", ()),
        )
        table = compile_rows(tuple((pattern_from_tuple(pattern), address)
                                   for pattern, address in patterns_and_addresses))
        expected = 2
        coarse_bound = 0
        for pattern, address in patterns_and_addresses:
            apps, literals, _ = pattern_counts(pattern)
            expected += 6 * apps + literals + len(address)
            coarse_bound += 5 * apps + literals + len(address)
        self.assertEqual(len(table.states), expected)
        self.assertLessEqual(table.tick_bound, coarse_bound)


class TableBoundaryTests(unittest.TestCase):
    def test_table_is_total_and_every_reference_is_finite_and_backward(self):
        for size in range(1, 5):
            for pattern in patterns(size):
                table = compile_pattern(pattern_from_tuple(pattern))
                self.assertEqual(len(OBSERVATIONS), 6)
                for control, row in enumerate(table.states):
                    self.assertEqual(len(row), 6)
                    for observation, instruction in zip(OBSERVATIONS, row):
                        self.assertIs(table.transition(control, *observation), instruction)
                        if instruction.next_state is not None:
                            self.assertGreaterEqual(instruction.next_state, 0)
                            self.assertLess(instruction.next_state, control)
                self.assertLessEqual(table.tick_bound, len(table.states) - 2)

    def test_incoming_side_is_the_only_position_observation(self):
        false = (Instruction("false"),) * 6
        true = (Instruction("true"),) * 6
        for accepted_observation in OBSERVATIONS:
            branch = tuple(Instruction("stay", int(obs == accepted_observation))
                           for obs in OBSERVATIONS)
            table = ProbeTable((false, true, branch), 2)
            tree = App(App(S, S), S)
            # Include S/root as a separate invocation.
            cursors = [Cursor.at(S)] + [Cursor.at(tree, path)
                                      for path in ((), (0,), (0, 0), (0, 1), (1,))]
            cursors += [Cursor.at(App(S, App(S, S)), (1,))]
            observed = set()
            for cursor in cursors:
                local = cursor.kind, cursor.incoming
                observed.add(local)
                self.assertEqual(execute(table, cursor).answer,
                                 local == accepted_observation)
            self.assertEqual(observed, set(OBSERVATIONS))

    def test_input_term_table_and_cursor_are_immutable(self):
        tree = App(S, App(S, S))
        cursor = Cursor.at(tree, (1,))
        table = compile_pattern((HOLE, LITERAL_S))
        states_before = table.states
        result = execute(table, cursor)
        self.assertTrue(result.answer)
        self.assertIs(table.states, states_before)
        self.assertIs(result.cursor.root, tree)
        self.assertIs(result.cursor.focus, tree.right)
        for obj, name, value in (
            (table, "start", 0), (cursor, "focus", S),
            (tree, "left", tree.right), (table.states[0][0], "command", "true"),
            (cursor.parents[0], "side", "L"),
        ):
            with self.assertRaises(FrozenInstanceError):
                setattr(obj, name, value)
        with self.assertRaises(TypeError):
            table.states[0][0] = Instruction("true")

    def test_invalid_patterns_and_addresses_are_rejected(self):
        for pattern in (None, "K", "", 1, True, [], ["S", "S"], (),
                        ("S",), ("S", "S", "S"), ("S", None)):
            with self.subTest(pattern=pattern):
                with self.assertRaises(ValueError):
                    compile_pattern(pattern)
                with self.assertRaises(ValueError):
                    pattern_budget(pattern)
        for address in (None, [], [0], (2,), (-1,), (True,), (False,), (0.0,), ("L",)):
            with self.subTest(address=address):
                with self.assertRaises(ValueError):
                    compile_rows((((HOLE, HOLE), address),))
                with self.assertRaises(ValueError):
                    Cursor.at(App(S, S), address)
        for rows in ((None,), (("S",),), (["S", ()],)):
            with self.assertRaises(ValueError):
                compile_rows(rows)

    def test_invalid_instructions_tables_and_observations_are_rejected(self):
        for args in (("contract",), ("L",), ("stay", True), ("stay", -1),
                     ("true", 0), ("false", False)):
            with self.assertRaises(ValueError):
                Instruction(*args)
        terminal = (Instruction("false"),) * 6
        for states, start in (
            ((), 0), ([terminal], 0), ((terminal,), True), ((terminal,), -1),
            ((terminal,), 1), ((terminal[:-1],), 0), ((list(terminal),), 0),
            ((("false",) * 6,), 0),
            (((Instruction("stay", 0),) * 6,), 0),
            ((terminal, (Instruction("L", 2),) * 6), 1),
            ((terminal, (Instruction("L", 0),) * 5 + (Instruction("true"),)), 1),
            ((terminal[:5] + (Instruction("true"),),), 0),
        ):
            with self.subTest(states=states, start=start):
                with self.assertRaises(ValueError):
                    ProbeTable(states, start)
        table = compile_pattern(HOLE)
        for control in (-1, len(table.states), True, None):
            with self.assertRaises(ValueError):
                table.transition(control, "S", "root")
        for kind, incoming in (("leaf", "root"), ("S", "U"), (None, "L")):
            with self.assertRaises(ValueError):
                table.transition(table.start, kind, incoming)

    def test_absent_moves_raise_instead_of_silently_changing_semantics(self):
        with self.assertRaises(InvalidMove):
            Cursor.at(S, (0,))
        with self.assertRaises(InvalidMove):
            Cursor.at(S).move("U")
        with self.assertRaises(InvalidMove):
            Cursor.at(S).move("R")
        with self.assertRaises(ValueError):
            Cursor.at(S).move("stay")
        with self.assertRaises(TypeError):
            Cursor.at("S")
        terminal = (Instruction("false"),) * 6
        malformed = ProbeTable((terminal, (Instruction("L", 0),) * 6), 1)
        with self.assertRaises(InvalidMove):
            execute(malformed, Cursor.at(S))


if __name__ == "__main__":
    unittest.main()
