"""Pointwise and trace differential checks for exact succinct probe code."""
from dataclasses import FrozenInstanceError, fields, replace
from functools import lru_cache
import random
import unittest
from unittest.mock import patch

from s_only import probes, succinct_probes
from s_only.probes import Configuration, Cursor, Instruction, OBSERVATIONS, execute, step
from s_only.succinct_probes import SuccinctProbeTable, compile_pattern
from s_only.terms import App, S


@lru_cache(maxsize=None)
def patterns(leaves):
    if leaves == 1:
        return ("_", "S")
    return tuple((left, right)
                 for cut in range(1, leaves)
                 for left in patterns(cut)
                 for right in patterns(leaves - cut))


@lru_cache(maxsize=None)
def trees(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right)
                 for cut in range(1, leaves)
                 for left in trees(cut)
                 for right in trees(leaves - cut))


def cursors(term):
    pending = [Cursor.at(term)]
    while pending:
        cursor = pending.pop()
        yield cursor
        if isinstance(cursor.focus, App):
            pending.extend((cursor.move("R"), cursor.move("L")))


def bounded_run(table, cursor, limit):
    """An external harness; a huge virtual tick bound cannot extend this limit."""
    configuration = Configuration(table.start, cursor)
    for ticks in range(limit + 1):
        answer = table.answer(configuration.control)
        if answer is not None:
            return answer, configuration.cursor, ticks
        if ticks < limit:
            configuration = step(table, configuration)
    raise AssertionError("probe exceeded the external microtick limit")


class SuccinctProbeTests(unittest.TestCase):
    def assert_pointwise_equal(self, pattern):
        materialized = probes.compile_pattern(pattern)
        succinct = compile_pattern(pattern)
        self.assertEqual(succinct.state_count, len(materialized.states))
        self.assertEqual(succinct.start, materialized.start)
        self.assertEqual(succinct.tick_bound, materialized.tick_bound)
        for control in range(succinct.state_count):
            self.assertIs(succinct.answer(control), materialized.answer(control))
            for kind, incoming in OBSERVATIONS:
                instruction = succinct.transition(control, kind, incoming)
                self.assertEqual(instruction, materialized.transition(control, kind, incoming))
                self.assertIs(type(instruction), Instruction)
                self.assertIs(type(instruction.command), str)
                if instruction.next_state is not None:
                    self.assertLess(instruction.next_state, control)
        return materialized, succinct

    def assert_same_cursor(self, first, second):
        self.assertIs(first.focus, second.focus)
        self.assertEqual(first.path, second.path)
        self.assertIs(first.root, second.root)
        for a, b in zip(first.parents, second.parents):
            self.assertIs(a.parent, b.parent)
            self.assertEqual(a.side, b.side)

    def test_independent_pair_layout_including_zero_width_children(self):
        # Literal left, hole right: inner self.move('R', ...) allocates before U.
        table = compile_pattern(("S", "_"))
        self.assertEqual(table.start, 8)
        expected = (
            (Instruction("false"), Instruction("false")),
            (Instruction("true"), Instruction("true")),
            (Instruction("U", 1), Instruction("U", 1)),
            (Instruction("U", 0), Instruction("U", 0)),
            (Instruction("R", 2), Instruction("R", 2)),
            (Instruction("U", 4), Instruction("U", 4)),
            (Instruction("stay", 5), Instruction("stay", 3)),
            (Instruction("L", 6), Instruction("L", 6)),
            (Instruction("stay", 0), Instruction("stay", 7)),
        )
        for control, row in enumerate(expected):
            for kind, incoming in OBSERVATIONS:
                self.assertEqual(table.transition(control, kind, incoming),
                                 row[int(kind == "application")])
        for pattern in (("_", "_"), ("_", "S"), ("S", "S")):
            self.assert_pointwise_equal(pattern)

    def test_all_550_patterns_with_up_to_five_leaves(self):
        checked = 0
        for size in range(1, 6):
            for pattern in patterns(size):
                self.assert_pointwise_equal(pattern)
                checked += 1
        self.assertEqual(checked, 550)

    def test_seeded_mixed_shared_dags_preserve_all_occurrence_controls(self):
        rng = random.Random(71651)
        for _ in range(100):
            pool = ["_", "S"]
            for _ in range(8):
                pool.append((rng.choice(pool), rng.choice(pool)))
            self.assert_pointwise_equal(pool[-1])
        shared = ("S", "_")
        table = compile_pattern((shared, shared))
        self.assertEqual(len(table.nodes), 4)
        self.assertEqual(table.state_count, 22)
        self.assertEqual(table.nodes[table.root].left, table.nodes[table.root].right)
        # The identical descriptors have different continuations in their two
        # occurrence intervals; no quotient of those controls has been taken.
        self.assertNotEqual(table.transition(4, "S", "root"),
                            table.transition(13, "S", "root"))

    def test_full_microtick_traces_at_every_small_tree_occurrence(self):
        compiled = [self.assert_pointwise_equal(pattern)
                    for size in range(1, 5) for pattern in patterns(size)]
        checks = 0
        for size in range(1, 6):
            for term in trees(size):
                for cursor in cursors(term):
                    for materialized, succinct in compiled:
                        first = Configuration(materialized.start, cursor)
                        second = Configuration(succinct.start, cursor)
                        for ticks in range(materialized.tick_bound + 1):
                            self.assertEqual(first.control, second.control)
                            self.assert_same_cursor(first.cursor, second.cursor)
                            self.assertIs(materialized.answer(first.control),
                                          succinct.answer(second.control))
                            if materialized.answer(first.control) is not None:
                                self.assertIs(step(materialized, first), first)
                                self.assertIs(step(succinct, second), second)
                                self.assert_same_cursor(cursor, second.cursor)
                                break
                            first, second = step(materialized, first), step(succinct, second)
                        else:
                            self.fail("trace exceeded the materialized static bound")
                        checks += 1
        self.assertEqual(checks, 17850)

    def test_each_lookup_uses_at_most_the_compiled_height_iterations(self):
        descriptor_type = type(compile_pattern("S").nodes[0])
        original = descriptor_type.__getattribute__
        iterations = 0

        def counted_getattribute(node, name):
            nonlocal iterations
            # Exactly one selected-descriptor kind read occurs per loop.
            # Child-width metadata reads do not count as new iterations.
            if name == "kind":
                iterations += 1
            return original(node, name)

        tables = [compile_pattern(pattern)
                  for size in range(1, 5) for pattern in patterns(size)]
        with patch.object(descriptor_type, "__getattribute__", counted_getattribute):
            for table in tables:
                for control in range(table.state_count):
                    for observation in OBSERVATIONS:
                        iterations = 0
                        table.transition(control, *observation)
                        self.assertLessEqual(iterations, table.lookup_depth_bound)
                        if control < 2:
                            self.assertEqual(iterations, 0)
                        else:
                            self.assertGreaterEqual(iterations, 1)

    def test_existing_execute_and_exact_positive_tick_bound(self):
        def fill(pattern):
            return S if type(pattern) is str else App(fill(pattern[0]), fill(pattern[1]))
        for size in range(1, 5):
            for pattern in patterns(size):
                table = compile_pattern(pattern)
                focus = fill(pattern)
                ambient = App(focus, focus)
                for path in ((0,), (1,)):
                    cursor = Cursor.at(ambient, path)
                    answer, restored, ticks = bounded_run(table, cursor, table.tick_bound)
                    self.assertTrue(answer)
                    self.assertEqual(ticks, table.tick_bound)
                    self.assert_same_cursor(cursor, restored)
                    result = execute(table, cursor)
                    self.assertTrue(result.answer)
                    self.assert_same_cursor(cursor, result.cursor)

    def test_runtime_has_no_source_term_matching_or_mutable_cache(self):
        table = compile_pattern((("_", "S"), "S"))
        focus = App(App(S, S), S)
        ambient = focus
        for _ in range(2000):
            ambient = App(S, ambient)
        cursor = Cursor.at(ambient, (1,) * 2000)
        original_nodes = table.nodes
        with patch.object(App, "__eq__", side_effect=AssertionError("term equality")), \
             patch.object(type(S), "__eq__", side_effect=AssertionError("term equality")), \
             patch("s_only.probes._Builder.match", side_effect=AssertionError("materialization")), \
             patch("s_only.succinct_probes.compile_pattern",
                   side_effect=AssertionError("compilation")), \
             patch("s_only.terms.format_term", side_effect=AssertionError("serialization")):
            for _ in range(2):
                result = execute(table, cursor)
                self.assertTrue(result.answer)
                self.assert_same_cursor(cursor, result.cursor)
        self.assertIs(table.nodes, original_nodes)
        self.assertEqual([f.name for f in fields(table)], ["nodes", "root"])
        self.assertFalse(hasattr(table, "__dict__"))
        self.assertEqual([f.name for f in fields(Configuration)], ["control", "cursor"])
        with self.assertRaises(FrozenInstanceError):
            table.root = 0
        with self.assertRaises(FrozenInstanceError):
            table.nodes[0].width = 100

    def test_deep_unshared_input_has_no_recursive_validation_or_hashing(self):
        pattern = "S"
        depth = 6000
        for _ in range(depth):
            pattern = (pattern, "_")
        table = compile_pattern(pattern)
        self.assertEqual(len(table.nodes), depth + 2)
        self.assertEqual(table.state_count, 6 * depth + 3)
        self.assertEqual(table.tick_bound, 5 * depth + 1)
        self.assertEqual(table.lookup_depth_bound, depth + 1)
        # This control is the deepest literal test, reached by index decoding
        # alone; no input traversal is involved in this lookup.
        deepest_literal = 4 * depth + 2
        self.assertEqual(table.transition(deepest_literal, "S", "root"),
                         Instruction("stay", deepest_literal - 1))
        self.assertEqual(bounded_run(table, Cursor.at(S), 1)[0::2], (False, 1))

    def test_large_doubled_literal_dag_under_strict_external_tick_limits(self):
        depth = 4096
        pattern = "S"
        for _ in range(depth):
            pattern = (pattern, pattern)
        # Materializing or recursively hashing this occurrence tree is
        # infeasible.  The compile path must visit shared objects by identity.
        with patch("s_only.probes.compile_pattern",
                   side_effect=AssertionError("materialization")), \
             patch("s_only.probes._Builder.match", side_effect=AssertionError("materialization")):
            table = compile_pattern(pattern)
        self.assertEqual(len(table.nodes), depth + 1)
        self.assertEqual(table.state_count, 7 * (1 << depth) - 4)
        self.assertEqual(table.tick_bound, 6 * (1 << depth) - 5)
        self.assertEqual(table.lookup_depth_bound, depth + 1)
        self.assertEqual(table.start, table.state_count - 1)
        # Control 2 + 2*depth is the first-emitted literal, inside the chain
        # of right occurrences.  Exercise all 4097 descriptor levels.
        self.assertEqual(table.transition(2 + 2 * depth, "S", "R"),
                         Instruction("stay", 2 * depth))
        for focus, cap in ((S, 1), (App(S, S), 4)):
            ambient = App(focus, focus)
            cursor = Cursor.at(ambient, (1,))
            answer, restored, ticks = bounded_run(table, cursor, cap)
            self.assertFalse(answer)
            self.assertEqual(ticks, cap)
            self.assert_same_cursor(cursor, restored)
        with self.assertRaisesRegex(AssertionError, "external microtick"):
            bounded_run(table, Cursor.at(App(S, S)), 3)

    def test_invalid_patterns_are_rejected_without_user_equality_or_hashing(self):
        class PoisonStr(str):
            def __eq__(self, other):
                raise AssertionError("custom equality")
            def __hash__(self):
                raise AssertionError("custom hashing")
        class PoisonTuple(tuple):
            def __len__(self):
                raise AssertionError("custom length")
        cycle = []
        cycle.append(cycle)
        bad = (None, True, 1, "", "s", [], (), ("S",), ("S", "_", "S"),
               ("S", []), ("S", PoisonStr("S")), PoisonTuple(("S", "_")), cycle)
        for pattern in bad:
            with self.subTest(type=type(pattern)):
                with self.assertRaises(ValueError):
                    compile_pattern(pattern)
        deep_bad = []
        for _ in range(6000):
            deep_bad = ("S", deep_bad)
        with self.assertRaises(ValueError):
            compile_pattern(deep_bad)

    def test_unused_valid_descriptors_do_not_change_the_root_table(self):
        pattern = "S"
        for _ in range(12):
            pattern = (pattern, pattern)
        spare = compile_pattern(pattern).nodes
        # The public constructor permits unused immutable metadata.  Its
        # root descriptor index is larger than its entire virtual control set.
        table = SuccinctProbeTable(spare + (spare[0],), len(spare))
        self.assertGreater(table.root, table.state_count)
        literal = probes.compile_pattern("S")
        self.assertEqual(table.state_count, len(literal.states))
        self.assertEqual(table.start, literal.start)
        self.assertEqual(table.tick_bound, literal.tick_bound)
        self.assertEqual(table.lookup_depth_bound, 1)
        for control in range(table.state_count):
            self.assertIs(table.answer(control), literal.answer(control))
            for observation in OBSERVATIONS:
                self.assertEqual(table.transition(control, *observation),
                                 literal.transition(control, *observation))

    def test_control_observation_and_descriptor_bounds(self):
        table = compile_pattern(("S", "_"))
        for control in (-1, table.state_count, table.state_count + 1, True, 1.0, "1", None):
            with self.assertRaises(ValueError):
                table.transition(control, "S", "root")
            with self.assertRaises(ValueError):
                table.answer(control)
        for kind, incoming in ((None, "root"), ("S", None), ("leaf", "root"),
                               ("S", "up"), ([], "L"), ("application", True)):
            with self.assertRaises(ValueError):
                table.transition(0, kind, incoming)
        for nodes, root in ((list(table.nodes), table.root), ((), 0), (table.nodes, True),
                            (table.nodes, 0), ((object(),), 0)):
            with self.assertRaises(ValueError):
                SuccinctProbeTable(nodes, root)
        replacements = (
            replace(table.nodes[-1], width=table.state_count),
            replace(table.nodes[-1], ticks=-1),
            replace(table.nodes[-1], height=True),
            replace(table.nodes[-1], left=table.root),
            replace(table.nodes[-1], right=True),
            replace(table.nodes[-1], kind="unknown"),
        )
        for descriptor in replacements:
            with self.assertRaises(ValueError):
                SuccinctProbeTable(table.nodes[:-1] + (descriptor,), table.root)
        with self.assertRaises(ValueError):
            SuccinctProbeTable((replace(table.nodes[0], left=0),), 0)


if __name__ == "__main__":
    unittest.main()
