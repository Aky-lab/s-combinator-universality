"""Independent adversarial review of the exact succinct probe representation.

All expansion in this suite is bounded. Huge-table tests sample precomputed
occurrence rows and never enumerate their virtual state space or execute a
positive huge match.
"""
from contextlib import ExitStack
from dataclasses import replace
from functools import lru_cache
import random
import unittest
from unittest.mock import patch

from s_only import probes, succinct_probes
from s_only.probes import Configuration, Cursor, Instruction, OBSERVATIONS
from s_only.succinct_probes import SuccinctProbeTable, compile_pattern
from s_only.terms import App, S


@lru_cache(maxsize=None)
def exact_patterns(leaves):
    if leaves == 1:
        return ("_", "S")
    return tuple((left, right)
                 for split in range(1, leaves)
                 for left in exact_patterns(split)
                 for right in exact_patterns(leaves - split))


class PoisonStr(str):
    def __eq__(self, other):
        raise AssertionError("untrusted string equality")

    def __hash__(self):
        raise AssertionError("untrusted string hash")


class PoisonInt(int):
    def __lt__(self, other):
        raise AssertionError("untrusted integer ordering")

    def __eq__(self, other):
        raise AssertionError("untrusted integer equality")


class SuccinctProbeReviewTests(unittest.TestCase):
    def assert_table_equal(self, pattern, succinct=None):
        materialized = probes.compile_pattern(pattern)
        succinct = compile_pattern(pattern) if succinct is None else succinct
        self.assertEqual(succinct.state_count, len(materialized.states))
        self.assertEqual(succinct.start, materialized.start)
        self.assertEqual(succinct.tick_bound, materialized.tick_bound)
        # Reverse order makes this independent of any monotone-query history.
        for control in reversed(range(succinct.state_count)):
            self.assertIs(succinct.answer(control), materialized.answer(control))
            for observation in reversed(OBSERVATIONS):
                actual = succinct.transition(control, *observation)
                self.assertEqual(actual, materialized.transition(control, *observation))
                if actual.next_state is not None:
                    self.assertIs(type(actual.next_state), int)
                    self.assertGreaterEqual(actual.next_state, 0)
                    self.assertLess(actual.next_state, control)
        return succinct

    def test_all_2688_six_leaf_patterns_pointwise(self):
        patterns = exact_patterns(6)
        self.assertEqual(len(patterns), 2688)
        for pattern in patterns:
            self.assert_table_equal(pattern)

    def test_equal_but_distinct_tuples_are_not_structurally_interned(self):
        first, second = tuple(["S", "_"]), tuple(["S", "_"])
        self.assertEqual(first, second)
        self.assertIsNot(first, second)
        duplicated = self.assert_table_equal((first, second))
        shared = self.assert_table_equal((first, first))
        self.assertEqual(len(duplicated.nodes), 5)
        self.assertEqual(len(shared.nodes), 4)
        self.assertNotEqual(duplicated.nodes[-1].left, duplicated.nodes[-1].right)
        self.assertEqual(shared.nodes[-1].left, shared.nodes[-1].right)
        self.assertEqual(duplicated.state_count, shared.state_count)
        for control in range(shared.state_count):
            for observation in OBSERVATIONS:
                self.assertEqual(duplicated.transition(control, *observation),
                                 shared.transition(control, *observation))

    def test_handmade_valid_metadata_and_cross_branch_sharing(self):
        descriptor = type(compile_pattern("S").nodes[0])
        rng = random.Random(862219)
        for _ in range(50):
            nodes = [descriptor("_", None, None, 0, 0, 1),
                     descriptor("S", None, None, 1, 1, 1)]
            patterns = ["_", "S"]
            for _ in range(9):
                left, right = rng.randrange(len(nodes)), rng.randrange(len(nodes))
                a, b = nodes[left], nodes[right]
                nodes.append(descriptor("pair", left, right,
                                        6 + a.width + b.width,
                                        5 + a.ticks + b.ticks,
                                        1 + max(a.height, b.height)))
                patterns.append((patterns[left], patterns[right]))
            self.assert_table_equal(patterns[-1], SuccinctProbeTable(tuple(nodes), 10))
        # Legal unused descriptors do not alter the root fragment's semantics.
        nodes = (descriptor("S", None, None, 1, 1, 1),) * 16
        self.assert_table_equal("S", SuccinctProbeTable(nodes, 15))

    def test_corrupt_descriptor_fields_are_rejected_before_hooks_run(self):
        table = compile_pattern((("S", "_"), "S"))
        for index, node in enumerate(table.nodes):
            for field in ("width", "ticks", "height"):
                for value in (-1, True, False, 1.0, None, "1", [], PoisonInt(1)):
                    with self.subTest(index=index, field=field, value_type=type(value)):
                        changed = replace(node, **{field: value})
                        nodes = table.nodes[:index] + (changed,) + table.nodes[index + 1:]
                        with self.assertRaises(ValueError):
                            SuccinctProbeTable(nodes, table.root)
                # Nonnegative, correctly typed but incorrect counts are invalid.
                changed = replace(node, **{field: getattr(node, field) + 1})
                nodes = table.nodes[:index] + (changed,) + table.nodes[index + 1:]
                with self.assertRaises(ValueError):
                    SuccinctProbeTable(nodes, table.root)
            for kind in (None, True, [], "unknown", PoisonStr(node.kind)):
                changed = replace(node, kind=kind)
                nodes = table.nodes[:index] + (changed,) + table.nodes[index + 1:]
                with self.assertRaises(ValueError):
                    SuccinctProbeTable(nodes, table.root)
            for field in ("left", "right"):
                values = (-1, index, index + 1, True, 0.0, "0", [], PoisonInt(0))
                if node.kind == "pair":
                    values += (None,)
                else:
                    values += (0,)
                for value in values:
                    changed = replace(node, **{field: value})
                    nodes = table.nodes[:index] + (changed,) + table.nodes[index + 1:]
                    with self.assertRaises(ValueError):
                        SuccinctProbeTable(nodes, table.root)

    def test_api_rejects_subclass_controls_and_observations(self):
        table = compile_pattern(("S", "_"))
        for control in (PoisonInt(0), PoisonInt(table.start)):
            with self.assertRaises(ValueError):
                table.answer(control)
            with self.assertRaises(ValueError):
                table.transition(control, "S", "root")
        for control in (0, 1, table.start):
            for kind, incoming in ((PoisonStr("S"), "root"),
                                   ("S", PoisonStr("root")),
                                   (PoisonStr("application"), "L")):
                with self.assertRaises(ValueError):
                    table.transition(control, kind, incoming)

    def test_huge_doubled_mixed_pattern_boundary_rows(self):
        depth = 128
        pattern = ("_", "S")
        for _ in range(depth):
            pattern = (pattern, pattern)
        table = compile_pattern(pattern)
        self.assertEqual(len(table.nodes), depth + 3)
        self.assertEqual(table.state_count, 13 * (1 << depth) - 4)
        self.assertEqual(table.tick_bound, 11 * (1 << depth) - 5)
        self.assertEqual(table.lookup_depth_bound, depth + 2)

        # These selected occurrence layouts are assembled outside the lookup,
        # from the closed-form widths of this family. No table counts are read.
        rng = random.Random(491)
        paths = [(0,) * depth, (1,) * depth,
                 tuple(level % 2 for level in range(depth))]
        paths += [tuple(rng.randrange(2) for _ in range(depth)) for _ in range(5)]
        checked_rows = {}
        for path in paths:
            origin, yes, no = 2, 1, 0
            for level, side in enumerate(path):
                child_width = 13 * (1 << (depth - level - 1)) - 6
                right_move = origin + child_width + 2
                left_move = origin + 2 * child_width + 4
                rows = {
                    origin: (Instruction("U", yes),) * 2,
                    origin + 1: (Instruction("U", no),) * 2,
                    right_move: (Instruction("R", right_move - 1),) * 2,
                    right_move + 1: (Instruction("U", right_move),) * 2,
                    left_move: (Instruction("L", left_move - 1),) * 2,
                    left_move + 1: (Instruction("stay", no), Instruction("stay", left_move)),
                }
                checked_rows.update(rows)
                if side == 0:
                    origin, yes, no = right_move + 2, right_move + 1, origin + 1
                else:
                    origin, yes, no = origin + 2, origin, origin + 1
            # The bottom fragment is (_, S), independently spelling every row.
            checked_rows.update({
                origin: (Instruction("U", yes),) * 2,
                origin + 1: (Instruction("U", no),) * 2,
                origin + 2: (Instruction("stay", origin), Instruction("stay", origin + 1)),
                origin + 3: (Instruction("R", origin + 2),) * 2,
                origin + 4: (Instruction("U", origin + 3),) * 2,
                origin + 5: (Instruction("L", origin + 4),) * 2,
                origin + 6: (Instruction("stay", no), Instruction("stay", origin + 5)),
            })
        self.assertGreater(len(checked_rows), 5000)
        for control, expected in checked_rows.items():
            for kind, incoming in OBSERVATIONS:
                actual = table.transition(control, kind, incoming)
                self.assertEqual(actual, expected[kind == "application"])
                self.assertGreaterEqual(actual.next_state, 0)
                self.assertLess(actual.next_state, control)

    def test_transition_is_independent_of_terms_files_compilers_and_history(self):
        pattern = (("_", "S"), (("S", "_"), "S"))
        table = compile_pattern(pattern)
        original_nodes = table.nodes
        expected = {(control, observation): table.transition(control, *observation)
                    for control in range(table.state_count)
                    for observation in OBSERVATIONS}
        queries = list(expected)
        random.Random(74).shuffle(queries)
        with ExitStack() as stack:
            for name in ("builtins.open", "builtins.hash", "builtins.id",
                         "s_only.probes.compile_pattern", "s_only.probes._Builder.match",
                         "s_only.succinct_probes.compile_pattern", "s_only.terms.format_term",
                         "s_only.terms.prefix", "s_only.probes.Cursor.move"):
                stack.enter_context(patch(name, side_effect=AssertionError(name)))
            stack.enter_context(patch.object(App, "__getattribute__",
                                            side_effect=AssertionError("input term access")))
            for control, observation in queries + list(reversed(queries)):
                self.assertEqual(table.transition(control, *observation),
                                 expected[control, observation])
        self.assertIs(table.nodes, original_nodes)
        self.assertEqual(table.root, len(original_nodes) - 1)

    def test_both_failure_restorations_and_success_have_identical_primitive_traces(self):
        tables = (probes.compile_pattern(("S", "S")), compile_pattern(("S", "S")))
        cases = ((App(App(S, S), S), False, ("stay", "L", "stay", "U")),
                 (App(S, App(S, S)), False,
                  ("stay", "L", "stay", "U", "R", "stay", "U")),
                 (App(S, S), True, ("stay", "L", "stay", "U", "R", "stay", "U")))
        for focus, answer, commands in cases:
            ambient = App(focus, focus)
            for path in ((), (0,), (1,)):
                cursor = Cursor.at(focus if not path else ambient, path)
                configurations = [Configuration(table.start, cursor) for table in tables]
                for command in commands:
                    first, second = configurations
                    self.assertEqual(first.control, second.control)
                    self.assertIs(first.cursor.focus, second.cursor.focus)
                    self.assertEqual(first.cursor.path, second.cursor.path)
                    for index, table in enumerate(tables):
                        config = configurations[index]
                        instruction = table.transition(config.control, config.cursor.kind,
                                                       config.cursor.incoming)
                        self.assertEqual(instruction.command, command)
                        configurations[index] = probes.step(table, config)
                for table, config in zip(tables, configurations):
                    self.assertIs(table.answer(config.control), answer)
                    self.assertIs(config.cursor.focus, cursor.focus)
                    self.assertIs(config.cursor.root, cursor.root)
                    self.assertEqual(config.cursor.path, cursor.path)
                    self.assertIs(probes.step(table, config), config)


if __name__ == "__main__":
    unittest.main()
