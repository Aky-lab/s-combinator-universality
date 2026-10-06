"""Pointwise and primitive-trace checks for succinct prioritized row code."""
from dataclasses import FrozenInstanceError, fields, replace
from functools import lru_cache
from itertools import product
import random
import unittest
from unittest.mock import patch

from s_only import probes, succinct_probes, succinct_rows
from s_only.probes import Configuration, Cursor, Instruction, OBSERVATIONS, execute, step
from s_only.succinct_rows import SuccinctRowsTable, compile_rows
from s_only.terms import App, S


@lru_cache(maxsize=None)
def patterns(leaves):
    if leaves == 1:
        return ("_", "S")
    return tuple((left, right)
                 for cut in range(1, leaves)
                 for left in patterns(cut)
                 for right in patterns(leaves - cut))


def addresses(pattern):
    pending = [(pattern, ())]
    while pending:
        node, address = pending.pop()
        yield address
        if type(node) is tuple:
            pending.extend(((node[1], address + (1,)), (node[0], address + (0,))))


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


def graph_profiles(table):
    """Independent DP to each terminal; no pattern recurrence is used here."""
    bounds = []
    for row in table.states:
        command = row[0].command
        if command in ("true", "false"):
            bounds.append((0, None) if command == "false" else (None, 0))
        else:
            profiles = []
            for terminal in (0, 1):
                paths = [bounds[entry.next_state][terminal] for entry in row]
                profiles.append(max((1 + bound for bound in paths if bound is not None),
                                    default=None))
            bounds.append(tuple(profiles))
    return bounds[table.start]


def bounded_run(table, cursor, limit):
    """Strict external harness; table.tick_bound cannot increase this budget."""
    configuration = Configuration(table.start, cursor)
    for ticks in range(limit + 1):
        answer = table.answer(configuration.control)
        if answer is not None:
            return answer, configuration.cursor, ticks
        if ticks < limit:
            configuration = step(table, configuration)
    raise AssertionError("row execution exceeded external microtick limit")


class SuccinctRowsTests(unittest.TestCase):
    def assert_pointwise_equal(self, rows):
        materialized = probes.compile_rows(rows)
        succinct = compile_rows(rows)
        self.assertEqual(succinct.state_count, len(materialized.states))
        self.assertEqual(succinct.start, materialized.start)
        self.assertEqual(succinct.tick_bound, materialized.tick_bound)
        for control in range(succinct.state_count):
            self.assertIs(succinct.answer(control), materialized.answer(control))
            for observation in OBSERVATIONS:
                instruction = succinct.transition(control, *observation)
                self.assertEqual(instruction, materialized.transition(control, *observation))
                self.assertIs(type(instruction), Instruction)
                self.assertIs(type(instruction.command), str)
                if instruction.next_state is not None:
                    self.assertIs(type(instruction.next_state), int)
                    self.assertLess(instruction.next_state, control)
        return materialized, succinct

    def assert_same_cursor(self, first, second):
        self.assertIs(first.focus, second.focus)
        self.assertIs(first.root, second.root)
        self.assertEqual(first.path, second.path)
        self.assertEqual(len(first.parents), len(second.parents))
        for a, b in zip(first.parents, second.parents):
            self.assertIs(a.parent, b.parent)
            self.assertEqual(a.side, b.side)

    def test_independently_written_reversed_address_and_pattern_layout(self):
        table = compile_rows(((("S", "_"), (1,)), ("S", ())))
        expected = (
            (Instruction("false"), Instruction("false")),
            (Instruction("true"), Instruction("true")),
            (Instruction("stay", 1), Instruction("stay", 0)),
            (Instruction("R", 1), Instruction("R", 1)),
            (Instruction("U", 3), Instruction("U", 3)),
            (Instruction("U", 2), Instruction("U", 2)),
            (Instruction("R", 4), Instruction("R", 4)),
            (Instruction("U", 6), Instruction("U", 6)),
            (Instruction("stay", 7), Instruction("stay", 5)),
            (Instruction("L", 8), Instruction("L", 8)),
            (Instruction("stay", 2), Instruction("stay", 9)),
        )
        self.assertEqual((table.state_count, table.start, table.tick_bound), (11, 10, 7))
        for control, row in enumerate(expected):
            for kind, incoming in OBSERVATIONS:
                self.assertEqual(table.transition(control, kind, incoming),
                                 row[int(kind == "application")])
        pattern = (("_", "_"), ("_", "_"))
        table = compile_rows(((pattern, (1, 0)),))
        self.assertEqual(table.transition(2, "S", "root"), Instruction("L", 1))
        self.assertEqual(table.transition(3, "S", "root"), Instruction("R", 2))

    def test_empty_and_zero_state_wildcards_keep_unreachable_controls(self):
        cases = (
            ((), (2, 0, 0, 0)),
            ((("_", ()),), (2, 1, 0, 0)),
            ((("_", ()),) * 5, (2, 1, 0, 0)),
            ((("_", ()), ("S", ())), (3, 1, 0, 1)),
            ((("S", ()), ("_", ()), (("S", "S"), ())), (11, 10, 1, 2)),
            ((("S", ()), ("_", ()), ("_", ()), ("S", ())), (4, 3, 1, 2)),
        )
        for rows, expected in cases:
            with self.subTest(rows=rows):
                _, table = self.assert_pointwise_equal(rows)
                self.assertEqual((table.state_count, table.start, table.tick_bound,
                                  len(table.blocks)), expected)
        table = compile_rows((("S", ()), ("_", ()), (("S", "S"), ())))
        self.assertEqual(table.transition(10, "application", "root"), Instruction("stay", 1))
        self.assertEqual(table.blocks[-1].no, 1)

    def test_all_2955_small_row_lists_preserve_every_observation(self):
        options = tuple((pattern, address)
                        for size in (1, 2) for pattern in patterns(size)
                        for address in addresses(pattern))
        self.assertEqual(len(options), 14)
        checked = 0
        for count in range(4):
            for rows in product(options, repeat=count):
                self.assert_pointwise_equal(rows)
                checked += 1
        self.assertEqual(checked, 2955)

    def test_larger_seeded_lists_shared_dags_and_scoped_addresses(self):
        rng = random.Random(62271)
        for _ in range(180):
            pool = ["_", "S"]
            for _ in range(7):
                pool.append((rng.choice(pool), rng.choice(pool)))
            rows = []
            for _ in range(rng.randrange(9)):
                pattern = rng.choice(pool)
                node, address = pattern, ()
                while type(node) is tuple and rng.randrange(3):
                    direction = rng.randrange(2)
                    node, address = node[direction], address + (direction,)
                rows.append((pattern, address))
            self.assert_pointwise_equal(rows)

    def test_success_failure_profiles_against_independent_graph_dp(self):
        checked = 0
        for size in range(1, 5):
            for pattern in patterns(size):
                expected_failure, expected_success = graph_profiles(probes.compile_pattern(pattern))
                table = compile_rows(((pattern, ()),))
                code = table.patterns[0]
                self.assertEqual(code.failure_ticks, expected_failure)
                self.assertEqual(code.probe.tick_bound, expected_success)
                checked += 1
        self.assertEqual(checked, 102)
        self.assertIsNone(compile_rows((("_", ()),)).patterns[0].failure_ticks)
        code = compile_rows(((("_", "_"), ()),)).patterns[0]
        self.assertEqual((code.probe.tick_bound, code.failure_ticks), (5, 1))

    def test_graph_bound_need_not_be_attained_by_an_input_tree(self):
        table = compile_rows(((("_", "_"), ()), (("S", "S"), ())))
        self.assertEqual(table.tick_bound, 8)
        for size in range(1, 6):
            for tree in trees(size):
                answer, cursor, ticks = bounded_run(table, Cursor.at(tree), 5)
                self.assertEqual(ticks, 2 if tree is S else 5)
                self.assertEqual(answer, tree is not S)
                self.assertIs(cursor.focus, tree)

    def test_full_microtick_traces_and_selected_cursor_at_every_small_occurrence(self):
        options = tuple((pattern, address)
                        for size in (1, 2) for pattern in patterns(size)
                        for address in addresses(pattern))
        row_lists = [()] + [(row,) for row in options] + list(product(options, repeat=2))
        compiled = [(probes.compile_rows(rows), compile_rows(rows)) for rows in row_lists]
        checks = 0
        for size in range(1, 5):
            for tree in trees(size):
                for cursor in cursors(tree):
                    for materialized, succinct in compiled:
                        first = Configuration(materialized.start, cursor)
                        second = Configuration(succinct.start, cursor)
                        for _ in range(materialized.tick_bound + 1):
                            self.assertEqual(first.control, second.control)
                            self.assert_same_cursor(first.cursor, second.cursor)
                            self.assertIs(materialized.answer(first.control),
                                          succinct.answer(second.control))
                            if materialized.answer(first.control) is not None:
                                self.assertIs(step(materialized, first), first)
                                self.assertIs(step(succinct, second), second)
                                break
                            first, second = step(materialized, first), step(succinct, second)
                        else:
                            self.fail("trace exceeded the original graph bound")
                        actual = execute(succinct, cursor)
                        self.assertEqual(actual.answer, materialized.answer(first.control))
                        self.assert_same_cursor(actual.cursor, first.cursor)
                        checks += 1
        self.assertEqual(checks, 10339)

    def test_first_match_priority_and_nonroot_failure_restoration(self):
        shared = App(S, App(S, S))
        ambient = App(shared, shared)
        rows = ((("_", "_"), (0,)), (("S", "_"), (1,)))
        for invocation in ((0,), (1,)):
            cursor = Cursor.at(ambient, invocation)
            first = execute(compile_rows(rows), cursor)
            second = execute(compile_rows(tuple(reversed(rows))), cursor)
            self.assertTrue(first.answer)
            self.assertEqual(first.cursor.path, invocation + (0,))
            self.assertTrue(second.answer)
            self.assertEqual(second.cursor.path, invocation + (1,))
            failed = execute(compile_rows((("S", ()), (("S", "S"), (0,)))), cursor)
            self.assertFalse(failed.answer)
            self.assert_same_cursor(failed.cursor, cursor)

    def test_identity_reuse_keeps_separate_occurrence_intervals(self):
        first = tuple(["S", "_"])
        equal_distinct = tuple(["S", "_"])
        self.assertIsNot(first, equal_distinct)
        rows = ((first, (0,)), (first, (1,)), (equal_distinct, ()))
        with patch("s_only.succinct_rows.compile_pattern", wraps=succinct_probes.compile_pattern) as compiler:
            table = compile_rows(rows)
        self.assertEqual(compiler.call_count, 2)
        self.assertEqual(len(table.patterns), 2)
        self.assertEqual([block.pattern for block in table.blocks], [1, 0, 0])
        self.assertEqual(table.state_count, 25)
        self.assertEqual(table.blocks[1].stop, table.blocks[2].origin)
        self.assertNotEqual(table.blocks[1].no, table.blocks[2].no)
        self.assert_pointwise_equal(rows)

    def test_frozen_plain_metadata_and_runtime_needs_no_source_or_compiler(self):
        table = compile_rows(((("S", "_"), (1,)), ("S", ())))
        cursor = Cursor.at(App(S, App(S, S)))
        self.assertEqual([field.name for field in fields(table)],
                         ["patterns", "blocks", "start", "ticks"])
        for obj, attribute in ((table, "start"), (table.blocks[0], "no"),
                               (table.patterns[0], "failure_ticks"),
                               (table.patterns[0].probe, "root"),
                               (table.patterns[0].probe.nodes[0], "width")):
            with self.assertRaises(FrozenInstanceError):
                setattr(obj, attribute, 0)
        self.assertFalse(hasattr(table, "__dict__"))
        self.assertEqual([field.name for field in fields(Configuration)], ["control", "cursor"])
        self.assertIs(type(table.patterns), tuple)
        self.assertIs(type(table.blocks), tuple)
        before = repr(table)
        forbidden = AssertionError("runtime source, compiler, file, or term equality access")
        with patch("s_only.probes.compile_rows", side_effect=forbidden), \
             patch("s_only.probes.compile_pattern", side_effect=forbidden), \
             patch("s_only.probes._Builder.match", side_effect=forbidden), \
             patch("s_only.succinct_rows.compile_rows", side_effect=forbidden), \
             patch("s_only.succinct_rows.compile_pattern", side_effect=forbidden), \
             patch("s_only.succinct_rows._failure_ticks", side_effect=forbidden), \
             patch("s_only.succinct_rows._validate_selection", side_effect=forbidden), \
             patch("builtins.open", side_effect=forbidden), \
             patch.object(App, "__eq__", side_effect=forbidden), \
             patch.object(type(S), "__eq__", side_effect=forbidden), \
             patch.object(App, "__hash__", side_effect=forbidden), \
             patch("s_only.terms.format_term", side_effect=forbidden), \
             patch("s_only.terms.prefix", side_effect=forbidden):
            for _ in range(4):
                result = execute(table, cursor)
                self.assertTrue(result.answer)
                self.assertIs(result.cursor.focus, cursor.focus.right)
                self.assertEqual(result.cursor.path, (1,))
        self.assertEqual(repr(table), before)

    def test_binary_search_and_pattern_decoder_iteration_bounds(self):
        rows = tuple((("S", "_"), (0,) if i % 2 else ()) for i in range(37))
        table = compile_rows(rows)
        block_type = type(table.blocks[0])
        descriptor_type = type(table.patterns[0].probe.nodes[0])
        block_get = block_type.__getattribute__
        descriptor_get = descriptor_type.__getattribute__
        counts = [0, 0]
        movement = {control for block in table.blocks
                    for control in range(block.origin, block.origin + len(block.address))}

        def read_block(block, name):
            if name == "origin":
                counts[0] += 1
            return block_get(block, name)

        def read_descriptor(node, name):
            if name == "kind":
                counts[1] += 1
            return descriptor_get(node, name)

        with patch.object(block_type, "__getattribute__", read_block), \
             patch.object(descriptor_type, "__getattribute__", read_descriptor):
            for control in range(table.state_count):
                for observation in OBSERVATIONS:
                    counts[:] = [0, 0]
                    table.transition(control, *observation)
                    search = counts[0] - int(control >= 2) - int(control in movement)
                    self.assertLessEqual(search, table.block_lookup_bound)
                    self.assertLessEqual(counts[1], table.pattern_lookup_depth_bound)
                    self.assertLessEqual(search + counts[1], table.lookup_depth_bound)
                    if control < 2:
                        self.assertEqual((search, counts[1]), (0, 0))
                    else:
                        self.assertGreaterEqual(search, 1)
        large = compile_rows((("S", ()),) * 4097)
        self.assertEqual(large.block_lookup_bound, 13)
        for control in (2, 3, 2050, large.state_count - 1):
            self.assertEqual(large.transition(control, "application", "R"),
                             Instruction("stay", control - 1 if control > 2 else 0))

    def test_deep_shared_virtual_patterns_fail_under_external_tick_caps(self):
        depth = 4096
        pattern = "S"
        for _ in range(depth):
            pattern = (pattern, pattern)
        with patch("s_only.probes.compile_rows", side_effect=AssertionError("materialization")), \
             patch("s_only.probes._Builder.match", side_effect=AssertionError("materialization")):
            table = compile_rows(((pattern, (1,) * depth), (pattern, ())))
        self.assertEqual(len(table.patterns), 1)
        self.assertEqual(len(table.patterns[0].probe.nodes), depth + 1)
        self.assertEqual(len(table.blocks), 2)
        self.assertEqual(table.state_count, 14 * (1 << depth) + depth - 10)
        self.assertEqual(table.tick_bound, 2 * (6 * (1 << depth) - 5))
        self.assertEqual(table.start, table.state_count - 1)
        self.assertEqual(table.transition(2 + 2 * depth, "S", "R"),
                         Instruction("stay", 2 * depth))
        self.assertEqual(table.lookup_depth_bound, depth + 3)
        for focus, limit in ((S, 2), (App(S, S), 8)):
            ambient = App(focus, focus)
            cursor = Cursor.at(ambient, (1,))
            answer, restored, ticks = bounded_run(table, cursor, limit)
            self.assertFalse(answer)
            self.assertEqual(ticks, limit)
            self.assert_same_cursor(restored, cursor)
        with self.assertRaisesRegex(AssertionError, "external microtick"):
            bounded_run(table, Cursor.at(App(S, S)), 7)

    def test_deep_linear_pattern_scoped_leaf_without_recursion(self):
        depth = 6000
        pattern = "_"
        for _ in range(depth):
            pattern = ("S", pattern)
        table = compile_rows(((pattern, (1,) * depth),))
        self.assertEqual(len(table.patterns[0].probe.nodes), depth + 2)
        self.assertEqual(table.state_count, 8 * depth + 2)
        self.assertEqual(table.tick_bound, 7 * depth)
        answer, cursor, ticks = bounded_run(table, Cursor.at(S), 1)
        self.assertFalse(answer)
        self.assertIs(cursor.focus, S)
        self.assertEqual(ticks, 1)

    def test_invalid_rows_addresses_and_patterns_reject_custom_callbacks(self):
        class PoisonInt(int):
            def __eq__(self, other):
                raise AssertionError("custom equality")

        class PoisonTuple(tuple):
            def __len__(self):
                raise AssertionError("custom length")

        class PoisonStr(str):
            def __hash__(self):
                raise AssertionError("custom hashing")
            def __eq__(self, other):
                raise AssertionError("custom equality")

        bad_rows = (None, [], (), ("S",), ("S", (), 1), PoisonTuple(("S", ())))
        for row in bad_rows:
            with self.assertRaises(ValueError):
                compile_rows((row,))
        for address in ([], None, "", (True,), (2,), (-1,), (1.0,), (PoisonInt(0),),
                        PoisonTuple((0,))):
            with self.assertRaises(ValueError):
                compile_rows(((("_", "_"), address),))
        for pattern in (PoisonStr("S"), PoisonTuple(("S", "_")), [], ("S", [])):
            with self.assertRaises(ValueError):
                compile_rows(((pattern, ()),))
        for pattern, address in (("_", (0,)), ("S", (1,)), (("_", "S"), (0, 1)),
                                 (("S", "_"), (1, 0)), (("_", "S"), (1, 0))):
            with self.assertRaisesRegex(ValueError, "guaranteed"):
                compile_rows(((pattern, address),))
        deep_bad = []
        for _ in range(6000):
            deep_bad = ("S", deep_bad)
        with self.assertRaises(ValueError):
            compile_rows(((deep_bad, ()),))
        # Any finite iterable is accepted, while each row/address stays immutable.
        self.assertEqual(compile_rows(iter((("S", ()),))).state_count, 3)

    def test_constructor_rejects_malformed_immutable_code_and_targets(self):
        table = compile_rows(((("S", "_"), (1,)), ("S", ())))
        for changes in ({"patterns": list(table.patterns)}, {"blocks": list(table.blocks)},
                        {"start": True}, {"start": 0}, {"start": table.state_count},
                        {"ticks": True}, {"ticks": -1}, {"ticks": table.ticks + 1},
                        {"patterns": (object(),)}, {"blocks": (object(),)}):
            with self.subTest(changes=changes):
                with self.assertRaises(ValueError):
                    replace(table, **changes)
        code = table.patterns[0]
        for bad in (replace(code, probe=object()), replace(code, failure_ticks=True),
                    replace(code, failure_ticks=-1), replace(code, failure_ticks=None),
                    replace(code, failure_ticks=code.failure_ticks + 1)):
            with self.assertRaises(ValueError):
                replace(table, patterns=(bad,) + table.patterns[1:])
        first, second = table.blocks
        for changes in ({"origin": True}, {"stop": -1}, {"pattern": True},
                        {"no": True}, {"origin": first.origin + 1},
                        {"stop": first.stop + 1}, {"pattern": len(table.patterns)},
                        {"address": []}, {"address": (0,)}, {"no": 2}):
            with self.assertRaises(ValueError):
                replace(table, blocks=(replace(first, **changes), second))
        with self.assertRaises(ValueError):
            replace(table, blocks=(first, replace(second, no=3)))
        zero = compile_rows((("_", ()),))
        with self.assertRaises(ValueError):
            replace(zero, blocks=(replace(first, pattern=0, stop=2),))
        # Valid unused immutable code is permitted, but does not create states.
        extra = compile_rows(((("S", "S"), ()),)).patterns
        empty = SuccinctRowsTable(extra, (), 0, 0)
        self.assertEqual((empty.state_count, empty.tick_bound), (2, 0))
        for observation in OBSERVATIONS:
            self.assertEqual(empty.transition(0, *observation), Instruction("false"))

    def test_invalid_controls_and_observations_include_terminal_states(self):
        table = compile_rows((("S", ()),))
        for control in (-1, table.state_count, True, 1.0, "1", None):
            with self.assertRaises(ValueError):
                table.answer(control)
            with self.assertRaises(ValueError):
                table.transition(control, "S", "root")
        class StrSubclass(str):
            pass
        for kind, incoming in ((None, "root"), ("S", []), ("leaf", "root"),
                               ("S", "up"), (StrSubclass("S"), "L"),
                               ("S", StrSubclass("root"))):
            for control in (0, table.start):
                with self.assertRaises(ValueError):
                    table.transition(control, kind, incoming)


if __name__ == "__main__":
    unittest.main()
