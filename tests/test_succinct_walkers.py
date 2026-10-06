"""Exact same-index and primitive-trace checks for succinct spine walkers."""
from contextlib import ExitStack
from dataclasses import FrozenInstanceError, fields, replace
from functools import lru_cache
from itertools import product
import inspect
import random
import unittest
from unittest.mock import patch

from s_only import probes, succinct_probes, succinct_rows, succinct_walkers, walkers
from s_only.encoding import C0, HALT, LIVE, append_routine, encode_word
from s_only.probes import Configuration, Cursor, Instruction, OBSERVATIONS
from s_only.succinct_walkers import (
    SuccinctInverseRowsTable, SuccinctWalkerTable,
    compile_ascent, compile_descent, compile_inverse_rows,
)
from s_only.terms import App, S, nodes
from s_only.walkers import execute, step


@lru_cache(maxsize=None)
def patterns(leaves):
    if leaves == 1:
        return ("_", "S")
    return tuple((left, right) for cut in range(1, leaves)
                 for left in patterns(cut) for right in patterns(leaves - cut))


def addresses(pattern):
    pending = [(pattern, ())]
    while pending:
        item, address = pending.pop()
        if address:
            yield address
        if type(item) is tuple:
            pending.extend(((item[1], address + (1,)), (item[0], address + (0,))))


@lru_cache(maxsize=None)
def trees(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for cut in range(1, leaves)
                 for left in trees(cut) for right in trees(leaves - cut))


def cursors(term):
    pending = [Cursor.at(term)]
    while pending:
        cursor = pending.pop()
        yield cursor
        if isinstance(cursor.focus, App):
            pending.extend((cursor.move("R"), cursor.move("L")))


def graph_profiles(table):
    """Independent six-edge DP with a separate profile for each terminal."""
    bounds = []
    for row in table.states:
        command = row[0].command
        if command in ("false", "true"):
            bounds.append((0, None) if command == "false" else (None, 0))
        else:
            bounds.append(tuple(max((1 + bounds[entry.next_state][terminal]
                                     for entry in row
                                     if bounds[entry.next_state][terminal] is not None),
                                    default=None) for terminal in (0, 1)))
    return bounds[table.start]


def bounded_run(table, cursor, limit):
    """External harness; a huge static coefficient cannot enlarge this budget."""
    configuration = Configuration(table.start, cursor)
    for ticks in range(limit + 1):
        answer = table.answer(configuration.control)
        if answer is not None:
            return answer, configuration.cursor, ticks
        if ticks < limit:
            configuration = step(table, configuration)
    raise AssertionError("walker exceeded external microtick limit")


COMPILERS = (
    (walkers.compile_inverse_rows, compile_inverse_rows),
    (walkers.compile_descent, compile_descent),
    (walkers.compile_ascent, compile_ascent),
)
OPTIONS = tuple((pattern, address) for pattern in patterns(2)
                for address in addresses(pattern))


class SuccinctWalkerTests(unittest.TestCase):
    def assert_same_cursor(self, first, second):
        self.assertIs(first.focus, second.focus)
        self.assertIs(first.root, second.root)
        self.assertEqual(first.path, second.path)
        self.assertEqual(len(first.parents), len(second.parents))
        for a, b in zip(first.parents, second.parents):
            self.assertIs(a.parent, b.parent)
            self.assertEqual(a.side, b.side)

    def assert_pointwise_equal(self, rows):
        results = []
        for old_compile, new_compile in COMPILERS:
            old, new = old_compile(rows), new_compile(rows)
            self.assertEqual(len(old.states), new.state_count)
            self.assertEqual(old.start, new.start)
            if isinstance(new, SuccinctWalkerTable):
                self.assertEqual(old.feedback, new.feedback)
                self.assertEqual(old.pass_bound, new.pass_bound)
                self.assertEqual(old.coefficient, new.coefficient)
            else:
                self.assertEqual(old.tick_bound, new.tick_bound)
            for control in range(new.state_count):
                self.assertIs(old.answer(control), new.answer(control))
                for observation in OBSERVATIONS:
                    entry = new.transition(control, *observation)
                    self.assertEqual(old.transition(control, *observation), entry)
                    self.assertIs(type(entry), Instruction)
                    self.assertIs(type(entry.command), str)
                    if entry.next_state is not None:
                        self.assertIs(type(entry.next_state), int)
                        self.assertLess(entry.next_state, new.state_count)
                        if isinstance(new, SuccinctWalkerTable) and control == new.feedback:
                            self.assertEqual(entry, Instruction("stay", new.start))
                        else:
                            self.assertLess(entry.next_state, control)
            results.append((old, new))
        return results

    def assert_trace(self, old, new, cursor):
        limit = (old.coefficient * (nodes(cursor.focus) if type(new.probe) is succinct_rows.SuccinctRowsTable
                                   else len(cursor.parents) + 1)
                 if isinstance(new, SuccinctWalkerTable) else old.tick_bound)
        a, b = Configuration(old.start, cursor), Configuration(new.start, cursor)
        for _ in range(limit + 1):
            self.assertEqual(a.control, b.control)
            self.assert_same_cursor(a.cursor, b.cursor)
            self.assertIs(old.answer(a.control), new.answer(b.control))
            if old.answer(a.control) is not None:
                self.assertIs(step(old, a), a)
                self.assertIs(step(new, b), b)
                return
            a, b = step(old, a), step(new, b)
        self.fail("trace exceeded the original static bound")

    def test_independent_literal_inverse_layout(self):
        table = compile_inverse_rows(((("S", "_"), (1,)),))
        expected = (
            (Instruction("false"), Instruction("false")),
            (Instruction("true"), Instruction("true")),
            (Instruction("R", 0), Instruction("R", 0)),
            (Instruction("U", 1), Instruction("U", 1)),
            (Instruction("U", 2), Instruction("U", 2)),
            (Instruction("R", 3), Instruction("R", 3)),
            (Instruction("U", 5), Instruction("U", 5)),
            (Instruction("stay", 6), Instruction("stay", 4)),
            (Instruction("L", 7), Instruction("L", 7)),
            (Instruction("stay", 2), Instruction("stay", 8)),
            (Instruction("U", 9), Instruction("U", 9)),
        )
        self.assertEqual((table.state_count, table.start, table.tick_bound), (12, 11, 8))
        for control, row in enumerate(expected):
            for kind, incoming in OBSERVATIONS:
                self.assertEqual(table.transition(control, kind, incoming),
                                 row[int(kind == "application")])
        for kind, incoming in OBSERVATIONS:
            self.assertEqual(table.transition(11, kind, incoming),
                             Instruction("stay", 10 if incoming == "R" else 0))
        deeper = compile_inverse_rows(((("_", ("_", "_")), (1, 0)),))
        for control, instruction in ((2, Instruction("L", 0)), (3, Instruction("R", 2)),
                                     (16, Instruction("U", 15)), (18, Instruction("U", 17))):
            self.assertEqual(deeper.transition(control, "S", "root"), instruction)
        self.assertEqual(deeper.transition(17, "S", "R"), Instruction("stay", 16))
        self.assertEqual(deeper.transition(17, "S", "root"), Instruction("stay", 2))
        self.assertEqual(deeper.transition(19, "S", "L"), Instruction("stay", 18))
        self.assertEqual(deeper.transition(19, "S", "R"), Instruction("stay", 0))

    def test_all_585_small_row_lists_and_all_64_three_leaf_rows(self):
        checked = 0
        for count in range(4):
            for rows in product(OPTIONS, repeat=count):
                self.assert_pointwise_equal(rows)
                checked += 1
        self.assertEqual(checked, 585)
        checked = 0
        for pattern in patterns(3):
            for address in addresses(pattern):
                self.assert_pointwise_equal(((pattern, address),))
                checked += 1
        self.assertEqual(checked, 64)

    def test_seeded_shared_dags_and_deeper_prioritized_families(self):
        rng = random.Random(423941)
        for _ in range(100):
            pool = ["_", "S"]
            for _ in range(7):
                pool.append((rng.choice(pool), rng.choice(pool)))
            rows = []
            for _ in range(rng.randrange(1, 6)):
                pattern = rng.choice(pool[2:])
                rows.append((pattern, rng.choice(tuple(addresses(pattern)))))
            self.assert_pointwise_equal(tuple(rows))

    def test_exact_profiles_are_graph_bounds_not_attainability_claims(self):
        for size in range(2, 5):
            for pattern in patterns(size):
                base = probes.compile_pattern(pattern)
                failure, success = graph_profiles(base)
                for address in addresses(pattern):
                    depth = len(address)
                    expected = (max(3 * depth - 2, 3 * depth + failure),
                                2 * depth + success)
                    old = walkers.compile_inverse_rows(((pattern, address),))
                    new = compile_inverse_rows(((pattern, address),))
                    self.assertEqual(graph_profiles(old), expected)
                    self.assertEqual(new.tick_bound, max(expected))
        rows = ((("_", "_"), (0,)),) * 2
        old = walkers.compile_inverse_rows(rows)
        table = compile_inverse_rows(rows)
        self.assertEqual((graph_profiles(old), table.tick_bound), ((8, 11), 11))
        actual_max = 0
        for size in range(1, 5):
            for term in trees(size):
                for cursor in cursors(term):
                    _, _, ticks = bounded_run(table, cursor, 11)
                    actual_max = max(actual_max, ticks)
        self.assertEqual(actual_max, 7)
        # Any L occurrence has an application parent, so the first row succeeds;
        # any other occurrence misses both incoming tests. Eleven is unattainable.

    def test_full_traces_for_10731_small_invocations(self):
        compiled = [self.assert_pointwise_equal(rows)
                    for count in range(3) for rows in product(OPTIONS, repeat=count)]
        checked = 0
        for size in range(1, 5):
            for term in trees(size):
                for cursor in cursors(term):
                    for family in compiled:
                        for old, new in family:
                            self.assert_trace(old, new, cursor)
                            checked += 1
        self.assertEqual(checked, 10731)

    def test_encoded_looking_trees_shared_occurrences_and_unchanged_execute(self):
        rows = ((("S", "_"), (1,)), ((("_", "_"), "_"), (0, 1)),
                (("_", ("_", "_")), (1, 0)))
        pairs = self.assert_pointwise_equal(rows)
        encoded = (C0, HALT, LIVE[0], LIVE[1], encode_word("101"), append_routine("01"))
        for term in encoded:
            ambient = App(term, term)
            for cursor in cursors(ambient):
                for old, new in pairs:
                    self.assert_trace(old, new, cursor)
                    first, second = execute(old, cursor), execute(new, cursor)
                    self.assertIs(first.answer, second.answer)
                    self.assert_same_cursor(first.cursor, second.cursor)

    def test_every_failed_ancestor_prefix_restores_exact_occurrence(self):
        pattern = ((("_", "_"), ("_", "_")), "S")
        old, new = self.assert_pointwise_equal(((pattern, (0, 1, 0)),))[0]
        deep = App(App(App(S, S), App(S, S)), App(S, S))
        ambient = App(deep, deep)
        for path in ((), (1,), (0,), (0, 0), (1, 0), (1, 1, 0), (0, 1, 0)):
            cursor = Cursor.at(ambient, path)
            self.assert_trace(old, new, cursor)
            answer, restored, _ = bounded_run(new, cursor, new.tick_bound)
            self.assertFalse(answer)
            self.assert_same_cursor(restored, cursor)
        rows = (((("_", "_"), ("_", "S")), (0, 1)), (("S", "S"), (1,)))
        ambient = App(App(S, S), App(S, App(S, S)))
        cursor = Cursor.at(ambient, (0, 1))
        result = execute(compile_inverse_rows(rows), cursor)
        self.assertTrue(result.answer)
        self.assert_same_cursor(result.cursor, Cursor.at(ambient, (0,)))

    def test_priority_and_overlapping_ancestor_limitations_are_unchanged(self):
        # A shadowed row remains a valid inverse candidate, not the selected edge.
        rows = ((("_", "_"), (0,)), (("_", "_"), (1,)))
        ambient = App(S, S)
        back = execute(compile_inverse_rows(rows), Cursor.at(ambient, (1,)))
        self.assertTrue(back.answer)
        again = execute(succinct_rows.compile_rows(rows), back.cursor)
        self.assertEqual(again.cursor.path, (0,))
        rows = ((("S", "_"), (1,)), ((("_", "_"), "_"), (0, 1)))
        ambient = App(App(S, S), S)
        down = execute(compile_descent(rows), Cursor.at(ambient))
        up = execute(compile_ascent(rows), down.cursor)
        self.assertEqual(down.cursor.path, (0, 1))
        self.assertEqual(up.cursor.path, (0,))
        # Prefix-overlapping addresses likewise provide no inverse boundary.
        rows = ((("_", "_"), (1,)), (("_", ("_", "_")), (1, 1)))
        ambient = App(S, App(S, S))
        original = Cursor.at(ambient, (1,))
        down = execute(compile_descent(rows), original)
        up = execute(compile_ascent(rows), down.cursor)
        self.assertEqual(down.cursor.path, (1, 1))
        self.assertEqual(up.cursor.path, ())

    def test_duplicate_identity_keeps_all_controls_and_no_source_objects(self):
        first, second = tuple(["S", "_"]), tuple(["S", "_"])
        rows = ((first, (0,)), (first, (1,)), (second, (0,)))
        with patch("s_only.succinct_walkers.compile_pattern", wraps=succinct_probes.compile_pattern) as build:
            table = compile_inverse_rows(rows)
        self.assertEqual(build.call_count, 2)
        self.assertEqual(len(table.patterns), 2)
        self.assertEqual([block.pattern for block in table.blocks], [1, 0, 0])
        self.assertEqual(table.state_count, 32)
        self.assert_pointwise_equal(rows)
        for block in table.blocks:
            self.assertLess(block.no, block.origin)

    def test_frozen_metadata_no_compiler_tree_hash_files_or_hidden_runtime_registers(self):
        rows = ((("S", "_"), (1,)), ((("_", "_"), "_"), (0,)))
        inverse, descent, ascent = (compile_inverse_rows(rows), compile_descent(rows), compile_ascent(rows))
        self.assertEqual([field.name for field in fields(inverse)], ["patterns", "blocks", "start", "ticks"])
        self.assertEqual([field.name for field in fields(descent)], ["probe"])
        self.assertEqual([field.name for field in fields(Configuration)], ["control", "cursor"])
        self.assertEqual([field.name for field in fields(Cursor)], ["focus", "parents"])
        for cls in (SuccinctInverseRowsTable, SuccinctWalkerTable):
            self.assertEqual(list(inspect.signature(cls.transition).parameters),
                             ["self", "control", "kind", "incoming"])
        for obj, field in ((inverse, "start"), (inverse.blocks[0], "no"),
                           (inverse.patterns[0], "failure_ticks"),
                           (inverse.patterns[0].probe, "root"), (ascent, "probe")):
            with self.assertRaises(FrozenInstanceError):
                setattr(obj, field, 0)
            self.assertFalse(hasattr(obj, "__dict__"))
        with self.assertRaises(TypeError):
            inverse.blocks[0].address[0] = 1
        before = tuple(repr(table) for table in (inverse, descent, ascent))
        ambient = App(S, App(S, S))
        curs = Cursor.at(ambient, (1, 1))
        forbidden = AssertionError("runtime source, compiler, tree equality, hash, or file access")
        with ExitStack() as stack:
            for target in (
                "s_only.probes.compile_rows", "s_only.probes.compile_pattern",
                "s_only.probes._Builder.match", "s_only.walkers._InverseBuilder.match",
                "s_only.walkers.compile_inverse_rows", "s_only.walkers.compile_descent",
                "s_only.walkers.compile_ascent", "s_only.succinct_walkers.compile_pattern",
                "s_only.succinct_walkers.compile_rows", "s_only.succinct_walkers._failure_ticks",
                "s_only.succinct_walkers._validate_selection", "s_only.succinct_rows.compile_pattern",
                "s_only.succinct_probes.compile_pattern", "s_only.terms.format_term",
                "s_only.terms.prefix", "builtins.open",
            ):
                stack.enter_context(patch(target, side_effect=forbidden))
            for cls in (App, type(S)):
                for name in ("__eq__", "__hash__"):
                    stack.enter_context(patch.object(cls, name, side_effect=forbidden))
            for _ in range(3):
                result = execute(inverse, curs)
                self.assertTrue(result.answer)
                self.assertEqual(result.cursor.path, (1,))
                self.assertEqual(execute(descent, Cursor.at(ambient)).cursor.path, (1, 1))
                self.assertEqual(execute(ascent, curs).cursor.path, ())
        self.assertEqual(tuple(repr(table) for table in (inverse, descent, ascent)), before)

    def test_code_bounded_search_and_matcher_iterations(self):
        rows = tuple((("S", ("_", "S")), (1, i % 2)) for i in range(37))
        table = compile_inverse_rows(rows)
        block_type, node_type = type(table.blocks[0]), type(table.patterns[0].probe.nodes[0])
        block_get, node_get = block_type.__getattribute__, node_type.__getattribute__
        counts = [0, 0]

        def block_read(block, name):
            if name == "origin":
                counts[0] += 1
            return block_get(block, name)

        def node_read(node, name):
            if name == "kind":
                counts[1] += 1
            return node_get(node, name)

        # Subtract non-search origin reads from the selected branch independently.
        extra = {}
        for block in table.blocks:
            depth = len(block.address)
            for q in range(block.origin, block.stop):
                branch_extra = 1  # pattern_origin
                if q < block.origin + depth:
                    branch_extra += 1  # restoration offset
                elif q >= block.stop - 2 * depth and (q - (block.stop - 2 * depth)) % 2:
                    index = (q - (block.stop - 2 * depth)) // 2
                    branch_extra += int(depth - index - 1 > 0)
                extra[q] = branch_extra
        with patch.object(block_type, "__getattribute__", block_read), \
             patch.object(node_type, "__getattribute__", node_read):
            for control in range(table.state_count):
                for observation in OBSERVATIONS:
                    counts[:] = [0, 0]
                    table.transition(control, *observation)
                    search = counts[0] - extra.get(control, 0)
                    self.assertLessEqual(search, table.block_lookup_bound)
                    self.assertLessEqual(counts[1], table.pattern_lookup_depth_bound)
                    self.assertLessEqual(search + counts[1], table.lookup_depth_bound)
                    self.assertGreaterEqual(search, int(control >= 2))
        many = compile_inverse_rows(((("_", "_"), (0,)),) * 4097)
        self.assertEqual(many.block_lookup_bound, 13)
        for block in (many.blocks[0], many.blocks[2048], many.blocks[-1]):
            self.assertEqual(many.transition(block.stop - 1, "S", "R"),
                             Instruction("stay", block.no))

    def test_huge_shared_virtual_code_uses_only_tiny_bounded_mismatches(self):
        depth = 4096
        pattern = "S"
        for _ in range(depth):
            pattern = (pattern, pattern)
        rows = ((pattern, (0,)), (pattern, (1,)))
        forbidden = AssertionError("materialized compiler invoked")
        with patch("s_only.probes.compile_rows", side_effect=forbidden), \
             patch("s_only.probes.compile_pattern", side_effect=forbidden), \
             patch("s_only.probes._Builder.match", side_effect=forbidden), \
             patch("s_only.walkers._InverseBuilder.match", side_effect=forbidden):
            inverse = compile_inverse_rows(rows)
            ascent, descent = compile_ascent(rows), compile_descent(rows)
        self.assertEqual(len(inverse.patterns), 1)
        self.assertEqual(len(inverse.patterns[0].probe.nodes), depth + 1)
        self.assertEqual(inverse.state_count, 14 * (1 << depth) - 4)
        self.assertEqual(inverse.tick_bound, 12 * (1 << depth) - 4)
        self.assertEqual(ascent.pass_bound, inverse.tick_bound)
        self.assertEqual(descent.state_count, 14 * (1 << depth) - 8)
        self.assertEqual(descent.pass_bound, 12 * (1 << depth) - 9)
        self.assertEqual(inverse.lookup_depth_bound, depth + 3)
        # First row in emitted order has a matcher origin 3. Its rightmost
        # leaf is at 3+2*depth; this lookup crosses every descriptor level.
        self.assertEqual(inverse.transition(3 + 2 * depth, "S", "R"),
                         Instruction("stay", 3 + 2 * (depth - 1)))
        ambient = App(S, S)
        for path, cap in (((), 2), ((0,), 8), ((1,), 8)):
            cursor = Cursor.at(ambient, path)
            for table in (inverse, ascent):
                answer, restored, ticks = bounded_run(table, cursor, cap)
                self.assertFalse(answer)
                self.assertEqual(ticks, cap)
                self.assert_same_cursor(restored, cursor)
        for focus, cap in ((S, 2), (ambient, 8)):
            answer, restored, ticks = bounded_run(descent, Cursor.at(focus), cap)
            self.assertFalse(answer)
            self.assertEqual(ticks, cap)
            self.assertIs(restored.focus, focus)
        with self.assertRaisesRegex(AssertionError, "external microtick"):
            bounded_run(ascent, Cursor.at(ambient, (0,)), 7)

    def test_deep_scoped_address_and_bad_deep_pattern_are_iterative(self):
        depth = 6000
        pattern = "_"
        for _ in range(depth):
            pattern = ("S", pattern)
        table = compile_inverse_rows(((pattern, (1,) * depth),))
        self.assertEqual(len(table.patterns[0].probe.nodes), depth + 2)
        self.assertEqual(table.state_count, 10 * depth + 2)
        self.assertEqual(table.tick_bound, 9 * depth - 2)
        answer, restored, ticks = bounded_run(table, Cursor.at(S), 1)
        self.assertFalse(answer)
        self.assertEqual(ticks, 1)
        self.assertIs(restored.focus, S)
        bad = []
        for _ in range(depth):
            bad = ("S", bad)
        with self.assertRaises(ValueError):
            compile_inverse_rows(((bad, (1,)),))

    def test_empty_lists_empty_addresses_invalid_syntax_and_plain_type_boundaries(self):
        class PoisonInt(int):
            def __eq__(self, other):
                raise AssertionError("custom equality")

        class PoisonTuple(tuple):
            def __len__(self):
                raise AssertionError("custom length")

        class PoisonStr(str):
            def __eq__(self, other):
                raise AssertionError("custom equality")
            def __hash__(self):
                raise AssertionError("custom hashing")

        for compiler in (compile_inverse_rows, compile_descent, compile_ascent):
            empty = compiler(())
            self.assertEqual((empty.state_count, empty.start), (2, 0))
            result, _, ticks = bounded_run(empty, Cursor.at(S), 0)
            self.assertFalse(result)
            self.assertEqual(ticks, 0)
            for rows in ((("_", ()),), ((("_", "_"), (0,)), ("S", ()))):
                with self.assertRaisesRegex(ValueError, "nonempty"):
                    compiler(rows)
            bad_rows = (None, [], (), ("S",), ("S", (), 1), PoisonTuple(("S", ())))
            for row in bad_rows:
                with self.assertRaises(ValueError):
                    compiler((row,))
            for address in ([], None, "", (True,), (2,), (-1,), (1.0,),
                            (PoisonInt(0),), PoisonTuple((0,))):
                with self.assertRaises(ValueError):
                    compiler(((("_", "_"), address),))
            for pattern in (PoisonStr("S"), PoisonTuple(("S", "_")), [], ("S", [])):
                with self.assertRaises(ValueError):
                    compiler(((pattern, (0,)),))
            for pattern, address in (("_", (0,)), ("S", (1,)), (("S", "_"), (1, 0))):
                with self.assertRaisesRegex(ValueError, "guaranteed"):
                    compiler(((pattern, address),))
            table = compiler(((("_", "_"), (0,)),))
            for control in (-1, table.state_count, True, None, 2.0, PoisonInt(2)):
                with self.assertRaises(ValueError):
                    table.answer(control)
                with self.assertRaises(ValueError):
                    table.transition(control, "S", "root")
            for kind, incoming in (("leaf", "L"), ("S", "U"), (None, "root"),
                                   (PoisonStr("S"), "root"), ("S", PoisonStr("L"))):
                for control in (0, 1, table.start):
                    with self.assertRaises(ValueError):
                        table.transition(control, kind, incoming)
        with self.assertRaisesRegex(ValueError, "empty feedback"):
            SuccinctWalkerTable(succinct_rows.compile_rows((("_", ()),)))

    def test_malformed_metadata_and_unused_indices_are_validated(self):
        table = compile_inverse_rows(((("S", "_"), (1,)),))
        block, code = table.blocks[0], table.patterns[0]
        for change in (
            {"patterns": list(table.patterns)}, {"blocks": list(table.blocks)},
            {"patterns": (None,)}, {"blocks": (None,)}, {"start": True},
            {"start": -1}, {"start": 1}, {"start": table.state_count},
            {"ticks": True}, {"ticks": -1}, {"ticks": table.ticks + 1},
        ):
            with self.assertRaises(ValueError):
                replace(table, **change)
        for change in (
            {"origin": True}, {"origin": 3}, {"stop": True}, {"stop": block.stop + 1},
            {"pattern": True}, {"pattern": 1}, {"no": True}, {"no": 1},
            {"no": table.state_count}, {"address": []}, {"address": ()},
            {"address": (True,)}, {"address": (1, 0)},
        ):
            with self.assertRaises(ValueError):
                replace(table, blocks=(replace(block, **change),))
        for failure in (None, True, -1, code.failure_ticks + 1):
            with self.assertRaises(ValueError):
                replace(table, patterns=(replace(code, failure_ticks=failure),))
        class BlockSubclass(type(block)):
            pass

        class CodeSubclass(type(code)):
            pass

        class ProbeSubclass(succinct_probes.SuccinctProbeTable):
            pass

        class InverseSubclass(SuccinctInverseRowsTable):
            pass

        with self.assertRaises(ValueError):
            replace(table, blocks=(BlockSubclass(block.origin, block.stop, block.pattern,
                                                block.address, block.no),))
        with self.assertRaises(ValueError):
            replace(table, patterns=(CodeSubclass(code.probe, code.failure_ticks),))
        with self.assertRaises(ValueError):
            replace(table, patterns=(replace(code, probe=ProbeSubclass(code.probe.nodes,
                                                                      code.probe.root)),))
        with self.assertRaises(ValueError):
            SuccinctWalkerTable(InverseSubclass(table.patterns, table.blocks,
                                                table.start, table.ticks))
        for probe in (None, succinct_probes.compile_pattern("S"), code):
            with self.assertRaises(ValueError):
                SuccinctWalkerTable(probe)
        # Unused valid metadata is allowed. Pattern and descriptor indices can
        # exceed the active virtual control range and need their own bit budget.
        hole = succinct_probes.compile_pattern("_")
        # The pair's children must be adjusted to the padded descriptor indices.
        shifted = tuple(replace(node, left=node.left + 1000, right=node.right + 1000)
                        if node.kind == "pair" else node for node in code.probe.nodes)
        padded = succinct_probes.SuccinctProbeTable((hole.nodes[0],) * 1000 + shifted,
                                                   1000 + code.probe.root)
        padded_code = replace(code, probe=padded)
        unused = succinct_rows._PatternCode(hole, None)
        expanded = replace(table, patterns=(unused,) * 1000 + (padded_code,),
                           blocks=(replace(block, pattern=1000),))
        self.assertGreater(len(expanded.patterns), expanded.state_count)
        self.assertGreater(len(padded.nodes), expanded.state_count)
        for q in range(table.state_count):
            for observation in OBSERVATIONS:
                self.assertEqual(expanded.transition(q, *observation), table.transition(q, *observation))
        with self.assertRaises(ValueError):
            replace(table, patterns=table.patterns + (replace(unused, failure_ticks=True),))
        # Revalidate forged nested code instead of trusting a frozen outer shell.
        broken = object.__new__(type(code.probe.nodes[0]))
        for field in fields(code.probe.nodes[0]):
            object.__setattr__(broken, field.name, getattr(code.probe.nodes[0], field.name))
        object.__setattr__(broken, "width", True)
        forged = object.__new__(succinct_probes.SuccinctProbeTable)
        object.__setattr__(forged, "nodes", (broken,))
        object.__setattr__(forged, "root", 0)
        with self.assertRaises(ValueError):
            replace(table, patterns=table.patterns + (replace(unused, probe=forged),))


if __name__ == "__main__":
    unittest.main()
