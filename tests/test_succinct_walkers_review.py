"""Independent adversarial review of exact succinct inverse/spine code.

Reference tables stay small. Huge virtual controls are queried at independently
calculated indices, and every execution uses a separate small microtick cap.
"""
from contextlib import ExitStack
from dataclasses import fields, is_dataclass, replace
import random
import unittest
from unittest.mock import patch

from s_only import probes, succinct_probes, succinct_rows, succinct_walkers, walkers
from s_only.probes import Configuration, Cursor, Instruction, OBSERVATIONS
from s_only.succinct_probes import SuccinctProbeTable
from s_only.succinct_walkers import (
    SuccinctInverseRowsTable, SuccinctWalkerTable,
    compile_ascent, compile_descent, compile_inverse_rows,
)
from s_only.terms import App, S


COMPILERS = ((walkers.compile_inverse_rows, compile_inverse_rows),
             (walkers.compile_descent, compile_descent),
             (walkers.compile_ascent, compile_ascent))


class PoisonInt(int):
    def __eq__(self, other):
        raise AssertionError("nonplain integer equality")

    def __lt__(self, other):
        raise AssertionError("nonplain integer ordering")


class PoisonStr(str):
    def __eq__(self, other):
        raise AssertionError("nonplain string equality")

    def __hash__(self):
        raise AssertionError("nonplain string hashing")


class PoisonTuple(tuple):
    def __len__(self):
        raise AssertionError("nonplain tuple length")

    def __iter__(self):
        raise AssertionError("nonplain tuple iteration")


def forged(cls, **values):
    instance = object.__new__(cls)
    for field, value in values.items():
        object.__setattr__(instance, field, value)
    return instance


def source_profiles(pattern):
    if type(pattern) is str:
        return (None, 0) if pattern == "_" else (1, 1)
    lf, ly = source_profiles(pattern[0])
    rf, ry = source_profiles(pattern[1])
    candidates = [1]
    if lf is not None:
        candidates.append(3 + lf)
    if rf is not None:
        candidates.append(5 + ly + rf)
    return max(candidates), 5 + ly + ry


def inverse_profiles(rows):
    failure, success = 0, None
    for pattern, address in reversed(rows):
        f, y = source_profiles(pattern)
        d = len(address)
        row_failure = max(3 * d - 2, 3 * d + f)
        success = max(2 * d + y,
                      row_failure + success if success is not None else 0)
        failure += row_failure
    return failure, success


def graph_profiles(table):
    values = []
    for row in table.states:
        if row[0].command == "false":
            values.append((0, None))
        elif row[0].command == "true":
            values.append((None, 0))
        else:
            values.append(tuple(max((1 + values[entry.next_state][exit_index]
                                     for entry in row
                                     if values[entry.next_state][exit_index] is not None),
                                    default=None) for exit_index in (0, 1)))
    return values[table.start]


def paths(pattern):
    result = []
    if type(pattern) is tuple:
        for side, child in enumerate(pattern):
            result.append((side,))
            result.extend((side,) + path for path in paths(child))
    return result


def branch(path, leaf=S, sibling=S):
    result = leaf
    for side in reversed(path):
        result = App(result, sibling) if side == 0 else App(sibling, result)
    return result


def pattern_branch(path):
    result = "_"
    for side in reversed(path):
        result = (result, "_") if side == 0 else ("_", result)
    return result


def bounded_trace(table, cursor, cap):
    configuration = Configuration(table.start, cursor)
    result = [configuration]
    for _ in range(cap):
        if table.answer(configuration.control) is not None:
            return result
        configuration = walkers.step(table, configuration)
        result.append(configuration)
    if table.answer(configuration.control) is None:
        raise AssertionError("independent execution cap exceeded")
    return result


class SuccinctWalkersReviewTests(unittest.TestCase):
    def assert_occurrence(self, actual, expected):
        self.assertIs(actual.focus, expected.focus)
        self.assertIs(actual.root, expected.root)
        self.assertEqual(actual.path, expected.path)
        self.assertEqual(len(actual.parents), len(expected.parents))
        for first, second in zip(actual.parents, expected.parents):
            self.assertIs(first.parent, second.parent)
            self.assertEqual(first.side, second.side)

    def assert_same_table(self, original, actual):
        self.assertEqual((len(original.states), original.start),
                         (actual.state_count, actual.start))
        controls = list(range(actual.state_count))
        random.Random(77912).shuffle(controls)
        for q in controls + controls[:5]:
            self.assertIs(actual.answer(q), original.answer(q))
            for observation in reversed(OBSERVATIONS):
                entry = actual.transition(q, *observation)
                self.assertEqual(entry, original.transition(q, *observation))
                self.assertIs(type(entry), Instruction)
                self.assertIs(type(entry.command), str)
                if entry.next_state is not None:
                    self.assertIs(type(entry.next_state), int)
                    self.assertTrue(0 <= entry.next_state < actual.state_count)
        if type(actual) is SuccinctWalkerTable:
            self.assertEqual((original.feedback, original.pass_bound, original.coefficient),
                             (actual.feedback, actual.pass_bound, actual.coefficient))
        else:
            self.assertEqual(original.tick_bound, actual.tick_bound)

    def test_asymmetric_longer_families_and_exit_specific_graph_profiles(self):
        rng = random.Random(934858)

        def pattern(leaves):
            if leaves == 1:
                return rng.choice(("_", "S"))
            cut = rng.randrange(1, leaves)
            return pattern(cut), pattern(leaves - cut)

        for _ in range(48):
            choices = [pattern(rng.randrange(3, 10)) for _ in range(4)]
            rows = tuple((item, rng.choice(paths(item)))
                         for item in rng.choices(choices, k=rng.randrange(2, 9)))
            original = walkers.compile_inverse_rows(rows)
            profiles = inverse_profiles(rows)
            self.assertEqual(graph_profiles(original), profiles)
            self.assertEqual(compile_inverse_rows(rows).tick_bound, max(profiles))
            for old, new in COMPILERS:
                self.assert_same_table(old(rows), new(rows))

    def test_all_inverse_interval_boundaries_at_huge_nonuniform_indices(self):
        depth = 128
        pattern = ("_", "S")
        for _ in range(depth):
            pattern = (pattern, pattern)
        first = (0, 1, 1, 0, 1) * 17
        second = (1, 0, 0, 1) * 23
        rows = ((pattern, first), (("S", "_"), (1,)), (pattern, second))
        table = compile_inverse_rows(rows)
        width = 13 * (1 << depth) - 6
        emitted = ((pattern, second, width), (("S", "_"), (1,), 7),
                   (pattern, first, width))
        origin, remaining = 2, 0
        for source, address, w in emitted:
            d = len(address)
            m, t = origin + d, origin + d + w
            for j, side in enumerate(reversed(address)):
                expected = Instruction("L" if side == 0 else "R",
                                       remaining if j == 0 else origin + j - 1)
                for observation in OBSERVATIONS:
                    self.assertEqual(table.transition(origin + j, *observation), expected)
            for i, side in enumerate(address):
                restored = d - i - 1
                failure = remaining if restored == 0 else origin + restored - 1
                for kind, incoming in OBSERVATIONS:
                    self.assertEqual(table.transition(t + 2 * i, kind, incoming),
                                     Instruction("U", t + 2 * i - 1))
                    self.assertEqual(table.transition(t + 2 * i + 1, kind, incoming),
                                     Instruction("stay", t + 2 * i if incoming == "LR"[side]
                                                 else failure))
            if source is pattern:
                for path in ((0,) * depth, (1,) * depth,
                             tuple(index % 2 for index in range(depth))):
                    base, yes, no = m, 1, m - 1
                    for level, side in enumerate(path):
                        child_width = 13 * (1 << (depth - level - 1)) - 6
                        right_move = base + child_width + 2
                        left_move = base + 2 * child_width + 4
                        expected = {
                            base: (Instruction("U", yes),) * 2,
                            base + 1: (Instruction("U", no),) * 2,
                            right_move: (Instruction("R", right_move - 1),) * 2,
                            right_move + 1: (Instruction("U", right_move),) * 2,
                            left_move: (Instruction("L", left_move - 1),) * 2,
                            left_move + 1: (Instruction("stay", no),
                                           Instruction("stay", left_move)),
                        }
                        for q, entries in expected.items():
                            for kind, incoming in OBSERVATIONS:
                                self.assertEqual(table.transition(q, kind, incoming),
                                                 entries[kind == "application"])
                        if side == 0:
                            base, yes, no = right_move + 2, right_move + 1, base + 1
                        else:
                            base, yes, no = base + 2, base, base + 1
                    for kind, incoming in OBSERVATIONS:
                        self.assertEqual(table.transition(base + 2, kind, incoming),
                                         Instruction("stay", base if kind == "S" else base + 1))
                        self.assertEqual(table.transition(base + 6, kind, incoming),
                                         Instruction("stay", no if kind == "S" else base + 5))
            remaining, origin = t + 2 * d - 1, t + 2 * d
        self.assertEqual((table.state_count, table.start), (origin, remaining))
        self.assertGreater(table.state_count.bit_length(), 128)
        # Every root incoming test misses; the huge static bound is not fuel.
        trace = bounded_trace(table, Cursor.at(S), 3)
        self.assertEqual(len(trace) - 1, 3)
        self.assertFalse(table.answer(trace[-1].control))

    def test_every_side_miss_restores_before_fallback_at_root_and_wrong_side(self):
        address = (0, 1, 1, 0, 1, 0, 1)
        pattern = pattern_branch(address)
        for completed in range(len(address)):
            suffix = address[len(address) - completed:] if completed else ()
            wrong_side = 1 - address[len(address) - completed - 1]
            for path in (suffix, (wrong_side,) + suffix):
                ambient = branch(path)
                cursor = Cursor.at(ambient, path)
                rows = ((pattern, address),)
                old, new = walkers.compile_inverse_rows(rows), compile_inverse_rows(rows)
                a, b = bounded_trace(old, cursor, 3 * completed + 1), bounded_trace(new, cursor, 3 * completed + 1)
                self.assertEqual(len(a), 3 * completed + 2)
                self.assertEqual([item.control for item in a], [item.control for item in b])
                for first, second in zip(a, b):
                    self.assert_occurrence(first.cursor, second.cursor)
                self.assertFalse(new.answer(b[-1].control))
                self.assert_occurrence(b[-1].cursor, cursor)
                if path:
                    fallback = (("_", "_"), (path[-1],))
                    family = compile_inverse_rows(rows + (fallback,))
                    trace = bounded_trace(family, cursor, 3 * completed + 8)
                    fallback_entry = family.blocks[0].stop - 1
                    entries = [item.cursor for item in trace if item.control == fallback_entry]
                    self.assertEqual(len(entries), 1)
                    self.assert_occurrence(entries[0], cursor)
                    self.assertTrue(family.answer(trace[-1].control))
                    self.assert_occurrence(trace[-1].cursor, Cursor.at(ambient, path[:-1]))

    def test_late_matcher_failure_restores_all_edges_before_a_different_candidate(self):
        address = (0, 1, 0, 1, 1)
        pattern = (pattern_branch(address[1:]), "S")
        candidate = branch(address, sibling=S)
        ambient = App(candidate.left, App(S, S))
        cursor = Cursor.at(ambient, address)
        rows = ((pattern, address), (("_", "_"), (1,)))
        old, new = walkers.compile_inverse_rows(rows), compile_inverse_rows(rows)
        a, b = bounded_trace(old, cursor, 100), bounded_trace(new, cursor, 100)
        self.assertEqual([item.control for item in a], [item.control for item in b])
        for first, second in zip(a, b):
            self.assert_occurrence(first.cursor, second.cursor)
        second_start = new.blocks[0].stop - 1
        fallback = [item.cursor for item in b if item.control == second_start]
        self.assertEqual(len(fallback), 1)
        self.assert_occurrence(fallback[0], cursor)
        self.assertTrue(new.answer(b[-1].control))
        self.assert_occurrence(b[-1].cursor, Cursor.at(ambient, address[:-1]))

    def test_empty_families_keep_the_unused_boolean_feedback_and_absorb_false(self):
        for old, new in COMPILERS:
            table = new(())
            self.assert_same_table(old(()), table)
            cursor = Cursor.at(App(S, S), (1,))
            config = Configuration(0, cursor)
            self.assertIs(walkers.step(table, config), config)
            if type(table) is SuccinctWalkerTable:
                self.assertEqual((table.feedback, table.pass_bound, table.coefficient), (1, 0, 1))
                self.assertIsNone(table.answer(1))
                for observation in OBSERVATIONS:
                    self.assertEqual(table.transition(1, *observation), Instruction("stay", 0))
                resumed = walkers.step(table, Configuration(1, cursor))
                self.assertEqual(resumed.control, 0)
                self.assertIs(resumed.cursor, cursor)
                self.assertIs(walkers.step(table, resumed), resumed)
            else:
                self.assertTrue(table.answer(1))
                true = Configuration(1, cursor)
                self.assertIs(walkers.step(table, true), true)

    def test_large_unused_counts_and_indices_never_enter_active_lookup(self):
        seed = compile_inverse_rows(((("_", "_"), (1,)),))
        code = seed.patterns[0]
        node_type = type(code.probe.nodes[0])
        nodes = [node_type("S", None, None, 1, 1, 1)]
        for index in range(160):
            last = nodes[-1]
            nodes.append(node_type("pair", index, index, 6 + 2 * last.width,
                                   5 + 2 * last.ticks, last.height + 1))
        unused_ids = {id(node) for node in nodes}
        nodes.extend(node_type("_", None, None, 0, 0, 1) for _ in range(1500))
        child = len(nodes) - 1
        nodes.append(node_type("pair", child, child, 6, 5, 2))
        probe = SuccinctProbeTable(tuple(nodes), len(nodes) - 1)
        active = replace(code, probe=probe)
        unused = succinct_rows._PatternCode(succinct_probes.compile_pattern("S"), 1)
        table = replace(seed, patterns=(unused,) * 3000 + (active,),
                        blocks=(replace(seed.blocks[0], pattern=3000),))
        wrapper = SuccinctWalkerTable(table)
        self.assertEqual((table.state_count, table.tick_bound, table.lookup_depth_bound), (11, 7, 3))
        original_get = node_type.__getattribute__

        def guarded(node, name):
            if id(node) in unused_ids:
                raise AssertionError("unused huge metadata read at runtime")
            return original_get(node, name)

        with patch.object(node_type, "__getattribute__", guarded):
            self.assert_same_table(walkers.compile_inverse_rows(((("_", "_"), (1,)),)), table)
            self.assert_same_table(walkers.compile_ascent(((("_", "_"), (1,)),)), wrapper)
        self.assertGreater(probe.root.bit_length(), table.state_count.bit_length())
        self.assertGreater(table.blocks[0].pattern.bit_length(), table.state_count.bit_length())

    def test_wrapper_revalidates_forged_rows_and_unused_nested_child_metadata(self):
        rows = (((("S", "_"), "S"), (0, 1)),)
        for compile_probe in (compile_inverse_rows, succinct_rows.compile_rows):
            seed = compile_probe(rows)
            values = {field.name: getattr(seed, field.name) for field in fields(seed)}
            changes = [{"start": True}, {"ticks": seed.ticks + 1},
                       {"blocks": list(seed.blocks)},
                       {"blocks": (replace(seed.blocks[0], no=seed.state_count),)}]
            code = seed.patterns[0]
            nodes, root = code.probe.nodes, code.probe.root
            for index, node in enumerate(nodes):
                corruptions = [{"kind": PoisonStr(node.kind)}, {"width": True},
                               {"ticks": PoisonInt(node.ticks)}, {"height": -1}]
                if node.kind == "pair":
                    corruptions += [{"left": index}, {"right": root + 1}, {"left": -1}]
                else:
                    corruptions += [{"left": 0}, {"right": True}]
                for change in corruptions:
                    bad_nodes = nodes[:index] + (replace(node, **change),) + nodes[index + 1:]
                    bad_probe = forged(SuccinctProbeTable, nodes=bad_nodes, root=root)
                    unused = replace(code, probe=bad_probe)
                    changes.append({"patterns": seed.patterns + (unused,)})
            for failure in (True, PoisonInt(1), -1, None, code.failure_ticks + 1):
                changes.append({"patterns": seed.patterns + (replace(code, failure_ticks=failure),)})
            for change in changes:
                with self.subTest(type=type(seed).__name__, change=tuple(change)):
                    with self.assertRaises(ValueError):
                        SuccinctWalkerTable(forged(type(seed), **dict(values, **change)))

    def test_all_inverse_primitive_fields_and_illegal_continuations_rejected(self):
        table = compile_inverse_rows(((("S", "_"), (1,)), (("_", "S"), (0,))))
        for field in ("start", "ticks"):
            for value in (True, False, PoisonInt(0), 0.0, "0", None, [], -1):
                with self.assertRaises(ValueError):
                    replace(table, **{field: value})
        for i, block in enumerate(table.blocks):
            for field in ("origin", "stop", "pattern", "no"):
                for value in (True, PoisonInt(0), 0.0, "0", None, [], -1, 1 << 10000):
                    altered = table.blocks[:i] + (replace(block, **{field: value}),) + table.blocks[i + 1:]
                    with self.assertRaises(ValueError):
                        replace(table, blocks=altered)
            for changes in ({"no": 1}, {"no": block.origin}, {"no": block.stop - 1},
                            {"origin": block.origin + 1}, {"stop": block.stop - 1},
                            {"address": ()}, {"address": PoisonTuple((1,))},
                            {"address": (PoisonInt(1),)}, {"address": (True,)}):
                altered = table.blocks[:i] + (replace(block, **changes),) + table.blocks[i + 1:]
                with self.assertRaises(ValueError):
                    replace(table, blocks=altered)
        for field in ("patterns", "blocks"):
            with self.assertRaises(ValueError):
                replace(table, **{field: PoisonTuple(getattr(table, field))})
        for blocks in (table.blocks[::-1], table.blocks[1:], table.blocks + table.blocks):
            with self.assertRaises(ValueError):
                replace(table, blocks=blocks)
        for compiler in (compile_inverse_rows, compile_ascent, compile_descent):
            instance = compiler(((("_", "_"), (0,)),))
            for q in (0, 1, instance.start):
                for observation in ((PoisonStr("S"), "root"), ("S", PoisonStr("L"))):
                    with self.assertRaises(ValueError):
                        instance.transition(q, *observation)
            for q in (PoisonInt(0), True, 1 << 10000, -1):
                with self.assertRaises(ValueError):
                    instance.answer(q)
                with self.assertRaises(ValueError):
                    instance.transition(q, "S", "root")

    def test_lookup_and_unchanged_runtime_do_not_use_sources_compilers_or_cursor_helpers(self):
        rows = (((("S", "_"), "_"), (0, 1)), (("_", "_"), (1,)))
        tables = [compiler(rows) for compiler in (compile_inverse_rows, compile_descent, compile_ascent)]
        expected = [[(q, obs, table.transition(q, *obs)) for q in range(table.state_count)
                     for obs in OBSERVATIONS] for table in tables]
        with ExitStack() as stack:
            for name in ("builtins.open", "builtins.hash", "builtins.id",
                         "s_only.succinct_walkers.compile_pattern", "s_only.succinct_walkers.compile_rows",
                         "s_only.succinct_walkers._validate_selection", "s_only.succinct_walkers._failure_ticks",
                         "s_only.succinct_rows._failure_ticks", "s_only.succinct_probes.compile_pattern"):
                stack.enter_context(patch(name, side_effect=AssertionError(name)))
            stack.enter_context(patch.object(Cursor, "__getattribute__", side_effect=AssertionError("cursor access")))
            stack.enter_context(patch.object(App, "__getattribute__", side_effect=AssertionError("term access")))
            for table, queries in zip(tables, expected):
                for q, observation, instruction in list(reversed(queries)) + queries:
                    self.assertEqual(table.transition(q, *observation), instruction)
        ambient = App(App(S, S), App(S, S))
        cursor = Cursor.at(ambient, (0, 1))
        results = [walkers.execute(table, cursor) for table in tables]
        with ExitStack() as stack:
            for name in ("path", "root"):
                stack.enter_context(patch.object(Cursor, name, property(lambda _: (_ for _ in ()).throw(
                    AssertionError("cursor helper accessed")))))
            stack.enter_context(patch("s_only.succinct_walkers._inverse_bound", side_effect=AssertionError("bound at runtime")))
            for table, expected_result in zip(tables, results):
                result = walkers.execute(table, cursor)
                self.assertIs(result.answer, expected_result.answer)
                self.assertIs(result.cursor.focus, expected_result.cursor.focus)
                self.assertEqual([(id(frame.parent), frame.side) for frame in result.cursor.parents],
                                 [(id(frame.parent), frame.side) for frame in expected_result.cursor.parents])

    def test_retained_code_contains_only_immutable_fields_and_fixed_source_addresses(self):
        shared = tuple(["S", "_"])
        other = tuple([shared, shared])
        address = tuple([0, 1])
        source_rows = [(other, address), (shared, (1,))]
        original_ids = {id(source_rows), id(source_rows[0]), id(source_rows[1]), id(shared), id(other)}
        table = compile_inverse_rows(iter(source_rows))
        self.assertIs(table.blocks[-1].address, address)
        pending = [table]
        while pending:
            value = pending.pop()
            self.assertNotIn(id(value), original_ids)
            if type(value) is tuple:
                pending.extend(value)
            elif is_dataclass(value):
                self.assertTrue(type(value).__dataclass_params__.frozen)
                self.assertFalse(hasattr(value, "__dict__"))
                pending.extend(getattr(value, field.name) for field in fields(value))
            else:
                self.assertIn(type(value), (str, int, type(None)))
        original = walkers.compile_inverse_rows(source_rows)
        source_rows[:] = [("_", ())]
        self.assert_same_table(original, table)


if __name__ == "__main__":
    unittest.main()
