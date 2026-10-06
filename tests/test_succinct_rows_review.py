"""Independent adversarial review of exact succinct prioritized-row code.

Only small reference tables are materialized. Exponential cases query sparse,
independently indexed controls and run tiny mismatching inputs under fixed caps.
"""
from contextlib import ExitStack
from dataclasses import replace
import random
import unittest
from unittest.mock import patch

from s_only import probes
from s_only.probes import Configuration, Cursor, Instruction, OBSERVATIONS
from s_only.succinct_probes import SuccinctProbeTable
from s_only.succinct_rows import SuccinctRowsTable, compile_rows
from s_only.terms import App, S


class PoisonInt(int):
    def __eq__(self, other):
        raise AssertionError("untrusted integer comparison")

    def __lt__(self, other):
        raise AssertionError("untrusted integer comparison")


class PoisonStr(str):
    def __eq__(self, other):
        raise AssertionError("untrusted string comparison")

    def __hash__(self):
        raise AssertionError("untrusted string hash")


class PoisonTuple(tuple):
    def __iter__(self):
        raise AssertionError("untrusted tuple iteration")

    def __len__(self):
        raise AssertionError("untrusted tuple length")


def source_profiles(pattern):
    """Independent source recurrence: longest paths to false and true exits."""
    if pattern == "_":
        return None, 0
    if pattern == "S":
        return 1, 1
    left_failure, left_success = source_profiles(pattern[0])
    right_failure, right_success = source_profiles(pattern[1])
    failure_paths = [1]
    if left_failure is not None:
        failure_paths.append(3 + left_failure)
    if right_failure is not None:
        failure_paths.append(5 + left_success + right_failure)
    return max(failure_paths), 5 + left_success + right_success


def row_profiles(rows):
    """Compose each distinct exit before taking a longest-path maximum."""
    failure, success = 0, None
    for pattern, address in reversed(rows):
        row_failure, row_success = source_profiles(pattern)
        success_paths = [row_success + len(address)]
        if row_failure is not None and success is not None:
            success_paths.append(row_failure + success)
        failure = None if row_failure is None or failure is None else row_failure + failure
        success = max(success_paths)
    return failure, success


def graph_profiles(table):
    profiles = []
    for state, row in enumerate(table.states):
        if row[0].command == "false":
            profiles.append((0, None))
        elif row[0].command == "true":
            profiles.append((None, 0))
        else:
            exits = []
            for terminal in (0, 1):
                candidates = [profiles[instruction.next_state][terminal] for instruction in row]
                exits.append(max((value + 1 for value in candidates if value is not None),
                                 default=None))
            profiles.append(tuple(exits))
    return profiles[table.start]


def scoped_addresses(pattern):
    result = [()]
    if type(pattern) is tuple:
        for side in (0, 1):
            result.extend((side,) + path for path in scoped_addresses(pattern[side]))
    return result


def bounded_run(table, cursor, limit):
    configuration = Configuration(table.start, cursor)
    for ticks in range(limit + 1):
        answer = table.answer(configuration.control)
        if answer is not None:
            return answer, configuration.cursor, ticks
        if ticks < limit:
            configuration = probes.step(table, configuration)
    raise AssertionError("independent tick cap exceeded")


def forged_probe(nodes, root):
    """Bypass the inner constructor to test the outer defensive validation."""
    probe = object.__new__(SuccinctProbeTable)
    object.__setattr__(probe, "nodes", nodes)
    object.__setattr__(probe, "root", root)
    return probe


class SuccinctRowsReviewTests(unittest.TestCase):
    def assert_pointwise_equal(self, rows, table=None):
        reference = probes.compile_rows(rows)
        table = compile_rows(rows) if table is None else table
        self.assertEqual((table.state_count, table.start, table.tick_bound),
                         (len(reference.states), reference.start, reference.tick_bound))
        expected_profiles = row_profiles(rows)
        self.assertEqual(graph_profiles(reference), expected_profiles)
        self.assertEqual(table.tick_bound,
                         max(value for value in expected_profiles if value is not None))
        # Nonmonotone, repeated queries expose accidental history dependence.
        controls = list(range(table.state_count))
        random.Random(32451).shuffle(controls)
        for control in controls + controls[-4:]:
            self.assertIs(table.answer(control), reference.answer(control))
            for observation in reversed(OBSERVATIONS):
                actual = table.transition(control, *observation)
                self.assertEqual(actual, reference.transition(control, *observation))
                if actual.next_state is not None:
                    self.assertIs(type(actual.next_state), int)
                    self.assertGreaterEqual(actual.next_state, 0)
                    self.assertLess(actual.next_state, control)
        return table

    def test_asymmetric_deep_addresses_and_terminal_specific_profiles(self):
        rng = random.Random(82019)

        def make_pattern(leaves):
            if leaves == 1:
                return rng.choice(("_", "S"))
            split = rng.randrange(1, leaves)
            return make_pattern(split), make_pattern(leaves - split)

        for _ in range(80):
            patterns = [make_pattern(rng.randrange(3, 8)) for _ in range(5)]
            rows = [(pattern, rng.choice(scoped_addresses(pattern)))
                    for pattern in rng.choices(patterns, k=rng.randrange(3, 10))]
            if rng.randrange(2):
                rows.insert(rng.randrange(len(rows) + 1), ("_", ()))
            self.assert_pointwise_equal(tuple(rows))
            for pattern in patterns:
                self.assertEqual(source_profiles(pattern),
                                 graph_profiles(probes.compile_pattern(pattern)))

    def test_priority_obstructions_make_graph_bound_unattainable(self):
        rows = ((("_", "_"), ()), (("S", "_"), ()))
        table = self.assert_pointwise_equal(rows)
        self.assertEqual(row_profiles(rows), (5, 7))
        self.assertEqual(table.tick_bound, 7)
        # These two cases exhaust the root observation, regardless of subtree size.
        for focus, expected in ((S, (False, 2)),
                                (App(S, S), (True, 5)),
                                (App(App(S, S), App(S, S)), (True, 5))):
            ambient = App(focus, focus)
            for path in ((0,), (1,)):
                cursor = Cursor.at(ambient, path)
                answer, result, ticks = bounded_run(table, cursor, 5)
                self.assertEqual((answer, ticks), expected)
                self.assertIs(result.focus, focus)
                self.assertIs(result.root, ambient)
                self.assertEqual(result.path, path)

    def test_multiple_wildcard_cuts_preserve_all_unreachable_controls(self):
        p = (("S", "_"), ("_", ("S", "_")))
        q = (p, "_")
        rows = (("_", ()), (p, (1, 1, 0)), ("_", ()), (q, (0, 0, 1)),
                ("_", ()), ("_", ()), (p, (0,)), ("S", ()))
        table = self.assert_pointwise_equal(rows)
        self.assertEqual((table.start, table.tick_bound), (1, 0))
        self.assertEqual(len(table.blocks), 4)
        self.assertGreater(table.state_count, 80)
        self.assertEqual([block.no for block in table.blocks], [0, 2, 1, 1])
        for focus in (S, App(S, S)):
            cursor = Cursor.at(focus)
            result = probes.execute(table, cursor)
            self.assertTrue(result.answer)
            self.assertIs(result.cursor, cursor)

    def test_public_code_can_have_large_unused_indices_and_tiny_control_range(self):
        seed = compile_rows((("S", ()),))
        code_type = type(seed.patterns[0])
        descriptor = seed.patterns[0].probe.nodes[0]
        # Reachable root index has ten bits despite only three virtual controls.
        probe = SuccinctProbeTable((descriptor,) * 1025, 1024)
        used = code_type(probe, 1)
        unused = compile_rows((("_", ()),)).patterns[0]
        codes = (unused,) * 2048 + (used,) + (unused,) * 3
        block = replace(seed.blocks[0], pattern=2048)
        table = SuccinctRowsTable(codes, (block,), 2, 1)
        self.assert_pointwise_equal((("S", ()),), table)
        self.assertEqual(table.lookup_depth_bound, 2)
        self.assertGreater(table.blocks[0].pattern.bit_length(), table.state_count.bit_length())
        self.assertGreater(probe.root.bit_length(), table.state_count.bit_length())
        empty = SuccinctRowsTable(codes, (), 0, 0)
        true = SuccinctRowsTable(codes, (), 1, 0)
        self.assertEqual((empty.state_count, true.state_count), (2, 2))
        for observation in OBSERVATIONS:
            self.assertEqual(empty.transition(0, *observation), Instruction("false"))
            self.assertEqual(true.transition(1, *observation), Instruction("true"))

    def test_unused_large_counters_do_not_enlarge_active_lookup_integers(self):
        seed = compile_rows((("S", ()),))
        code_type = type(seed.patterns[0])
        descriptor_type = type(seed.patterns[0].probe.nodes[0])
        nodes = [descriptor_type("S", None, None, 1, 1, 1)]
        for index in range(128):
            previous = nodes[-1]
            nodes.append(descriptor_type("pair", index, index,
                                         6 + 2 * previous.width,
                                         5 + 2 * previous.ticks, previous.height + 1))
        # A root literal leaves the large, valid DAG unreachable in static code.
        nodes.append(descriptor_type("S", None, None, 1, 1, 1))
        probe = SuccinctProbeTable(tuple(nodes), len(nodes) - 1)
        self.assertGreater(nodes[-2].width.bit_length(), 128)
        self.assertEqual((probe.state_count, probe.lookup_depth_bound), (3, 1))
        table = replace(seed, patterns=(code_type(probe, 1),))
        self.assert_pointwise_equal((("S", ()),), table)
        self.assertEqual(table.lookup_depth_bound, 2)

    def test_outer_constructor_revalidates_even_unused_pattern_children(self):
        seed = compile_rows((((("S", "_"), "S"), ()),))
        code = seed.patterns[0]
        root, nodes = code.probe.root, code.probe.nodes
        corruptions = [(list(nodes), root), (PoisonTuple(nodes), root),
                       (nodes, True), (nodes, PoisonInt(root)), (nodes, root - 1)]
        for index, node in enumerate(nodes):
            changes = [{"kind": PoisonStr(node.kind)}, {"width": True},
                       {"ticks": PoisonInt(node.ticks)}, {"height": node.height + 1}]
            if node.kind == "pair":
                changes += [{"left": index}, {"right": -1}, {"left": PoisonInt(0)}]
            else:
                changes += [{"left": 0}, {"right": True}]
            for change in changes:
                corruptions.append((nodes[:index] + (replace(node, **change),) + nodes[index + 1:], root))
        for bad_nodes, bad_root in corruptions:
            with self.subTest(root_type=type(bad_root), nodes_type=type(bad_nodes)):
                poisoned = replace(code, probe=forged_probe(bad_nodes, bad_root))
                with self.assertRaises(ValueError):
                    SuccinctRowsTable((poisoned,), (), 0, 0)
        for failure in (True, PoisonInt(1), -1, "1", 1.0, None, code.failure_ticks + 1):
            with self.assertRaises(ValueError):
                SuccinctRowsTable((replace(code, failure_ticks=failure),), (), 0, 0)

    def test_all_outer_integer_fields_reject_nonplain_values_before_hooks(self):
        table = compile_rows(((("S", "_"), (1,)), ("S", ())))
        for field in ("start", "ticks"):
            for value in (True, False, PoisonInt(0), 0.0, "0", None, []):
                with self.assertRaises(ValueError):
                    replace(table, **{field: value})
        for block_index, block in enumerate(table.blocks):
            for field in ("origin", "stop", "pattern", "no"):
                for value in (True, False, PoisonInt(0), 0.0, "0", None, [], -1):
                    blocks = (table.blocks[:block_index] + (replace(block, **{field: value}),)
                              + table.blocks[block_index + 1:])
                    with self.assertRaises(ValueError):
                        replace(table, blocks=blocks)
            for address in (PoisonTuple(()), (PoisonInt(0),), (False,), [1], None):
                blocks = (table.blocks[:block_index] + (replace(block, address=address),)
                          + table.blocks[block_index + 1:])
                with self.assertRaises(ValueError):
                    replace(table, blocks=blocks)
        for field in ("patterns", "blocks"):
            with self.assertRaises(ValueError):
                replace(table, **{field: PoisonTuple(getattr(table, field))})

    def test_interval_gaps_overlap_reordering_and_illegal_fallthrough_are_rejected(self):
        table = compile_rows(((("S", "_"), (1,)), (("_", "S"), (0,)), ("S", ())))
        for index, block in enumerate(table.blocks):
            for change in ({"origin": block.origin + 1}, {"origin": block.origin - 1},
                           {"stop": block.stop + 1}, {"stop": block.stop - 1},
                           {"no": block.origin}, {"no": block.stop - 1},
                           {"no": table.state_count}, {"pattern": len(table.patterns)}):
                blocks = table.blocks[:index] + (replace(block, **change),) + table.blocks[index + 1:]
                with self.assertRaises(ValueError):
                    replace(table, blocks=blocks)
        with self.assertRaises(ValueError):
            replace(table, blocks=tuple(reversed(table.blocks)))
        # A preceding fragment's interior is not a legal row entry.
        block = table.blocks[-1]
        with self.assertRaises(ValueError):
            replace(table, blocks=table.blocks[:-1] + (replace(block, no=block.origin - 2),))
        for start in (0, 2, table.state_count - 2, table.state_count):
            with self.assertRaises(ValueError):
                replace(table, start=start)
        # A wildcard may reset the start and bound while retaining every interval.
        terminal = replace(table, start=1, ticks=0)
        self.assertEqual(terminal.state_count, table.state_count)

    def test_huge_mixed_rows_sparse_independent_indices_and_reversed_addresses(self):
        depth = 128
        pattern = ("_", "S")
        for _ in range(depth):
            pattern = (pattern, pattern)
        a = (1, 0, 1, 1, 0) * 20
        b = (0, 1, 0) * 30
        rows = (("S", ()), ("_", ()), (pattern, a), (pattern, b), ("S", ()))
        table = compile_rows(rows)
        width = 13 * (1 << depth) - 6
        self.assertEqual(table.state_count, 4 + 2 * width + len(a) + len(b))
        self.assertEqual((table.start, table.tick_bound), (table.state_count - 1, 1))
        self.assertEqual(len(table.patterns), 3)
        self.assertEqual(len(table.blocks), 4)
        origins = (3, 3 + width + len(b))
        previous = 2
        for origin, address in zip(origins, (b, a)):
            for offset, side in enumerate(reversed(address)):
                expected = Instruction("L" if side == 0 else "R", 1 if offset == 0 else origin + offset - 1)
                for observation in OBSERVATIONS:
                    self.assertEqual(table.transition(origin + offset, *observation), expected)
            pattern_origin = origin + len(address)
            paths = ((0,) * depth, (1,) * depth, tuple(i % 2 for i in range(depth)))
            for path in paths:
                base, yes, no = pattern_origin, pattern_origin - 1, previous
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
                        left_move + 1: (Instruction("stay", no), Instruction("stay", left_move)),
                    }
                    for control, instructions in expected.items():
                        for kind, incoming in OBSERVATIONS:
                            self.assertEqual(table.transition(control, kind, incoming),
                                             instructions[kind == "application"])
                    if side == 0:
                        base, yes, no = right_move + 2, right_move + 1, base + 1
                    else:
                        base, yes, no = base + 2, base, base + 1
                expected = {
                    base: (Instruction("U", yes),) * 2,
                    base + 1: (Instruction("U", no),) * 2,
                    base + 2: (Instruction("stay", base), Instruction("stay", base + 1)),
                    base + 3: (Instruction("R", base + 2),) * 2,
                    base + 4: (Instruction("U", base + 3),) * 2,
                    base + 5: (Instruction("L", base + 4),) * 2,
                    base + 6: (Instruction("stay", no), Instruction("stay", base + 5)),
                }
                for control, instructions in expected.items():
                    for kind, incoming in OBSERVATIONS:
                        self.assertEqual(table.transition(control, kind, incoming),
                                         instructions[kind == "application"])
            previous = origin + len(address) + width - 1
        # Remove the leading reset to exercise both giant rows on tiny failures.
        failures = compile_rows(((pattern, a), (pattern, b)))
        for focus, limit in ((S, 2), (App(S, S), 8)):
            cursor = Cursor.at(App(focus, focus), (1,))
            answer, restored, ticks = bounded_run(failures, cursor, limit)
            self.assertEqual((answer, ticks), (False, limit))
            self.assertIs(restored.focus, focus)
            self.assertIs(restored.root, cursor.root)
            self.assertEqual(restored.path, (1,))

    def test_lookup_has_no_source_term_cursor_compiler_hash_or_history_access(self):
        rows = (((("S", "_"), ("_", "S")), (1, 0)),
                ("_", ()), ((("_", "S"), "_"), (0, 1)), ("S", ()))
        table = compile_rows(rows)
        expected = {(control, observation): table.transition(control, *observation)
                    for control in range(table.state_count) for observation in OBSERVATIONS}
        queries = list(expected)
        random.Random(99422).shuffle(queries)
        with ExitStack() as stack:
            for name in ("builtins.open", "builtins.hash", "builtins.id",
                         "s_only.probes.compile_rows", "s_only.probes.compile_pattern",
                         "s_only.probes._Builder.match", "s_only.succinct_rows.compile_rows",
                         "s_only.succinct_rows.compile_pattern", "s_only.succinct_rows._failure_ticks",
                         "s_only.succinct_rows._validate_selection",
                         "s_only.succinct_probes.compile_pattern", "s_only.probes.Cursor.move",
                         "s_only.terms.format_term", "s_only.terms.prefix"):
                stack.enter_context(patch(name, side_effect=AssertionError(name)))
            stack.enter_context(patch.object(App, "__getattribute__", side_effect=AssertionError("term read")))
            stack.enter_context(patch.object(Cursor, "__getattribute__", side_effect=AssertionError("cursor read")))
            for control, observation in queries + list(reversed(queries)):
                self.assertEqual(table.transition(control, *observation), expected[control, observation])
        for control in (0, 1, table.start):
            for kind, incoming in ((PoisonStr("S"), "root"), ("S", PoisonStr("L"))):
                with self.assertRaises(ValueError):
                    table.transition(control, kind, incoming)
        for control in (PoisonInt(0), PoisonInt(table.start)):
            with self.assertRaises(ValueError):
                table.answer(control)
            with self.assertRaises(ValueError):
                table.transition(control, "S", "root")


if __name__ == "__main__":
    unittest.main()
