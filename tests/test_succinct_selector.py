"""Exact whole-graph comparisons and bounded native traces for interval code."""
from contextlib import ExitStack
from dataclasses import FrozenInstanceError, fields, replace
import hashlib
import json
from pathlib import Path
import sys
import time
import unittest
from unittest.mock import patch

from s_only import probes, succinct_probes, succinct_rows, succinct_walkers, walkers
from s_only.cts import Program
from s_only.encoding import encode
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit, compile_table as eager_compile
from s_only.root_selector import SelectorTable, execute, erase, step
from s_only.selector_parts.graph import Command, GraphBuilder
from s_only.succinct_selector import (
    SuccinctGraphBuilder, SuccinctSelectorTable, _DirectRow, _Fragment, compile_table,
)
from s_only.terms import App, S, prefix

ROOT = Path(__file__).resolve().parents[1]


def finish(builder, start):
    return (builder.finish(start) if type(builder) is SuccinctGraphBuilder
            else SelectorTable(builder.finish(), start))


def digest(table):
    value = hashlib.sha256()
    for control, row in enumerate(table.states):
        for observation, instruction in enumerate(row):
            value.update(f'{control}:{observation}:{instruction.command}:{instruction.next_state}\n'.encode())
    return value.hexdigest()


def eager(program):
    return eager_compile(program, required_period=None, max_states=300_000,
                         max_appendant_bits=8, max_phases=2)


class SuccinctEmbeddingTests(unittest.TestCase):
    def compare(self, original, compact):
        self.assertEqual(compact.state_count, len(original.states))
        self.assertEqual(compact.start, original.start)
        self.assertEqual(compact.linear_coefficient, original.linear_coefficient)
        for control, row in enumerate(original.states):
            self.assertEqual(compact.status(control), original.status(control))
            for observation, entry in zip(OBSERVATIONS, row):
                self.assertEqual(compact.transition(control, *observation), entry)
        self.assertEqual(compact.materialize(max_states=len(original.states)), original)

    def test_all_fragment_kinds_and_empty_boundaries(self):
        pattern = (('S', '_'), ('_', 'S'))
        rows = ((pattern, (0, 1)), (('S', '_'), (1,)))
        cases = (
            (probes.compile_pattern, succinct_probes.compile_pattern, '_'),
            (probes.compile_pattern, succinct_probes.compile_pattern, pattern),
            (probes.compile_rows, succinct_rows.compile_rows, ()),
            (probes.compile_rows, succinct_rows.compile_rows, (('_', ()), ('S', ()))),
            (probes.compile_rows, succinct_rows.compile_rows,
             (('S', ()), ('_', ()), (pattern, (1,)))),
            (walkers.compile_inverse_rows, succinct_walkers.compile_inverse_rows, ()),
            (walkers.compile_inverse_rows, succinct_walkers.compile_inverse_rows, rows),
            (walkers.compile_descent, succinct_walkers.compile_descent, ()),
            (walkers.compile_descent, succinct_walkers.compile_descent, rows),
            (walkers.compile_ascent, succinct_walkers.compile_ascent, ()),
            (walkers.compile_ascent, succinct_walkers.compile_ascent, rows),
        )
        for old_compile, new_compile, source in cases:
            with self.subTest(compiler=old_compile.__name__, source=source):
                tables = []
                for builder, fragment in ((GraphBuilder(), old_compile(source)),
                                          (SuccinctGraphBuilder(), new_compile(source))):
                    no = builder.uniform('normal')
                    done = builder.uniform('contracted')
                    yes = builder.uniform('Rdx', done)
                    start = builder.embed(fragment, yes, no)
                    tables.append(finish(builder, start))
                self.compare(*tables)

    def test_mixed_builder_order_forward_reservation_and_assignment(self):
        tables = []
        for builder in (GraphBuilder(), SuccinctGraphBuilder()):
            normal = builder.uniform('normal')
            contracted = builder.uniform('contracted')
            selected = builder.uniform('Rdx', contracted)
            before = builder.reserve()
            missed = builder.reserve()
            hit = builder.rows((('_', ()), ('S', ())), selected, missed)
            ascent = builder.ascent(((('_', '_'), (1,)),), hit)
            descent = builder.descent(((('_', '_'), (0,)),), ascent)
            inverse = builder.inverse_rows(((('_', '_'), (1,)),), descent, missed)
            builder.jump(before, builder.path((1, 0), inverse))
            builder.states[missed] = tuple(Command('stay', normal) if side == 'root'
                                          else Command('U', missed)
                                          for _, side in OBSERVATIONS)
            start = builder.root(builder.node_test(normal, before))
            tables.append(finish(builder, start))
        self.compare(*tables)

    def test_empty_walkers_keep_unreachable_feedback(self):
        builder = SuccinctGraphBuilder()
        normal = builder.uniform('normal')
        self.assertEqual(builder.descent((), normal), normal)
        self.assertEqual(builder.state_count, 2)
        self.assertEqual(builder.ascent((), normal), normal)
        table = builder.finish(normal)
        self.assertEqual(table.state_count, 3)
        for control in (1, 2):
            self.assertIsNone(table.status(control))
            for observation in OBSERVATIONS:
                self.assertEqual(table.transition(control, *observation), Command('stay', normal))

    def test_reservation_facade_is_not_a_virtual_collection(self):
        builder = SuccinctGraphBuilder()
        q = builder.reserve()
        self.assertIsNone(builder.states[q])
        with self.assertRaises(TypeError):
            len(builder.states)
        with self.assertRaises(TypeError):
            tuple(builder.states)
        with self.assertRaises(ValueError):
            builder.finish(q)
        with self.assertRaises(ValueError):
            builder.states[True] = (Command('normal'),) * 6
        builder.states[q] = (Command('normal'),) * 6
        with self.assertRaises(ValueError):
            builder.jump(q, q)
        self.assertEqual(builder.finish(q).status(q), 'normal')

    def test_huge_virtual_offsets_and_direct_rows_after_embedding(self):
        pattern = 'S'
        for _ in range(128):
            pattern = (pattern, pattern)
        probe = succinct_probes.compile_pattern(pattern)
        builder = SuccinctGraphBuilder()
        normal = builder.uniform('normal')
        contracted = builder.uniform('contracted')
        yes = builder.uniform('Rdx', contracted)
        start = builder.embed(probe, yes, normal)
        origin = 3
        after = builder.root(start)
        table = builder.finish(after)
        self.assertGreater(table.state_count, sys.maxsize)
        self.assertEqual(table.state_count, probe.state_count + 2)
        self.assertEqual(table.metadata_records, 159)
        self.assertFalse(hasattr(table, 'states'))
        for old in (2, 3, 4, 10, probe.state_count // 2, probe.state_count - 1):
            for observation in OBSERVATIONS:
                entry = probe.transition(old, *observation)
                target = normal if entry.next_state == 0 else yes if entry.next_state == 1 else origin + entry.next_state - 2
                self.assertEqual(table.transition(origin + old - 2, *observation),
                                 Command(entry.command, target))
        self.assertEqual(table.transition(after, 'S', 'root'), Command('stay', start))
        with self.assertRaises(CompilationLimit):
            table.materialize(max_states=100_000)


class SuccinctValidationTests(unittest.TestCase):
    def setUp(self):
        self.normal = _DirectRow(0, (Command('normal'),) * 6)
        self.contracted = _DirectRow(1, (Command('contracted'),) * 6)
        self.selected = _DirectRow(2, (Command('Rdx', 1),) * 6)
        self.blocks = (self.normal, self.contracted, self.selected)
        self.table = SuccinctSelectorTable(self.blocks, 2)

    def test_immutable_representation(self):
        self.assertEqual(tuple(field.name for field in fields(self.table)), ('blocks', 'start'))
        with self.assertRaises(FrozenInstanceError):
            self.table.start = 0
        with self.assertRaises(FrozenInstanceError):
            self.normal.origin = 1
        with self.assertRaises(FrozenInstanceError):
            self.normal.row[0].command = 'Rdx'

    def test_invalid_interval_and_start_metadata(self):
        for blocks, start in (([], 0), ((), 0), (list(self.blocks), 0),
                              ((replace(self.normal, origin=True),), 0),
                              ((replace(self.normal, origin=1),), 1),
                              ((self.normal, replace(self.contracted, origin=2)), 0),
                              (self.blocks, True), (self.blocks, -1), (self.blocks, 3),
                              ((self.normal, object()), 0)):
            with self.subTest(blocks=blocks, start=start), self.assertRaises(ValueError):
                SuccinctSelectorTable(blocks, start)

    def test_invalid_direct_instructions_and_terminal_rows(self):
        class Word(str):
            pass
        with self.assertRaises(ValueError):
            Command(Word('normal'))
        bad_rows = (list(self.normal.row), (), (Command('normal'),) * 5,
                    (object(),) * 6, (Command('true'),) * 6,
                    (Command('normal', 0),) * 6,
                    (Command('normal'),) * 5 + (Command('contracted'),),
                    (Command('stay', None),) * 6, (Command('stay', True),) * 6,
                    (Command('L', 3),) * 6, (Command('unknown', 0),) * 6,
                    (Command('Rdx', 0),) * 6,
                    (Command('Rdx', 1),) * 5 + (Command('stay', 1),))
        for row in bad_rows:
            with self.subTest(row=row), self.assertRaises(ValueError):
                SuccinctSelectorTable((replace(self.normal, row=row),) + self.blocks[1:], 2)
        with self.assertRaises(ValueError):
            SuccinctSelectorTable((self.normal, replace(self.contracted,
                                  row=(Command('contracted'), Command('normal'))), self.selected), 2)

    def test_fragment_targets_exact_types_and_nested_validation(self):
        probe = succinct_probes.compile_pattern('S')
        fragment = _Fragment(3, probe, 2, 0)
        table = SuccinctSelectorTable(self.blocks + (fragment,), 3)
        self.assertEqual(table.transition(3, 'S', 'root'), Command('stay', 2))
        for bad in (replace(fragment, yes=True), replace(fragment, no=4),
                    replace(fragment, table=object()),
                    replace(fragment, table=succinct_probes.compile_pattern('_'))):
            with self.subTest(fragment=bad), self.assertRaises(ValueError):
                SuccinctSelectorTable(self.blocks + (bad,), 3)
        corrupt = object.__new__(type(probe))
        object.__setattr__(corrupt, 'root', probe.root)
        object.__setattr__(corrupt, 'nodes', (replace(probe.nodes[0], width=2),))
        with self.assertRaises(ValueError):
            SuccinctSelectorTable(self.blocks + (replace(fragment, table=corrupt),), 3)
        # Rdx cannot continue to movement code even if it leads to contracted.
        with self.assertRaises(ValueError):
            SuccinctSelectorTable((self.normal, self.contracted,
                                   replace(self.selected, row=(Command('Rdx', 3),) * 6), fragment), 2)

    def test_control_observation_and_materialization_caps(self):
        class Word(str):
            pass
        for control in (True, -1, 3, 1.0, None):
            with self.assertRaises(ValueError):
                self.table.transition(control, 'S', 'root')
            with self.assertRaises(ValueError):
                self.table.status(control)
        for observation in (('bad', 'root'), ('S', 'bad'), (Word('S'), 'root'),
                            ('S', Word('root')), (None, 'root')):
            with self.assertRaises(ValueError):
                self.table.transition(0, *observation)
        for cap in (0, -1, True, 3.0, None):
            with self.assertRaises(ValueError):
                self.table.materialize(max_states=cap)
        with self.assertRaises(CompilationLimit):
            self.table.materialize(max_states=2)
        self.assertEqual(len(self.table.materialize(max_states=3).states), 3)

    def test_compile_scope_metadata_and_soft_time_limits(self):
        with self.assertRaises(TypeError):
            compile_table(('',))
        with self.assertRaises(CompilationLimit):
            compile_table(Program(('',) * 3))
        with self.assertRaises(CompilationLimit):
            compile_table(Program(('1' * 9,)))
        for cap in (None, True, -1, 9, 1.5):
            with self.assertRaises(ValueError):
                compile_table(Program(('',)), max_appendant_bits=cap)
        for cap in (None, True, 0, -1, 1.5):
            with self.assertRaises(ValueError):
                SuccinctGraphBuilder(max_metadata_records=cap)
        for seconds in (None, True, 0, -1, float('inf'), float('nan')):
            with self.assertRaises(ValueError):
                SuccinctGraphBuilder(max_compile_seconds=seconds)
        with self.assertRaises(CompilationLimit):
            compile_table(Program(('',)), max_metadata_records=7)
        builder = SuccinctGraphBuilder(max_metadata_records=8)
        normal = builder.uniform('normal')
        with self.assertRaises(CompilationLimit):
            builder.match((('S', 'S'), ('S', 'S')), normal, normal)
        with patch('s_only.succinct_selector.time.monotonic', side_effect=(0, 2)):
            builder = SuccinctGraphBuilder(max_compile_seconds=1)
            with self.assertRaises(CompilationLimit):
                builder.uniform('normal')


class WholeSuccinctSelectorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = Program(('1', ''))
        cls.compact = compile_table(cls.program)
        cls.original = eager(cls.program)

    def test_every_same_index_primitive_and_frozen_legacy_digest(self):
        compact, original = self.compact, self.original
        self.assertEqual((compact.state_count, compact.start), (257_299, 227_379))
        self.assertEqual(compact.start, original.start)
        self.assertEqual(compact.state_count, len(original.states))
        self.assertEqual((len(compact.blocks), compact.metadata_records), (370, 33_040))
        actual = hashlib.sha256()
        for control, row in enumerate(original.states):
            self.assertEqual(compact.status(control), original.status(control))
            for index, (obs, expected) in enumerate(zip(OBSERVATIONS, row)):
                entry = compact.transition(control, *obs)
                self.assertEqual(entry, expected)
                actual.update(f'{control}:{index}:{entry.command}:{entry.next_state}\n'.encode())
        golden = json.loads((ROOT / 'results/two_phase_programs.json').read_text())['programs'][0]
        self.assertEqual(actual.hexdigest(), golden['control_table_sha256'])
        self.assertEqual(digest(original), actual.hexdigest())

    def test_period_one_full_materialization_is_exact(self):
        compact = compile_table(Program(('',)))
        self.assertEqual((compact.state_count, compact.start), (82_116, 71_512))
        self.assertEqual((len(compact.blocks), compact.metadata_records), (313, 13_460))
        self.assertEqual(compact.materialize(max_states=100_000), eager(Program(('',))))

    def test_bounded_native_trace_has_identical_ticks_and_one_contraction(self):
        records = json.loads((ROOT / 'fixtures/queue_101_path.json').read_text())
        term = encode(self.program, '101')
        deadline = time.monotonic() + 20
        for record in records['steps'][:12]:
            left = Configuration(self.original.start, Cursor.at(term))
            right = Configuration(self.compact.start, Cursor.at(term))
            for ticks in range(200_000):
                self.assertEqual(left.control, right.control)
                self.assertEqual(left.cursor.path, right.cursor.path)
                self.assertIs(left.cursor.focus, right.cursor.focus)
                if self.compact.status(right.control) in ('normal', 'Rdx'):
                    break
                left = step(self.original, left)
                right = step(self.compact, right)
                if ticks % 1024 == 0 and time.monotonic() >= deadline:
                    self.fail('external trace wall-time cap')
            else:
                self.fail('external trace microtick cap')
            self.assertEqual(self.compact.status(right.control), 'Rdx')
            self.assertEqual(right.cursor.path, tuple(map(int, record['path'])))
            result = step(self.compact, right)
            self.assertEqual(self.compact.status(result.control), 'contracted')
            self.assertIs(step(self.compact, result), result)
            term = erase(result.cursor)
            self.assertEqual(hashlib.sha256(prefix(term).encode('ascii')).hexdigest(),
                             record['after_sha256'])

    def test_unmodified_execute_and_normal_absorption(self):
        for term in (S, App(S, S), App(App(S, S), S)):
            result = execute(term, self.compact)
            self.assertEqual(self.compact.status(result.control), 'normal')
            self.assertIs(erase(result.cursor), term)
            self.assertIs(step(self.compact, result), result)
        redex = App(App(App(S, S), S), S)
        left, right = execute(redex, self.original), execute(redex, self.compact)
        self.assertEqual(left.control, right.control)
        self.assertEqual(erase(left.cursor), erase(right.cursor))
        self.assertEqual(erase(right.cursor), App(App(S, S), App(S, S)))

    def test_lookup_has_no_compiler_term_history_hash_or_file_access(self):
        controls = (0, 1, 2, 3, 14, 8123, self.compact.start, self.compact.state_count - 1)
        expected = {(q, obs): self.original.transition(q, *obs)
                    for q in controls for obs in OBSERVATIONS}
        blocked = AssertionError('lookup consulted a forbidden runtime source')
        targets = (
            's_only.succinct_selector.compile_pattern', 's_only.succinct_selector.compile_rows',
            's_only.succinct_selector.compile_inverse_rows', 's_only.succinct_selector.compile_descent',
            's_only.succinct_selector.compile_ascent', 's_only.succinct_selector.time.monotonic',
            's_only.succinct_probes.compile_pattern', 's_only.succinct_rows.compile_rows',
            's_only.succinct_walkers.compile_inverse_rows', 's_only.cts.step',
            's_only.encoding.compile_program', 's_only.program_selector_parts.patterns.PatternFamily',
            's_only.root_selector.selector_table', 's_only.probes.Cursor.at',
            's_only.probes.Cursor.move', 'builtins.open', 'builtins.hash', 'builtins.id',
        )
        with ExitStack() as stack:
            for target in targets:
                stack.enter_context(patch(target, side_effect=blocked))
            for q in reversed(controls):
                for obs in reversed(OBSERVATIONS):
                    self.assertEqual(self.compact.transition(q, *obs), expected[q, obs])


if __name__ == '__main__':
    unittest.main()
