"""Independent adversarial tests for the whole interval-coded selector.

All runtime budgets and archive comparisons belong to this external harness.
The production transition is still given only finite control and observations.
"""
from dataclasses import fields, is_dataclass, replace
import hashlib
import json
from pathlib import Path
import random
import sys
import time
import unittest
from unittest.mock import patch

from s_only import succinct_probes, succinct_rows, succinct_walkers
from s_only.cts import Program
from s_only.encoding import encode
from s_only.marker_observer import ObserverTable
from s_only.probes import Configuration, Cursor, Instruction, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit
from s_only.root_selector import SelectorTable, erase, step
from s_only.selector_parts.graph import Command, GraphBuilder
from s_only.succinct_selector import (
    SuccinctGraphBuilder, SuccinctSelectorTable, _DirectRow, _Fragment,
    compile_table,
)
from s_only.terms import nodes, prefix


ROOT = Path(__file__).resolve().parents[1]


def forged(cls, **values):
    result = object.__new__(cls)
    for name, value in values.items():
        object.__setattr__(result, name, value)
    return result


def finished(builder, start):
    if type(builder) is SuccinctGraphBuilder:
        return builder.finish(start)
    return SelectorTable(builder.finish(), start)


class SuccinctSelectorReviewTests(unittest.TestCase):
    def assert_same_table(self, original, compact):
        self.assertEqual((len(original.states), original.start),
                         (compact.state_count, compact.start))
        controls = list(range(compact.state_count))
        random.Random(831199).shuffle(controls)
        for control in controls:
            self.assertEqual(compact.status(control), original.status(control))
            for observation in reversed(OBSERVATIONS):
                actual = compact.transition(control, *observation)
                self.assertEqual(actual, original.transition(control, *observation))
                self.assertIs(type(actual), Command)
                if actual.next_state is not None:
                    self.assertIs(type(actual.next_state), int)
                    self.assertTrue(0 <= actual.next_state < compact.state_count)
        with self.assertRaises(CompilationLimit):
            compact.materialize(max_states=compact.state_count - 1)
        self.assertEqual(compact.materialize(max_states=compact.state_count), original)

    def test_randomized_compositions_forward_cross_and_self_targets(self):
        patterns = ('_', 'S', ('_', '_'), ('S', ('_', 'S')),
                    (('S', '_'), ('_', ('S', '_'))))
        ordinary = ((), (('_', ()),), (('S', ()), ('_', ()), ('S', ())),
                    ((patterns[-1], (1, 1, 0)), (patterns[-2], (1,))))
        strict = ((), ((patterns[2], (0,)),),
                  ((patterns[-1], (1, 1)), (patterns[-2], (1, 0))))
        for seed in range(24):
            tables = []
            for builder in (GraphBuilder(), SuccinctGraphBuilder()):
                rng = random.Random(4001 + seed)
                normal = builder.uniform('normal')
                contracted = builder.uniform('contracted')
                selected = builder.uniform('Rdx', contracted)
                reserved = [builder.reserve() for _ in range(4)]
                entries = [normal, contracted, selected] + reserved
                for _ in range(18):
                    yes, no = rng.choices(entries, k=2)
                    operation = rng.randrange(7)
                    if operation == 0:
                        entry = builder.match(rng.choice(patterns), yes, no)
                    elif operation == 1:
                        entry = builder.rows(rng.choice(ordinary), yes, no)
                    elif operation == 2:
                        entry = builder.inverse_rows(rng.choice(strict), yes, no)
                    elif operation == 3:
                        entry = builder.ascent(rng.choice(strict), no)
                    elif operation == 4:
                        entry = builder.descent(rng.choice(strict), no)
                    elif operation == 5:
                        entry = builder.root(yes)
                    else:
                        entry = builder.path(tuple(rng.randrange(2) for _ in range(4)), no)
                    entries.append(entry)
                builder.jump(reserved[0], reserved[0])
                builder.jump(reserved[1], entries[-1])
                builder.states[reserved[2]] = tuple(
                    Command('stay', entries[-2] if kind == 'S' else reserved[1])
                    for kind, _ in OBSERVATIONS)
                builder.jump(reserved[3], reserved[2])
                tables.append(finished(builder, entries[-1]))
            with self.subTest(seed=seed):
                self.assert_same_table(*tables)

    def test_repeated_same_fragment_keeps_distinct_controls_and_forward_targets(self):
        probe = succinct_rows.compile_rows(((('S', '_'), (1,)), ('_', ())))
        walker = succinct_walkers.compile_ascent((((('S', '_'), '_'), (0, 1)),))
        builder = SuccinctGraphBuilder()
        normal = builder.uniform('normal')
        later = builder.reserve()
        first = builder.embed(probe, later, normal)
        second = builder.embed(probe, first, later)
        third = builder.embed(walker, first, second)
        builder.jump(later, third)
        table = builder.finish(later)
        self.assertNotEqual(first, second)
        self.assertIs(table.blocks[2].table, table.blocks[3].table)
        for block in table.blocks[2:]:
            drop = 1 if type(block.table) is succinct_walkers.SuccinctWalkerTable else 2
            for local in range(drop, block.table.state_count):
                for obs in OBSERVATIONS:
                    expected = block.table.transition(local, *obs)
                    target = expected.next_state
                    target = (block.no if target == 0 else block.yes
                              if target == 1 and drop == 2 else block.origin + target - drop)
                    self.assertEqual(table.transition(block.origin + local - drop, *obs),
                                     Command(expected.command, target))
        # A walker's yes continuation is not used, but remains validated.
        with self.assertRaises(ValueError):
            SuccinctSelectorTable(table.blocks[:-1] +
                                  (replace(table.blocks[-1], yes=table.state_count),), later)

    def test_all_fragment_kinds_after_enormous_offsets(self):
        pattern = ('S', '_')
        for _ in range(96):
            pattern = (pattern, pattern)
        rows = ((pattern, (0, 1, 0, 1)),)
        fragments = (succinct_probes.compile_pattern(pattern),
                     succinct_rows.compile_rows(rows),
                     succinct_walkers.compile_inverse_rows(rows),
                     succinct_walkers.compile_descent(rows),
                     succinct_walkers.compile_ascent(rows))
        builder = SuccinctGraphBuilder()
        normal = builder.uniform('normal')
        later = builder.reserve()
        for fragment in fragments:
            builder.embed(fragment, later, normal)
        after = builder.root(later)
        builder.jump(later, after)
        table = builder.finish(after)
        self.assertGreater(table.state_count, sys.maxsize)
        self.assertFalse(hasattr(table, 'states'))
        for block in table.blocks[2:-1]:
            drop = 1 if type(block.table) is succinct_walkers.SuccinctWalkerTable else 2
            local_controls = {drop, drop + 1, block.table.start,
                              block.table.state_count // 2,
                              block.table.state_count - 2, block.table.state_count - 1}
            if hasattr(block.table, 'blocks'):
                for inner in block.table.blocks:
                    local_controls.update((inner.origin, inner.stop - 1))
            for local in local_controls:
                for obs in OBSERVATIONS:
                    source = block.table.transition(local, *obs)
                    target = source.next_state
                    target = (normal if target == 0 else later if target == 1 and drop == 2
                              else block.origin + target - drop)
                    self.assertEqual(table.transition(block.origin + local - drop, *obs),
                                     Command(source.command, target))
        for side in ('root', 'L', 'R'):
            self.assertEqual(table.transition(after, 'application', side),
                             Command('stay', later) if side == 'root' else Command('U', after))
        with patch.object(SuccinctSelectorTable, 'transition', side_effect=AssertionError('enumerated')):
            with self.assertRaises(CompilationLimit):
                table.materialize(max_states=1_000_000)

    def test_direct_targets_and_rdx_target_are_validated_even_when_unreachable(self):
        class Int(int):
            pass
        class Text(str):
            pass
        class DerivedCommand(Command):
            pass
        good = (_DirectRow(0, (Command('normal'),) * 6),
                _DirectRow(1, (Command('Rdx', 2),) * 6),
                _DirectRow(2, (Command('contracted'),) * 6))
        self.assertEqual(SuccinctSelectorTable(good, 0).status(1), 'Rdx')
        for bad in (None, False, Int(0), -1, 3, 0.0):
            for primitive in ('stay', 'L', 'R', 'U', 'Rdx'):
                with self.subTest(target=bad, command=primitive), self.assertRaises(ValueError):
                    SuccinctSelectorTable((good[0], _DirectRow(1, (Command(primitive, bad),) * 6),
                                           good[2]), 0)
        for row in ((), (Command('contracted'),),
                    (Command('contracted'),) * 5 + (Command('normal'),),
                    (Command('contracted', 0),) * 6,
                    (DerivedCommand('contracted'),) * 6,
                    (forged(Command, command=Text('contracted'), next_state=None),) * 6,
                    list(good[2].row)):
            with self.subTest(row=row), self.assertRaises(ValueError):
                SuccinctSelectorTable(good[:2] + (_DirectRow(2, row),), 0)

    def test_plain_type_preflight_precedes_all_uniformity_comparisons(self):
        class Poison:
            def __eq__(self, other):
                raise AssertionError('unvalidated metadata equality was called')

            def __ne__(self, other):
                raise AssertionError('unvalidated metadata inequality was called')

        constructors = (
            ('succinct', 'normal', lambda row: SuccinctSelectorTable((_DirectRow(0, row),), 0)),
            ('dense', 'normal', lambda row: SelectorTable((row,), 0)),
            ('observer', 'false', lambda row: ObserverTable((row,), 0)),
        )
        for name, terminal, constructor in constructors:
            for invalid in (Poison(), Command(terminal, Poison()),
                            forged(Command, command=Poison(), next_state=None)):
                row = (Command(terminal), invalid) + (Command(terminal),) * 4
                with self.subTest(table=name, invalid=type(invalid)), self.assertRaises(ValueError):
                    constructor(row)
        invalid = forged(Command, command=Poison(), next_state=None)
        rows = ((Command('Rdx', 1),) * 6, (invalid,) * 6)
        for name, constructor in (
                ('dense', lambda: SelectorTable(rows, 0)),
                ('succinct', lambda: SuccinctSelectorTable(tuple(_DirectRow(q, row)
                                                               for q, row in enumerate(rows)), 0))):
            with self.subTest(rdx_target=name), self.assertRaises(ValueError):
                constructor()

    def test_class_whitelists_cannot_be_spoofed_by_metaclass_equality(self):
        class Pretend(type):
            def __eq__(self, other):
                return True

        class MutableFragment(metaclass=Pretend):
            start = 2
            state_count = 3
            patterns = ()
            blocks = ()
            target = 0

            def __post_init__(self):
                pass

            def transition(self, control, kind, incoming):
                return Instruction('stay', self.target)

        class MutableBlock(metaclass=Pretend):
            origin = 0
            stop = 1
            row = (Command('normal'),) * 6

        fragment = MutableFragment()
        builder = SuccinctGraphBuilder()
        normal = builder.uniform('normal')
        contracted = builder.uniform('contracted')
        with self.subTest(case='builder fragment'), self.assertRaises(ValueError):
            builder.embed(fragment, contracted, normal)
        with self.subTest(case='nested fragment'), self.assertRaises(ValueError):
            SuccinctSelectorTable((_DirectRow(0, (Command('normal'),) * 6),
                                   _Fragment(1, fragment, 0, 0)), 0)
        with self.subTest(case='interval block'), self.assertRaises(ValueError):
            SuccinctSelectorTable((MutableBlock(),), 0)
        with self.subTest(case='walker child'), self.assertRaises(ValueError):
            succinct_walkers.SuccinctWalkerTable(fragment)

    def test_class_whitelists_reject_before_custom_metaclass_comparison(self):
        class Poison(type):
            def __eq__(self, other):
                raise AssertionError('class whitelist called custom equality')

            def __ne__(self, other):
                raise AssertionError('class whitelist called custom inequality')

        class Unknown(metaclass=Poison):
            def __float__(self):
                raise AssertionError('invalid time budget was converted')

        for constructor in (
                lambda: SuccinctGraphBuilder().embed(Unknown(), 0, 0),
                lambda: SuccinctSelectorTable((Unknown(),), 0),
                lambda: succinct_walkers.SuccinctWalkerTable(Unknown()),
                lambda: SuccinctGraphBuilder(max_compile_seconds=Unknown())):
            with self.subTest(constructor=constructor), self.assertRaises(ValueError):
                constructor()

    def test_metadata_exact_threshold_and_rejected_embedding_are_atomic(self):
        probe = succinct_probes.compile_pattern(('S', ('_', 'S')))
        full = SuccinctGraphBuilder()
        normal = full.uniform('normal')
        start = full.embed(probe, normal, normal)
        expected = full.finish(start)
        exact = SuccinctGraphBuilder(max_metadata_records=expected.metadata_records)
        normal = exact.uniform('normal')
        self.assertEqual(exact.finish(exact.embed(probe, normal, normal)), expected)
        short = SuccinctGraphBuilder(max_metadata_records=expected.metadata_records - 1)
        normal = short.uniform('normal')
        with self.assertRaises(CompilationLimit):
            short.embed(probe, normal, normal)
        self.assertEqual(short.state_count, 1)
        self.assertEqual(short.finish(normal).metadata_records, 7)

    def test_finished_table_retains_only_exact_frozen_code(self):
        builder = SuccinctGraphBuilder()
        normal = builder.uniform('normal')
        start = builder.rows(((('S', ('_', 'S')), (1,)),), normal, normal)
        table = builder.finish(start)
        seen, pending = set(), [table]
        while pending:
            value = pending.pop()
            if id(value) in seen:
                continue
            seen.add(id(value))
            if any(type(value) is allowed for allowed in (int, str, type(None))):
                continue
            if type(value) is tuple:
                pending.extend(value)
            else:
                self.assertTrue(is_dataclass(value), type(value))
                self.assertTrue(value.__dataclass_params__.frozen)
                self.assertFalse(hasattr(value, '__dict__'))
                pending.extend(getattr(value, field.name) for field in fields(value))
        expected = tuple(tuple(table.transition(q, *obs) for obs in OBSERVATIONS)
                         for q in range(table.state_count))
        # Mutating compile-time objects after finish cannot affect fixed code.
        builder._pieces.clear()
        builder._direct.clear()
        builder._count = 0
        for q in reversed(range(table.state_count)):
            self.assertEqual(tuple(table.transition(q, *obs) for obs in OBSERVATIONS), expected[q])

    def test_all_85_native_contractions_match_archive_with_explicit_budgets(self):
        data = json.loads((ROOT / 'fixtures/queue_101_path.json').read_text())
        archive = json.loads((ROOT / 'results/root_selector.json').read_text())
        self.assertEqual(len(data['steps']), 85)
        table = compile_table(Program(('1', '')))
        term = encode(Program(('1', '')), '101')
        self.assertEqual(prefix(term), data['initial_prefix'])
        deadline = time.monotonic() + 90
        total_ticks = 0
        for index, (record, archived) in enumerate(zip(data['steps'], archive['fixture_selections']), 1):
            self.assertLessEqual(nodes(term), 400_000)
            state = Configuration(table.start, Cursor.at(term))
            ticks = 0
            while table.status(state.control) is None:
                self.assertLess(ticks, 100_000, ('per-selection microtick cap', index))
                self.assertLess(total_ticks, 2_000_000, 'total microtick cap')
                if ticks % 1024 == 0:
                    self.assertLess(time.monotonic(), deadline, 'external wall-time cap')
                state = step(table, state)
                ticks += 1
                total_ticks += 1
            with self.subTest(contraction=index):
                self.assertEqual(table.status(state.control), 'Rdx')
                self.assertIs(state.cursor.root, term)
                self.assertEqual(state.cursor.path, tuple(map(int, record['path'])))
                self.assertEqual(ticks, archived['selection_microticks'])
                after = step(table, state)
                self.assertEqual(table.status(after.control), 'contracted')
                self.assertIs(step(table, after), after)
                term = erase(after.cursor)
                self.assertLessEqual(nodes(term), 400_000)
                self.assertEqual(nodes(term), record['nodes'])
                self.assertEqual(hashlib.sha256(prefix(term).encode('ascii')).hexdigest(),
                                 record['after_sha256'])
        self.assertEqual(total_ticks, 1_315_234)
        self.assertEqual(total_ticks, archive['total_selection_microticks'])


if __name__ == '__main__':
    unittest.main()
