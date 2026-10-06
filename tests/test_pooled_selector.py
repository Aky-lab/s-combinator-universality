"""Exact graph/trace preservation and compile-only value-sharing checks."""
from dataclasses import fields, is_dataclass, replace
import gc
import unittest
import weakref

from s_only.cts import Program
from s_only.encoding import encode
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit
from s_only.root_selector import erase, step
from s_only.succinct_probes import _Descriptor, SuccinctProbeTable, compile_pattern
from s_only.succinct_rows import compile_rows
from s_only.succinct_walkers import compile_inverse_rows, compile_descent, compile_ascent
from s_only.succinct_selector import SuccinctGraphBuilder, SuccinctSelectorTable
from s_only.succinct_periodic import compile_table as unpooled_compile
from s_only.pooled_selector import (
    _CodePool, PooledGraphBuilder, compile_table, compile_with_statistics,
)


def reachable(value):
    pending, seen = [value], set()
    while pending:
        item = pending.pop()
        if id(item) in seen:
            continue
        seen.add(id(item))
        yield item
        if type(item) is tuple:
            pending.extend(item)
        elif is_dataclass(item):
            pending.extend(getattr(item, field.name) for field in fields(item))


def graph_equal(test, left, right):
    test.assertEqual(left, right)
    test.assertEqual(left.state_count, right.state_count)
    test.assertEqual(left.start, right.start)
    for control in range(left.state_count):
        if hasattr(left, 'status'):
            test.assertEqual(left.status(control), right.status(control))
        for obs in OBSERVATIONS:
            test.assertEqual(left.transition(control, *obs), right.transition(control, *obs))


class PoolFactoryTests(unittest.TestCase):
    def test_equal_values_share_within_one_factory_only(self):
        pool = _CodePool()
        a = compile_pattern(tuple(['S', '_']), _factory=pool)
        b = compile_pattern(tuple(['S', '_']), _factory=pool)
        c = compile_pattern(tuple(['S', '_']), _factory=_CodePool())
        self.assertIs(a, b)
        self.assertEqual(a, c)
        self.assertIsNot(a, c)
        self.assertIsNot(a.nodes[-1], c.nodes[-1])
        stats = pool.statistics()
        self.assertEqual((stats.descriptor_requests, stats.descriptor_entries), (6, 3))
        self.assertEqual((stats.probe_requests, stats.probe_entries), (2, 1))
        self.assertEqual((stats.descriptor_hits, stats.probe_hits, stats.peak_pool_entries), (3, 1, 4))

    def test_local_index_and_occurrence_layout_is_unchanged(self):
        pool = _CodePool()
        shared = ('S', '_')
        patterns = ('_', 'S', ('_', '_'), (shared, shared),
                    (tuple(['S', '_']), tuple(['S', '_'])))
        for pattern in patterns:
            with self.subTest(pattern=pattern):
                graph_equal(self, compile_pattern(pattern), compile_pattern(pattern, _factory=pool))
        # Equal occurrence trees with different identity DAGs are not rewritten.
        self.assertNotEqual(compile_pattern(patterns[-2]), compile_pattern(patterns[-1]))

    def test_deep_dag_uses_flat_descriptor_keys_not_recursive_pattern_hash(self):
        pattern = 'S'
        for _ in range(1500):
            pattern = (pattern, pattern)
        pool = _CodePool(max_pool_records=1600)
        first = compile_pattern(pattern, _factory=pool)
        second = compile_pattern(pattern, _factory=pool)
        self.assertIs(first, second)
        self.assertEqual(len(first.nodes), 1501)
        self.assertEqual(first.state_count, 7 * 2 ** 1500 - 4)
        for control in (0, 1, 2, first.state_count // 2, first.start):
            for obs in OBSERVATIONS:
                self.assertEqual(first.transition(control, *obs), second.transition(control, *obs))

    def test_hostile_fields_are_rejected_before_hash_or_equality(self):
        class Poison:
            def __hash__(self):
                raise AssertionError('hostile hashing')
            def __eq__(self, other):
                raise AssertionError('hostile comparison')
        class FakeInt(int):
            def __hash__(self):
                raise AssertionError('hostile integer hashing')
        good = _Descriptor('S', None, None, 1, 1, 1)
        pool = _CodePool()
        for name, value in (('kind', Poison()), ('width', Poison()), ('ticks', True),
                            ('height', FakeInt(1)), ('left', Poison()), ('right', False)):
            with self.subTest(field=name), self.assertRaises(ValueError):
                pool.descriptor(replace(good, **{name: value}))
        for bad in (Poison(), _Descriptor('pair', Poison(), 0, 6, 5, 2),
                    _Descriptor('S', None, None, 2, 1, 1)):
            with self.assertRaises(ValueError):
                pool.descriptor(bad)
        forged = object.__new__(SuccinctProbeTable)
        object.__setattr__(forged, 'nodes', (replace(good, width=Poison()),))
        object.__setattr__(forged, 'root', 0)
        with self.assertRaises(ValueError):
            pool.probe(forged)
        object.__setattr__(forged, 'nodes', (good, _Descriptor('pair', 0, 0, 0, 0, 0)))
        object.__setattr__(forged, 'root', 1)
        with self.assertRaises(ValueError):
            pool.probe(forged)
        self.assertEqual(pool.statistics().peak_pool_entries, 0)

    def test_pool_budget_counts_whole_tables_and_descriptors(self):
        pool = _CodePool(max_pool_records=4)
        compile_pattern(('S', '_'), _factory=pool)
        compile_pattern(('S', '_'), _factory=pool)  # Hits do not consume entries.
        self.assertEqual(pool.statistics().peak_pool_entries, 4)
        with self.assertRaises(CompilationLimit):
            compile_pattern('S', _factory=pool)  # New table, existing descriptor.
        self.assertEqual(pool.statistics().peak_pool_entries, 4)
        with self.assertRaises(CompilationLimit):
            compile_pattern('S', _factory=_CodePool(deadline=0))


class PooledCompositionTests(unittest.TestCase):
    def test_rows_and_walkers_match_every_primitive_entry(self):
        pattern = (('S', '_'), ('_', 'S'))
        strict = ((pattern, (0, 1)), (tuple(['S', '_']), (1,)))
        for compiler, sources in (
                (compile_rows, ((), (('_', ()),), strict,
                                (('S', ()), ('_', ()), (pattern, (1,))))),
                (compile_inverse_rows, ((), strict)),
                (compile_descent, ((), strict)),
                (compile_ascent, ((), strict))):
            for source in sources:
                with self.subTest(compiler=compiler.__name__, source=source):
                    graph_equal(self, compiler(source), compiler(source, _factory=_CodePool()))

    def test_all_builder_paths_share_code_without_merging_intervals(self):
        tables, pooled = [], None
        for builder in (SuccinctGraphBuilder(), PooledGraphBuilder()):
            normal = builder.uniform('normal')
            done = builder.uniform('contracted')
            selected = builder.uniform('Rdx', done)
            pattern = ('S', '_')
            rows = ((pattern, (1,)), (tuple(['S', '_']), (1,)))
            target = builder.match(pattern, selected, normal)
            target = builder.rows(rows, target, normal)
            target = builder.inverse_rows(rows, target, normal)
            target = builder.descent(rows, target)
            target = builder.ascent(rows, target)
            # Zero-width matches still occupy a pool entry, no interval.
            self.assertEqual(builder.match('_', selected, normal), selected)
            tables.append(builder.finish(builder.root(target)))
            if type(builder) is PooledGraphBuilder:
                pooled = builder
        graph_equal(self, *tables)
        self.assertEqual(tables[0].metadata_records, tables[1].metadata_records)
        probes = [item for item in reachable(tables[1]) if type(item) is SuccinctProbeTable]
        self.assertEqual(len(probes), 1)
        self.assertEqual(pooled.pool_statistics.probe_entries, 2)
        self.assertGreater(pooled.pool_statistics.probe_hits, 0)
        reference = weakref.ref(pooled._pool)
        del pooled, builder
        gc.collect()
        self.assertIsNone(reference())
        graph_equal(self, *tables)

    def test_finished_code_contains_only_existing_exact_frozen_data(self):
        table, stats = compile_with_statistics(Program(('01',)))
        self.assertIs(type(table), SuccinctSelectorTable)
        self.assertEqual(tuple(field.name for field in fields(table)), ('blocks', 'start'))
        for item in reachable(table):
            if any(type(item) is primitive for primitive in (int, str, type(None), tuple)):
                continue
            self.assertTrue(is_dataclass(item))
            self.assertTrue(item.__dataclass_params__.frozen)
            self.assertFalse(hasattr(item, '__dict__'))
            self.assertNotEqual(type(item).__module__, 's_only.pooled_selector')
        self.assertGreater(stats.descriptor_hits, 0)
        self.assertGreater(stats.probe_hits, 0)
        # Every existing validator still accepts the shared finished objects.
        SuccinctSelectorTable.__post_init__(table)


class PooledProgramTests(unittest.TestCase):
    PROGRAMS = (('01',), ('1', ''), ('01', '', '01'),
                ('10', '1', '', '10'), ('01', '', '1', '01', '001'))

    @classmethod
    def setUpClass(cls):
        cls.tables = [(unpooled_compile(Program(words)), compile_with_statistics(Program(words)))
                      for words in cls.PROGRAMS]

    def test_exact_code_equality_counts_and_all_interval_boundaries(self):
        for words, (original, (pooled, stats)) in zip(self.PROGRAMS, self.tables):
            with self.subTest(appendants=words):
                self.assertEqual(original, pooled)
                self.assertEqual(original.metadata_records, pooled.metadata_records)
                self.assertEqual(original.lookup_depth_bound, pooled.lookup_depth_bound)
                old_objects, new_objects = list(reachable(original)), list(reachable(pooled))
                for kind in (_Descriptor, SuccinctProbeTable):
                    self.assertLess(sum(type(x) is kind for x in new_objects),
                                    sum(type(x) is kind for x in old_objects))
                for block in original.blocks:
                    for control in (block.origin, (block.origin + block.stop) // 2, block.stop - 1):
                        self.assertEqual(original.status(control), pooled.status(control))
                        for obs in OBSERVATIONS:
                            self.assertEqual(original.transition(control, *obs), pooled.transition(control, *obs))
                self.assertGreater(stats.descriptor_hits, stats.descriptor_entries)

    def test_first_three_native_selections_preserve_every_microtick(self):
        for words, (original, (pooled, _)) in zip(self.PROGRAMS, self.tables):
            with self.subTest(appendants=words):
                term = encode(Program(words), '11')
                for _ in range(3):
                    a = Configuration(original.start, Cursor.at(term))
                    b = Configuration(pooled.start, Cursor.at(term))
                    for ticks in range(200_001):
                        self.assertEqual(a.control, b.control)
                        self.assertIs(a.cursor.focus, b.cursor.focus)
                        self.assertEqual(a.cursor.path, b.cursor.path)
                        if original.status(a.control) is not None:
                            break
                        self.assertLess(ticks, 200_000, 'external microtick cap')
                        a, b = step(original, a), step(pooled, b)
                    self.assertEqual(original.status(a.control), 'Rdx')
                    self.assertEqual(pooled.status(b.control), 'Rdx')
                    aa, bb = step(original, a), step(pooled, b)
                    self.assertEqual(original.status(aa.control), 'contracted')
                    self.assertEqual(pooled.status(bb.control), 'contracted')
                    self.assertEqual(aa.cursor.path, bb.cursor.path)
                    self.assertEqual(erase(aa.cursor), erase(bb.cursor))
                    term = erase(aa.cursor)

    def test_public_scope_caps_and_exact_boundaries(self):
        for bounds in ({'max_phases': 6}, {'max_phases': True}, {'max_appendant_bits': 9},
                       {'max_appendant_bits': True}, {'max_metadata_records': 0},
                       {'max_compile_seconds': float('nan')}, {'max_pool_records': None},
                       {'max_pool_records': True}, {'max_pool_records': 0}):
            with self.subTest(bounds=bounds), self.assertRaises(ValueError):
                compile_table(Program(('',)), **bounds)
        for source, bounds in ((('',) * 6, {}), (('1' * 9,), {}),
                               (('',) * 3, {'max_phases': 2}), (('01',), {'max_appendant_bits': 1}),
                               (('',), {'max_metadata_records': 7}), (('',), {'max_pool_records': 1})):
            with self.subTest(source=source, bounds=bounds), self.assertRaises(CompilationLimit):
                compile_table(Program(source), **bounds)
        original, (table, stats) = self.tables[0]
        self.assertEqual(compile_table(Program(self.PROGRAMS[0]),
                         max_metadata_records=table.metadata_records,
                         max_pool_records=stats.peak_pool_entries), table)
        for bounds in ({'max_metadata_records': table.metadata_records - 1},
                       {'max_pool_records': stats.peak_pool_entries - 1}):
            with self.assertRaises(CompilationLimit):
                compile_table(Program(self.PROGRAMS[0]), **bounds)

    def test_plain_source_validation_precedes_hashing(self):
        class Word(str):
            pass
        class Words(tuple):
            pass
        class FakeProgram(Program):
            pass
        for source in (None, ('01',), FakeProgram(('01',))):
            with self.assertRaises(TypeError):
                compile_table(source)
        for words in ((), [], Words(('01',)), (Word('01'),), (True,), ('x',)):
            source = object.__new__(Program)
            object.__setattr__(source, 'appendants', words)
            with self.assertRaises(ValueError):
                compile_table(source)


class PooledMeasurementTests(unittest.TestCase):
    def test_value_digest_ignores_identity_but_sees_every_field(self):
        from tools.pooled_selector_report import code_sha256
        leaf = _Descriptor('S', None, None, 1, 1, 1)
        copy = replace(leaf)
        self.assertIsNot(leaf, copy)
        self.assertEqual(code_sha256((leaf, leaf)), code_sha256((leaf, copy)))
        self.assertNotEqual(code_sha256((leaf,)), code_sha256((leaf, leaf)))
        self.assertNotEqual(code_sha256((leaf,)),
                            code_sha256((replace(leaf, ticks=2),)))

    def test_reachable_objects_and_probe_reference_slots_are_distinct(self):
        from tools.pooled_selector_report import probe_reference_slots, reachable_values
        builder = PooledGraphBuilder()
        normal = builder.uniform('normal')
        target = builder.match(('S', '_'), normal, normal)
        start = builder.match(tuple(['S', '_']), target, normal)
        table = builder.finish(start)
        self.assertEqual(probe_reference_slots(table), 2)
        self.assertEqual(sum(type(value) is SuccinctProbeTable
                             for value in reachable_values(table)), 1)
        self.assertEqual(builder.pool_statistics.probe_entries, 1)

    def test_invalid_measurement_deadlines_do_not_launch_workers(self):
        from tools.pooled_selector_report import report
        for limit in (None, True, 0, -1, float('nan'), float('inf'), 161):
            with self.subTest(limit=limit), self.assertRaises(ValueError):
                report(max_seconds=limit)


if __name__ == '__main__':
    unittest.main()
