"""Independent field, graph, resource, and measurement review of code sharing.

Standard library only. External test envelope:
  timeout 180s sh -c 'ulimit -v 1048576; exec python -m unittest tests.test_pooled_selector_review -v'
The optional frozen-checkout comparison is run separately from these portable
regressions. These tests never materialize a large virtual controller.
"""
from contextlib import ExitStack
from dataclasses import fields, is_dataclass, replace
import gc
import inspect
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch
import weakref

from s_only.cts import Program
from s_only.encoding import encode
from s_only.pooled_selector import (
    _CodePool, PooledGraphBuilder, compile_table, compile_with_statistics,
)
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit
from s_only.root_selector import erase, step
from s_only.succinct_periodic import compile_table as unpooled_compile
from s_only.succinct_probes import _Descriptor, SuccinctProbeTable, compile_pattern
from s_only.succinct_rows import compile_rows
from s_only.succinct_selector import SuccinctGraphBuilder
from s_only.succinct_walkers import compile_inverse_rows, compile_descent, compile_ascent
from s_only.terms import App, S
from tools import pooled_selector_report as measurement


def assert_fields_equal(test, left, right):
    """Compare every exact record/tuple/scalar field without an object digest."""
    pending = [(left, right)]
    while pending:
        a, b = pending.pop()
        test.assertIs(type(a), type(b))
        if type(a) is tuple:
            test.assertEqual(len(a), len(b))
            pending.extend(zip(a, b))
        elif is_dataclass(a):
            pending.extend((getattr(a, field.name), getattr(b, field.name))
                           for field in fields(a))
        else:
            test.assertIn(type(a), (int, str, type(None)))
            test.assertEqual(a, b)


def forged(value, **changes):
    result = object.__new__(type(value))
    for field in fields(value):
        object.__setattr__(result, field.name,
                           changes.get(field.name, getattr(value, field.name)))
    return result


def all_addresses(pattern):
    pending = [(pattern, ())]
    while pending:
        node, address = pending.pop()
        yield address
        if type(node) is tuple:
            pending.extend(((node[0], address + (0,)), (node[1], address + (1,))))


class PooledSelectorReviewTests(unittest.TestCase):
    # Empty appendants, repeated words, and a differently distributed 8-bit cap.
    CASES = (('',), ('', '010'), ('0', '', '0'),
             ('', '11', '00', ''), ('10', '', '101', '', '001'))

    @classmethod
    def setUpClass(cls):
        cls.tables = [(unpooled_compile(Program(words)),
                       compile_with_statistics(Program(words))) for words in cls.CASES]

    def test_every_immutable_field_on_five_new_programs(self):
        for words, (old, (new, _)) in zip(self.CASES, self.tables):
            with self.subTest(words=words):
                assert_fields_equal(self, old, new)
                for name in ('state_count', 'start', 'metadata_records',
                             'lookup_depth_bound', 'linear_coefficient'):
                    self.assertEqual(getattr(old, name), getattr(new, name))
                for block in old.blocks:
                    for control in set((block.origin, block.stop - 1,
                                        (block.origin + block.stop) // 2)):
                        self.assertEqual(old.status(control), new.status(control))
                        for observation in reversed(OBSERVATIONS):
                            self.assertEqual(old.transition(control, *observation),
                                             new.transition(control, *observation))

    def test_all_controls_statuses_and_six_entries_for_empty_one_phase(self):
        old, (new, _) = self.tables[0]
        visited = 0
        statuses = {}
        for control in reversed(range(old.state_count)):
            status = old.status(control)
            self.assertEqual(status, new.status(control))
            statuses[status] = statuses.get(status, 0) + 1
            for observation in reversed(OBSERVATIONS):
                self.assertEqual(old.transition(control, *observation),
                                 new.transition(control, *observation))
                visited += 1
        self.assertEqual(visited, 6 * old.state_count)
        self.assertEqual({k: v for k, v in statuses.items() if k is not None},
                         {'normal': 1, 'contracted': 1, 'Rdx': 1})

    def test_exhaustive_small_patterns_and_addresses_preserve_components(self):
        leaves = ('_', 'S')
        shallow = leaves + tuple((a, b) for a in leaves for b in leaves)
        patterns = shallow + tuple((a, b) for a in shallow for b in shallow)
        pool = _CodePool(max_pool_records=10000)
        for pattern in patterns:
            old, new = compile_pattern(pattern), compile_pattern(pattern, _factory=pool)
            assert_fields_equal(self, old, new)
            for control in range(old.state_count):
                self.assertEqual(old.answer(control), new.answer(control))
                for obs in OBSERVATIONS:
                    self.assertEqual(old.transition(control, *obs), new.transition(control, *obs))
            for address in all_addresses(pattern):
                rows = ((pattern, address), ('_', ()), ('S', ()))
                compilers = [compile_rows]
                if address:
                    rows = ((pattern, address), (tuple(['_', '_']), (0,)))
                    compilers.extend((compile_inverse_rows, compile_descent, compile_ascent))
                for compiler in compilers:
                    old, new = compiler(rows), compiler(rows, _factory=pool)
                    assert_fields_equal(self, old, new)
                    self.assertEqual(old.start, new.start)
                    for control in range(old.state_count):
                        self.assertEqual(old.answer(control), new.answer(control))
                        for obs in OBSERVATIONS:
                            self.assertEqual(old.transition(control, *obs),
                                             new.transition(control, *obs))

    def test_runtime_is_independent_of_pool_clock_source_and_compilers(self):
        old, (new, _) = self.tables[-1]
        redex = App(App(App(S, S), S), S)
        terms = (S, App(S, S), redex, App(redex, redex),
                 encode(Program(self.CASES[-1]), '010'))
        retained = tuple(id(x) for x in measurement.reachable_values(new))
        with ExitStack() as stack:
            for target in ('s_only.pooled_selector._CodePool.descriptor',
                           's_only.pooled_selector._CodePool.probe',
                           's_only.pooled_selector.compile_table',
                           's_only.succinct_selector._assemble_program',
                           's_only.program_selector_parts.patterns.PatternFamily',
                           's_only.succinct_selector.time.monotonic',
                           's_only.cts.step', 's_only.encoding.encode', 'builtins.open'):
                stack.enter_context(patch(target, side_effect=AssertionError('runtime dependency')))
            for term in terms:
                for _ in range(3):
                    a, b = Configuration(old.start, Cursor.at(term)), Configuration(new.start, Cursor.at(term))
                    for ticks in range(200001):
                        self.assertEqual(a.control, b.control)
                        self.assertIs(a.cursor.focus, b.cursor.focus)
                        self.assertEqual(a.cursor.path, b.cursor.path)
                        self.assertEqual(old.status(a.control), new.status(b.control))
                        if old.status(a.control) is not None:
                            break
                        self.assertLess(ticks, 200000, 'external microtick cap')
                        a, b = step(old, a), step(new, b)
                    if old.status(a.control) == 'normal':
                        self.assertIs(step(old, a), a)
                        self.assertIs(step(new, b), b)
                        break
                    self.assertEqual(old.status(a.control), 'Rdx')
                    a, b = step(old, a), step(new, b)
                    self.assertEqual(old.status(a.control), 'contracted')
                    self.assertEqual(new.status(b.control), 'contracted')
                    self.assertEqual(a.cursor.path, b.cursor.path)
                    self.assertEqual(erase(a.cursor), erase(b.cursor))
                    term = erase(a.cursor)
        self.assertEqual(retained, tuple(id(x) for x in measurement.reachable_values(new)))

    def test_pool_source_and_builder_collect_with_table_and_statistics_alive(self):
        weak = []
        original = PooledGraphBuilder
        def capture(**kwargs):
            builder = original(**kwargs)
            weak.extend((weakref.ref(builder), weakref.ref(builder._pool)))
            return builder
        source = Program(('', ''))
        source_ref = weakref.ref(source)
        with patch('s_only.pooled_selector.PooledGraphBuilder', side_effect=capture):
            table, stats = compile_with_statistics(source)
        del source
        gc.collect()
        self.assertIsNone(source_ref())
        self.assertTrue(all(reference() is None for reference in weak))
        self.assertGreater(stats.peak_pool_entries, 0)
        table.transition(table.start, 'S', 'root')
        objects = tuple(measurement.reachable_values(table))
        self.assertTrue(all(type(value).__module__ != 's_only.pooled_selector'
                            for value in objects))

    def test_failed_pool_compile_is_collectible_and_does_not_poison_retry(self):
        weak = []
        original = PooledGraphBuilder
        def capture(**kwargs):
            builder = original(**kwargs)
            weak.extend((weakref.ref(builder), weakref.ref(builder._pool)))
            return builder
        with patch('s_only.pooled_selector.PooledGraphBuilder', side_effect=capture):
            with self.assertRaises(CompilationLimit):
                compile_table(Program(('',)), max_pool_records=2)
        gc.collect()
        self.assertTrue(all(reference() is None for reference in weak))
        self.assertEqual(compile_table(Program(self.CASES[0])), self.tables[0][1][0])

    def test_independent_compilations_do_not_retain_a_global_pool(self):
        first = self.tables[0][1][0]
        second = compile_table(Program(self.CASES[0]))
        ids = lambda table: {id(v) for v in measurement.reachable_values(table)
                             if type(v) in (_Descriptor, SuccinctProbeTable)}
        self.assertTrue(ids(first).isdisjoint(ids(second)))
        self.assertEqual(first, second)

    def test_hash_collisions_preserve_local_indices_and_exact_values(self):
        with patch.object(_Descriptor, '__hash__', return_value=0), \
             patch.object(SuccinctProbeTable, '__hash__', return_value=0):
            pool = _CodePool()
            patterns = ('S', '_', ('S', '_'), ('_', 'S'),
                        (('S', '_'), ('_', 'S')), (('S', '_'), ('S', '_')))
            probes = [compile_pattern(p, _factory=pool) for p in patterns]
            for p, probe in zip(patterns, probes):
                self.assertEqual(probe, compile_pattern(p))
                self.assertIs(probe, compile_pattern(p, _factory=pool))
            self.assertEqual(len({id(p) for p in probes}), len(patterns))
            self.assertEqual(pool.statistics().probe_entries, len(patterns))

    def test_invalid_keys_never_reach_hash_equality_or_subclass_callbacks(self):
        class Poison:
            def __hash__(self):
                raise AssertionError('hash')
            def __eq__(self, other):
                raise AssertionError('equality')
            def __lt__(self, other):
                raise AssertionError('ordering')
        class Int(int):
            __hash__ = Poison.__hash__
            __eq__ = Poison.__eq__
            __lt__ = Poison.__lt__
        class Text(str):
            __hash__ = Poison.__hash__
            __eq__ = Poison.__eq__
        class Tuple(tuple):
            def __len__(self):
                raise AssertionError('length')
            def __iter__(self):
                raise AssertionError('iteration')
        good = compile_pattern(('S', '_'))
        pool = _CodePool()
        invalid = [forged(good, nodes=Tuple(good.nodes)), forged(good, root=Int(good.root))]
        for name in ('kind', 'left', 'right', 'width', 'ticks', 'height'):
            invalid.append(forged(good, nodes=good.nodes[:-1] +
                                  (replace(good.nodes[-1], **{name: Poison()}),)))
        invalid.extend((forged(good, root=True),
                        forged(good, nodes=good.nodes[:-1] +
                               (replace(good.nodes[-1], kind=Text('pair')),))))
        with patch.object(SuccinctProbeTable, '__hash__', side_effect=AssertionError('table hash')):
            for bad in invalid:
                with self.assertRaises(ValueError):
                    pool.probe(bad)
        leaf = good.nodes[0]
        with patch.object(_Descriptor, '__hash__', side_effect=AssertionError('descriptor hash')):
            for name in ('kind', 'left', 'right', 'width', 'ticks', 'height'):
                with self.assertRaises(ValueError):
                    pool.descriptor(replace(leaf, **{name: Poison()}))
        self.assertEqual(pool.statistics().peak_pool_entries, 0)

    def test_equal_values_cannot_evade_referenced_slot_budget(self):
        # Two repeated S probes reference two records each plus one fragment;
        # neither their shared object nor its dictionary key makes slots free.
        builder = PooledGraphBuilder(max_metadata_records=13, max_pool_records=2)
        done = builder.uniform('normal')
        a = builder.match('S', done, done)
        b = builder.match('S', a, done)
        table = builder.finish(b)
        self.assertEqual(table.metadata_records, 13)
        self.assertEqual(builder.pool_statistics.peak_pool_entries, 2)
        self.assertEqual(builder.pool_statistics.probe_hits, 1)
        with self.assertRaisesRegex(CompilationLimit, 'metadata records'):
            builder.match('S', b, done)
        self.assertEqual(builder.finish(b), table)

    def test_unreachable_zero_width_values_consume_pool_entries(self):
        builder = PooledGraphBuilder(max_pool_records=2)
        done = builder.uniform('normal')
        self.assertEqual(builder.match('_', done, done), done)
        table = builder.finish(done)
        self.assertEqual(builder.pool_statistics.peak_pool_entries, 2)
        self.assertEqual(builder.pool_statistics.probe_entries, 1)
        self.assertFalse(any(type(x) is SuccinctProbeTable
                             for x in measurement.reachable_values(table)))
        with self.assertRaisesRegex(CompilationLimit, 'retained entries'):
            builder.match('S', done, done)
        self.assertEqual(builder.finish(done), table)

    def test_expired_pool_hits_do_not_bypass_soft_clock(self):
        now = [0.0]
        with patch('s_only.pooled_selector.time.monotonic', side_effect=lambda: now[0]):
            builder = PooledGraphBuilder(max_compile_seconds=1)
            done = builder.uniform('normal')
            first = builder.match('S', done, done)
            leaf = compile_pattern('S')
            now[0] = 1.0
            for request, value in ((builder._pool.descriptor, leaf.nodes[0]),
                                   (builder._pool.probe, leaf)):
                with self.assertRaisesRegex(CompilationLimit, 'soft compilation'):
                    request(value)
            with self.assertRaises(CompilationLimit):
                builder.match('S', first, done)
            with self.assertRaises(CompilationLimit):
                builder.finish(first)

    def test_existing_defaults_and_keyword_call_behavior_are_unchanged(self):
        self.assertEqual({name: p.default for name, p in
                          inspect.signature(unpooled_compile).parameters.items() if name != 'program'},
                         {'max_phases': 5, 'max_appendant_bits': 8,
                          'max_metadata_records': 250000, 'max_compile_seconds': 10})
        self.assertEqual(inspect.signature(SuccinctGraphBuilder).parameters['max_metadata_records'].default,
                         100000)
        for compiler in (compile_pattern, compile_rows, compile_inverse_rows,
                         compile_descent, compile_ascent):
            factory = inspect.signature(compiler).parameters['_factory']
            self.assertIs(factory.kind, inspect.Parameter.KEYWORD_ONLY)
            self.assertIsNone(factory.default)
            value = 'S' if compiler is compile_pattern else ()
            self.assertEqual(compiler(value), compiler(value, _factory=None))


class PooledMeasurementReviewTests(unittest.TestCase):
    def test_report_launches_each_mode_in_a_distinct_child_call(self):
        calls = []
        def fake_run(command, **kwargs):
            calls.append((command, kwargs))
            sample = dict.fromkeys(('state_count', 'start', 'intervals', 'referenced_metadata_slots',
                                    'probe_reference_slots', 'equality_distinct_probe_values'), 1)
            sample['immutable_value_code_sha256'] = 'same'
            return subprocess.CompletedProcess(command, 0, json.dumps(sample), '')
        with patch.object(measurement.subprocess, 'run', side_effect=fake_run), \
             patch.object(measurement.platform, 'platform', return_value='test-platform'):
            report = measurement.report(max_seconds=10)
        self.assertEqual(len(report['programs']), 5)
        self.assertEqual(len(calls), 10)
        self.assertEqual([command[-2:] for command, _ in calls],
                         [[str(i), mode] for i in range(5) for mode in ('unpooled', 'pooled')])
        for command, kwargs in calls:
            self.assertEqual(command[:4], [sys.executable, '-m', 'tools.pooled_selector_report', '--worker'])
            self.assertTrue(kwargs['check'])
            self.assertTrue(kwargs['capture_output'])
            self.assertTrue(0 < kwargs['timeout'] <= 10)

    def test_report_rejects_equal_counts_with_different_code_hashes(self):
        counter = [0]
        def fake_run(command, **kwargs):
            counter[0] += 1
            sample = dict.fromkeys(('state_count', 'start', 'intervals', 'referenced_metadata_slots',
                                    'probe_reference_slots', 'equality_distinct_probe_values'), 1)
            sample['immutable_value_code_sha256'] = str(counter[0])
            return subprocess.CompletedProcess(command, 0, json.dumps(sample), '')
        with patch.object(measurement.subprocess, 'run', side_effect=fake_run):
            with self.assertRaisesRegex(AssertionError, 'immutable_value_code_sha256'):
                measurement.report(max_seconds=10)
        self.assertEqual(counter[0], 2)

    def test_archived_metrics_are_consistent_and_not_mislabeled_as_bytes(self):
        path = Path(__file__).resolve().parents[1] / 'results' / 'pooled-selector.json'
        report = json.loads(path.read_text())
        self.assertIn('fresh process', report['method'])
        self.assertIn('not RSS', report['identity_caveat'])
        self.assertIn('not exact temporary bytes', report['peak_caveat'])
        for entry in report['programs']:
            a, b = entry['unpooled'], entry['pooled']
            for name in ('state_count', 'start', 'intervals', 'referenced_metadata_slots',
                         'probe_reference_slots', 'equality_distinct_probe_values',
                         'immutable_value_code_sha256'):
                self.assertEqual(a[name], b[name])
            for sample in (a, b):
                self.assertEqual(sample['compile_peak_minus_current_bytes'],
                                 sample['compile_tracemalloc_peak_bytes'] - sample['compile_tracemalloc_current_bytes'])
                self.assertGreaterEqual(sample['compile_peak_minus_current_bytes'], 0)
                self.assertGreater(sample['reachable_sys_getsizeof_bytes'],
                                   sample['reachable_descriptor_sys_getsizeof_bytes'])
            self.assertEqual(b['pool_peak_entries'],
                             b['pool']['descriptor_entries'] + b['pool']['probe_entries'])
            self.assertEqual(b['pool_descriptor_entries_absent_from_final_code'],
                             b['pool']['descriptor_entries'] - b['reachable_descriptors'])
            self.assertEqual(b['pool_probe_entries_absent_from_final_code'],
                             b['pool']['probe_entries'] - b['reachable_probe_tables'])
            self.assertLess(b['reachable_sys_getsizeof_bytes'], a['reachable_sys_getsizeof_bytes'])


if __name__ == '__main__':
    unittest.main()
