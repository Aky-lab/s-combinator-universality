"""Count/start differential checks; no claim about controller transitions."""
from contextlib import ExitStack
import gc
import itertools
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from s_only.compilation_cost import compilation_cost
from s_only.controller_size import CountingGraphBuilder, controller_size
from s_only.cts import Program
from s_only.probes import HOLE, LITERAL_S, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit, compile_table
from s_only.selector_parts.graph import Command, GraphBuilder
from s_only.succinct_periodic import compile_table as succinct_compile
from s_only.succinct_selector import _assemble_program


PROGRAMS = (('01',), ('1', ''), ('01', '', '01'),
            ('10', '1', '', '10'), ('01', '', '1', '01', '001'))
EXPECTED = ((129268, 111742), (257299, 227379), (694400, 621444),
            (1201863, 1086283), (2134486, 1945270))


def addresses(pattern):
    result, pending = [], [(pattern, ())]
    while pending:
        node, address = pending.pop()
        result.append(address)
        if type(node) is tuple:
            pending.extend(((node[0], address + (0,)), (node[1], address + (1,))))
    return result


class ControllerSizeTests(unittest.TestCase):
    def compare_fragment(self, name, source):
        outcomes = []
        for builder in (GraphBuilder(), CountingGraphBuilder()):
            no, yes = builder.uniform('normal'), builder.uniform('contracted')
            method = getattr(builder, name)
            start = method(source, yes) if name in ('descent', 'ascent') else method(source, yes, no)
            count = len(builder.states) if type(builder) is GraphBuilder else builder.finish(start).state_count
            outcomes.append((count, start))
        self.assertEqual(*outcomes, (name, source))

    def test_all_small_patterns_and_scoped_row_addresses(self):
        base = (HOLE, LITERAL_S)
        small = base + tuple(itertools.product(base, repeat=2))
        patterns = small + tuple(itertools.product(small, repeat=2))
        for pattern in patterns:
            self.compare_fragment('match', pattern)
            for address in addresses(pattern):
                self.compare_fragment('rows', ((pattern, address),))
                if address:
                    for kind in ('inverse_rows', 'descent', 'ascent'):
                        self.compare_fragment(kind, ((pattern, address),))

    def test_priorities_repeated_rows_and_zero_width_start_resets(self):
        options = (('_', ()), ('S', ()), (('_', '_'), ()),
                   (('S', '_'), (0,)), (('_', 'S'), (1,)))
        for count in range(4):
            for rows in itertools.product(options, repeat=count):
                self.compare_fragment('rows', rows)
        strict = options[-2:]
        for count in range(4):
            for rows in itertools.product(strict, repeat=count):
                for kind in ('inverse_rows', 'descent', 'ascent'):
                    self.compare_fragment(kind, rows)
        builder = CountingGraphBuilder()
        no, yes = builder.uniform('normal'), builder.uniform('contracted')
        self.assertEqual(builder.rows((('_', ()), ('S', ())), yes, no), yes)
        self.assertEqual(builder.state_count, 3)  # The unreachable S row stays.
        self.assertEqual(builder.rows((('S', ()), ('_', ())), yes, no), 3)

    def test_empty_walkers_keep_unreachable_feedback(self):
        builder = CountingGraphBuilder()
        done = builder.uniform('normal')
        for kind in ('rows', 'inverse_rows'):
            self.assertEqual(getattr(builder, kind)((), done, done), done)
            self.assertEqual(builder.state_count, 1)
        self.assertEqual(builder.descent((), done), done)
        self.assertEqual(builder.state_count, 2)
        self.assertEqual(builder.ascent((), done), done)
        self.assertEqual(builder.state_count, 3)
        self.assertEqual(builder.finish(done).direct_states, 1)

    def test_deep_shared_dag_uses_occurrence_width_not_occurrence_expansion(self):
        pattern = 'S'
        for _ in range(4096):
            pattern = (pattern, pattern)
        builder = CountingGraphBuilder(max_pattern_work=20_000)
        no, yes = builder.uniform('normal'), builder.uniform('contracted')
        start = builder.match(pattern, yes, no)
        expected = 7 * 2 ** 4096 - 6
        self.assertEqual(builder.state_count, expected + 2)
        self.assertEqual(start, expected + 1)
        self.assertEqual(builder.pattern_nodes, 4097)
        self.assertLess(builder.pattern_work, 20_000)
        self.assertEqual(builder.reserve(), expected + 2)
        self.assertEqual(len(builder._direct), 3)
        builder.jump(expected + 2, start)
        self.assertEqual(builder.finish(start).direct_states, 3)

    def test_identity_cache_lifetimes_and_repeated_row_occurrences(self):
        builder = CountingGraphBuilder()
        no, yes = builder.uniform('normal'), builder.uniform('contracted')
        for index in range(2000):
            # Fresh, subsequently discardable objects must never inherit a
            # stale width from an earlier fragment's id-keyed cache.
            pattern = ('S', '_') if index % 2 else (('_', '_'), 'S')
            width = 7 if index % 2 else 13
            before = builder.state_count
            builder.rows(((pattern, ()), (pattern, ())), yes, no)
            self.assertEqual(builder.state_count - before, 2 * width)

    def test_mixed_direct_reservation_and_fragment_emission_order(self):
        outcomes = []
        for builder in (GraphBuilder(), CountingGraphBuilder()):
            normal = builder.uniform('normal')
            contracted = builder.uniform('contracted')
            selected = builder.uniform('Rdx', contracted)
            before, missed = builder.reserve(), builder.reserve()
            hit = builder.rows((('_', ()), ('S', ())), selected, missed)
            ascent = builder.ascent(((('_', '_'), (1,)),), hit)
            descent = builder.descent(((('_', '_'), (0,)),), ascent)
            inverse = builder.inverse_rows(((('_', '_'), (1,)),), descent, missed)
            builder.jump(before, builder.path((1, 0), inverse))
            builder.states[missed] = tuple(Command('stay', normal) if side == 'root'
                                          else Command('U', missed) for _, side in OBSERVATIONS)
            start = builder.root(builder.node_test(normal, before))
            count = len(builder.finish()) if type(builder) is GraphBuilder else builder.finish(start).state_count
            outcomes.append((count, start))
        self.assertEqual(*outcomes)

    def test_sparse_reservations_discard_rows_and_reject_unfilled_controls(self):
        builder = CountingGraphBuilder()
        state = builder.reserve()
        self.assertIsNone(builder.states[state])
        for operation in (lambda: len(builder.states), lambda: tuple(builder.states)):
            with self.assertRaises(TypeError):
                operation()
        with self.assertRaises(ValueError):
            builder.finish(state)
        with self.assertRaises(ValueError):
            builder.states[True] = (Command('normal'),) * 6
        builder.states[state] = (Command('normal'),) * 6
        self.assertIs(builder._direct[state], True)
        with self.assertRaises(ValueError):
            builder.jump(state, state)
        with self.assertRaises(TypeError):
            builder.embed(None, state, state)
        for bad in (True, -1, 1, None):
            with self.assertRaises(ValueError):
                builder.finish(bad)

    def test_pattern_address_and_strictness_validation(self):
        for source in (None, [], ('S',), ('S', 'S', 'S'), 'x', ('S', object())):
            with self.assertRaises(ValueError):
                CountingGraphBuilder().match(source, 0, 0)
        for rows in ((['_', ()],), (('_', (0,)),), (('S', [0]),),
                     ((('_', '_'), (True,)),), ((('_', '_'), (2,)),)):
            with self.assertRaises(ValueError):
                CountingGraphBuilder().rows(rows, 0, 0)
        for kind in ('inverse_rows', 'descent', 'ascent'):
            with self.assertRaises(ValueError):
                getattr(CountingGraphBuilder(), kind)((('_', ()),), *([0] if kind != 'inverse_rows' else [0, 0]))

    def test_resource_budgets_are_checked(self):
        for bad in (0, -1, True, None, 1.0):
            with self.assertRaises(ValueError):
                CountingGraphBuilder(max_pattern_work=bad)
        for bad in (0, -1, True, None, float('nan'), float('inf'), 10 ** 1000):
            with self.assertRaises(ValueError):
                CountingGraphBuilder(max_compile_seconds=bad)
        with self.assertRaises(CompilationLimit):
            CountingGraphBuilder(max_pattern_work=1).match(('S', '_'), 0, 0)
        with patch('s_only.controller_size.time.monotonic', side_effect=(0.0, 2.0)):
            builder = CountingGraphBuilder(max_compile_seconds=1)
            with self.assertRaises(CompilationLimit):
                builder.reserve()
        with patch('s_only.program_selector_parts.patterns.PatternFamily', side_effect=AssertionError):
            with self.assertRaises(CompilationLimit):
                controller_size(Program(('', '') * 3), max_phases=5)
            with self.assertRaises(CompilationLimit):
                controller_size(Program(('01',)), max_appendant_bits=1)

    def test_program_validation(self):
        for bad in (None, ('01',), ['01']):
            with self.assertRaises(TypeError):
                controller_size(bad)
        for words in ([], (), ('012',), (True,)):
            forged = object.__new__(Program)
            object.__setattr__(forged, 'appendants', words)
            with self.assertRaises(ValueError):
                controller_size(forged)

    def test_no_table_compiler_is_called_and_shared_assembly_agrees(self):
        with ExitStack() as stack:
            for module in ('s_only.probes', 's_only.walkers', 's_only.selector_parts.graph',
                           's_only.succinct_probes', 's_only.succinct_rows', 's_only.succinct_walkers'):
                for name in ('compile_pattern', 'compile_rows', 'compile_inverse_rows',
                             'compile_descent', 'compile_ascent'):
                    target = module + '.' + name
                    stack.enter_context(patch(target, create=True, side_effect=AssertionError('table compiler called')))
            result = controller_size(Program(('01',)))
            same = _assemble_program(Program(('01',)), max_metadata_records=1,
                                     max_compile_seconds=120, _builder=CountingGraphBuilder())
        self.assertEqual((result.state_count, result.start), (same.state_count, same.start))
        self.assertEqual(result.direct_states + sum(x.state_count for x in result.fragments), result.state_count)
        self.assertEqual(sum(x.state_count for x in result.stages), result.state_count)
        position = 0
        for stage in result.stages:
            self.assertEqual(stage.first_state, position)
            position += stage.state_count
        self.assertEqual(result.stages[-1].start, result.start)

    def test_selected_action_component_agrees_with_source_only_formula(self):
        from s_only.program_selector_parts.patterns import PatternFamily
        for words in PROGRAMS + (('',), ('', '', '')):
            program = Program(words)
            shapes = PatternFamily(program, required_period=None)
            builder = CountingGraphBuilder()
            no, yes = builder.uniform('normal'), builder.uniform('contracted')
            before = builder.state_count
            builder.rows(shapes.selected_action_rows(), yes, no)
            self.assertEqual(builder.state_count - before,
                             compilation_cost(program).selected_action_embedded_states)

    def test_existing_periods_one_through_five_against_succinct_and_materialized(self):
        # Serial references, released before the next program. Run this suite
        # with the documented external 180-second / 1-GiB process envelope.
        for words, expected in zip(PROGRAMS, EXPECTED):
            with self.subTest(words=words):
                program = Program(words)
                counted = controller_size(program)
                self.assertEqual((counted.state_count, counted.start), expected)
                succinct = succinct_compile(program, max_compile_seconds=30)
                self.assertEqual((counted.state_count, counted.start), (succinct.state_count, succinct.start))
                del succinct
                gc.collect()
                materialized = compile_table(program, required_period=None, max_states=3_000_000,
                                             max_appendant_bits=8, max_phases=5)
                self.assertEqual((counted.state_count, counted.start),
                                 (len(materialized.states), materialized.start))
                del materialized
                gc.collect()

    def test_archived_materialized_counts_cover_additional_programs(self):
        root = Path(__file__).resolve().parents[1]
        for filename in ('two_phase_programs.json', 'positive_period_programs.json'):
            for record in json.loads((root / 'results' / filename).read_text())['programs']:
                result = controller_size(Program(tuple(record['appendants'])))
                self.assertEqual(result.state_count, record['finite_control_states'])


if __name__ == '__main__':
    unittest.main()
