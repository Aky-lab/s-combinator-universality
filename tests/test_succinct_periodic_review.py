"""Independent review of the bounded positive-period succinct entry point.

The exhaustive comparison below uses a new all-empty three-phase program,
not one of the four archived graph witnesses. Run with an external envelope:
  timeout 180s sh -c 'ulimit -v 1048576; exec python -m unittest discover -s tests -p test_succinct_periodic_review.py -v'
All counters, source checks, and process budgets are external to the selector.
"""
from contextlib import ExitStack
from dataclasses import fields, replace
import gc
import inspect
import math
import sys
import time
import unittest
from unittest.mock import patch
import weakref

from s_only.cts import Program
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit, compile_table as dense_compile
from s_only.reduction import contract_at, redex_paths
from s_only.root_selector import erase, step
from s_only.selector_parts.graph import Command
from s_only.succinct_periodic import compile_table
from s_only.succinct_probes import SuccinctProbeTable, compile_pattern
from s_only.succinct_rows import SuccinctRowsTable, compile_rows
from s_only.succinct_selector import (
    SuccinctGraphBuilder, SuccinctSelectorTable, _DirectRow, _Fragment,
    compile_table as small_compile,
)
from s_only.succinct_walkers import (
    SuccinctInverseRowsTable, SuccinctWalkerTable, compile_ascent,
    compile_descent, compile_inverse_rows,
)
from s_only.terms import App, S


def forged_copy(value, **changes):
    """Bypass dataclass construction solely to exercise nested revalidation."""
    result = object.__new__(type(value))
    for field in fields(value):
        object.__setattr__(result, field.name,
                           changes.get(field.name, getattr(value, field.name)))
    return result


class SuccinctPeriodicReviewTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.five = compile_table(Program(('',) * 5), max_appendant_bits=0)

    def test_api_defaults_and_keyword_only_resource_controls(self):
        signature = inspect.signature(compile_table)
        self.assertEqual({name: parameter.default for name, parameter in
                          signature.parameters.items() if name != 'program'},
                         {'max_phases': 5, 'max_appendant_bits': 8,
                          'max_metadata_records': 250000, 'max_compile_seconds': 10})
        for name, parameter in signature.parameters.items():
            if name != 'program':
                self.assertIs(parameter.kind, inspect.Parameter.KEYWORD_ONLY)
        old = inspect.signature(small_compile)
        self.assertNotIn('max_phases', old.parameters)
        self.assertEqual(old.parameters['max_metadata_records'].default, 100000)
        self.assertEqual(old.parameters['max_compile_seconds'].default, 10)

    def test_empty_phase_limit_and_plain_input_checks_precede_any_graph_work(self):
        class ExplodingTuple(tuple):
            def __len__(self):
                raise AssertionError('subclass length evaluated')

        class ExplodingWord(str):
            def __len__(self):
                raise AssertionError('subclass length evaluated')

        source = Program(('',))
        with patch('s_only.succinct_periodic._assemble_program',
                   side_effect=AssertionError('graph work started')):
            for words in (ExplodingTuple(('',)), [], (), (ExplodingWord('0'),),
                          (False,), ('2',), ('\u200b',)):
                with self.subTest(words=type(words)), self.assertRaises(ValueError):
                    compile_table(forged_copy(source, appendants=words))
            with self.assertRaises(CompilationLimit):
                compile_table(Program(('',) * 6), max_appendant_bits=0)
            with self.assertRaises(CompilationLimit):
                compile_table(Program(('',) * 5), max_phases=4)
            with self.assertRaises(CompilationLimit):
                compile_table(Program(('111111111',)))

    def test_clock_budgets_must_be_representable_by_a_finite_clock(self):
        # Oversized plain integers must be cleanly rejected, not leak the
        # OverflowError raised by math.isfinite's implicit float conversion.
        with patch('s_only.program_selector_parts.patterns.PatternFamily',
                   side_effect=AssertionError('source patterns constructed')):
            for seconds in (10 ** 400, -(10 ** 400), float('inf'), float('-inf'),
                            float('nan'), 0, -0.0, True, None):
                with self.subTest(seconds_type=type(seconds)), self.assertRaises(ValueError):
                    compile_table(Program(('',)), max_compile_seconds=seconds)
            with patch('s_only.succinct_selector.time.monotonic',
                       return_value=sys.float_info.max):
                with self.assertRaisesRegex(ValueError, 'finite deadline'):
                    compile_table(Program(('',)), max_compile_seconds=sys.float_info.max)
        with patch('s_only.succinct_selector.time.monotonic', return_value=0):
            for seconds in (1, 0.5, 10 ** 308, sys.float_info.max):
                builder = SuccinctGraphBuilder(max_compile_seconds=seconds)
                self.assertTrue(math.isfinite(builder._deadline))
                self.assertGreater(builder._deadline, 0)

    def test_soft_deadline_at_fragment_completion_and_final_validation(self):
        now = [0.0]
        with patch('s_only.succinct_selector.time.monotonic', side_effect=lambda: now[0]):
            builder = SuccinctGraphBuilder(max_compile_seconds=1)
            normal = builder.uniform('normal')

            def compile_then_expire(pattern):
                result = compile_pattern(pattern)
                now[0] = 1.0
                return result

            with patch('s_only.succinct_selector.compile_pattern',
                       side_effect=compile_then_expire):
                with self.assertRaises(CompilationLimit):
                    builder.match('S', normal, normal)
            self.assertEqual(builder.state_count, 1)

        now[0] = 0.0
        with patch('s_only.succinct_selector.time.monotonic', side_effect=lambda: now[0]):
            builder = SuccinctGraphBuilder(max_compile_seconds=1)
            normal = builder.uniform('normal')
            original = SuccinctSelectorTable.__post_init__

            def validate_then_expire(table):
                original(table)
                now[0] = 1.0

            with patch.object(SuccinctSelectorTable, '__post_init__', validate_then_expire):
                with self.assertRaises(CompilationLimit):
                    builder.finish(normal)

    def test_nested_corruption_is_rejected_in_every_fragment_family(self):
        pattern = (('S', '_'), ('_', 'S'))
        rows = ((pattern, (0, 1)),)
        fragments = (compile_pattern(pattern), compile_rows(rows),
                     compile_inverse_rows(rows), compile_descent(rows),
                     compile_ascent(rows))
        normal = _DirectRow(0, (Command('normal'),) * 6)
        for fragment in fragments:
            with self.subTest(fragment=type(fragment)):
                base = fragment.probe if type(fragment) is SuccinctWalkerTable else fragment
                probe = base if type(base) is SuccinctProbeTable else base.patterns[0].probe
                last = probe.nodes[-1]
                for field, invalid in (('kind', []), ('left', True), ('right', probe.root),
                                       ('width', last.width + 1), ('ticks', -1),
                                       ('height', last.height + 1)):
                    corrupted_probe = forged_copy(probe, nodes=probe.nodes[:-1] +
                                                   (replace(last, **{field: invalid}),))
                    if type(base) is SuccinctProbeTable:
                        corrupted = corrupted_probe
                    else:
                        code = replace(base.patterns[0], probe=corrupted_probe)
                        corrupted = forged_copy(base, patterns=(code,) + base.patterns[1:])
                    if type(fragment) is SuccinctWalkerTable:
                        corrupted = forged_copy(fragment, probe=corrupted)
                    with self.subTest(field=field), self.assertRaises(ValueError):
                        SuccinctSelectorTable((normal, _Fragment(1, corrupted, 0, 0)), 0)

    def test_unused_nested_code_and_unused_walker_continuation_are_validated(self):
        rows = compile_rows(((('S', '_'), (1,)),))
        unused = replace(rows.patterns[0], failure_ticks=True)
        corrupted = forged_copy(rows, patterns=rows.patterns + (unused,))
        normal = _DirectRow(0, (Command('normal'),) * 6)
        with self.assertRaises(ValueError):
            SuccinctSelectorTable((normal, _Fragment(1, corrupted, 0, 0)), 0)
        walker = compile_ascent(())
        self.assertEqual(walker.state_count, 2)
        table = SuccinctSelectorTable((normal, _Fragment(1, walker, 0, 0)), 0)
        self.assertEqual(table.state_count, 2)
        self.assertEqual(table.transition(1, 'S', 'root'), Command('stay', 0))
        for unused_target in (None, True, -1, 2):
            with self.subTest(target=unused_target), self.assertRaises(ValueError):
                SuccinctSelectorTable((normal, _Fragment(1, walker, unused_target, 0)), 0)

    def test_malformed_last_direct_row_is_rejected_before_earlier_rdx_comparisons(self):
        class Poison:
            def __eq__(self, other):
                raise AssertionError('unvalidated equality evaluated')

            def __ne__(self, other):
                raise AssertionError('unvalidated inequality evaluated')

        target = _DirectRow(1, (Command('contracted'),) * 6)
        for invalid in (Poison(), Command('contracted', Poison()),
                        forged_copy(Command('contracted'), command=Poison())):
            bad_target = replace(target, row=target.row[:5] + (invalid,))
            with self.subTest(value=type(invalid)), self.assertRaises(ValueError):
                SuccinctSelectorTable((_DirectRow(0, (Command('Rdx', 1),) * 6),
                                       bad_target), 0)

    def test_all_block_boundaries_and_observations_reject_nonplain_queries(self):
        table = self.five
        class Int(int):
            pass
        class Text(str):
            pass
        for control in (-1, table.state_count, True, 0.0, Int(table.start), None):
            with self.subTest(control=control), self.assertRaises(ValueError):
                table.status(control)
            with self.subTest(control=control), self.assertRaises(ValueError):
                table.transition(control, 'S', 'root')
        observations = ((Text('S'), 'root'), ('S', Text('root')), ('S', None),
                        ('application', 'left'), ('s', 'L'))
        for block in table.blocks:
            for control in {block.origin, block.stop - 1}:
                for observation in observations:
                    with self.assertRaises(ValueError):
                        table.transition(control, *observation)
                for observation in OBSERVATIONS:
                    instruction = table.transition(control, *observation)
                    if instruction.next_state is not None:
                        self.assertIs(type(instruction.next_state), int)
                        self.assertTrue(0 <= instruction.next_state < table.state_count)

    def test_source_is_collectible_and_retained_metadata_slots_have_exact_threshold(self):
        program = Program(('0', '', '0'))
        reference = weakref.ref(program)
        table = compile_table(program)
        del program
        gc.collect()
        self.assertIsNone(reference())
        slots = table.metadata_records
        self.assertEqual(compile_table(Program(('0', '', '0')),
                                       max_metadata_records=slots), table)
        with self.assertRaises(CompilationLimit):
            compile_table(Program(('0', '', '0')), max_metadata_records=slots - 1)
        # A failed construction has no cache or partially built result to reuse.
        self.assertEqual(compile_table(Program(('0', '', '0'))), table)

    def test_isolated_five_phase_runtime_on_arbitrary_occurrence_trees(self):
        table = self.five
        redex = App(App(App(S, S), S), S)
        terms = (S, App(S, S), App(App(S, S), S), redex,
                 App(S, redex), App(redex, S), App(redex, redex))
        with ExitStack() as stack:
            for target in ('s_only.succinct_periodic.compile_table',
                           's_only.succinct_selector._assemble_program',
                           's_only.program_selector_parts.patterns.PatternFamily',
                           's_only.succinct_selector.time.monotonic',
                           's_only.cts.step', 's_only.encoding.encode', 'builtins.open'):
                stack.enter_context(patch(target, side_effect=AssertionError('runtime dependency')))
            for term in terms:
                outcomes = []
                for _ in range(2):
                    state = Configuration(table.start, Cursor.at(term))
                    for ticks in range(200001):
                        status = table.status(state.control)
                        if status is not None:
                            break
                        self.assertLess(ticks, 200000, 'external microtick ceiling')
                        self.assertIs(state.cursor.root, term)
                        state = step(table, state)
                    else:
                        self.fail('external microtick ceiling')
                    if status == 'normal':
                        self.assertEqual(list(redex_paths(term)), [])
                        self.assertEqual(erase(state.cursor), term)
                        self.assertIs(step(table, state), state)
                    else:
                        self.assertEqual(status, 'Rdx')
                        self.assertIn(state.cursor.path, list(redex_paths(term)))
                        terminal = step(table, state)
                        self.assertEqual(erase(terminal.cursor), contract_at(term, state.cursor.path))
                        self.assertEqual(table.status(terminal.control), 'contracted')
                        self.assertIs(step(table, terminal), terminal)
                    outcomes.append((state.control, state.cursor.path, ticks))
                self.assertEqual(*outcomes)

    def test_nonarchived_empty_three_phase_full_index_comparison(self):
        program = Program(('', '', ''))
        compact = compile_table(program, max_appendant_bits=0)
        original = dense_compile(program, required_period=None, max_states=500000,
                                 max_appendant_bits=0, max_phases=3)
        self.assertEqual((compact.state_count, compact.start, compact.metadata_records),
                         (420724, 376900, 52338))
        self.assertEqual((compact.state_count, compact.start),
                         (len(original.states), original.start))
        deadline = time.monotonic() + 90
        counts = {'normal': 0, 'contracted': 0, 'Rdx': 0, None: 0}
        checked = 0
        # Reverse control/observation order independently exercises pure random
        # access instead of mirroring the forward archive verifier's traversal.
        for control in reversed(range(compact.state_count)):
            if control % 1024 == 0:
                self.assertLess(time.monotonic(), deadline, 'external comparison deadline')
            status = compact.status(control)
            self.assertEqual(status, original.status(control))
            counts[status] += 1
            for observation in reversed(OBSERVATIONS):
                self.assertEqual(compact.transition(control, *observation),
                                 original.transition(control, *observation))
                checked += 1
        self.assertEqual(checked, 2524344)
        self.assertEqual(counts, {'normal': 1, 'contracted': 1, 'Rdx': 1, None: 420721})


if __name__ == '__main__':
    unittest.main()
