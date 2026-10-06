"""Bounded positive-period API, shared assembly and hostile metadata checks.

Large all-entry/digest and two-horizon comparisons are separate externally
capped experiments. This focused suite does not materialize a large graph.
"""
from contextlib import ExitStack
from dataclasses import fields, is_dataclass, replace
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from s_only.cts import Program
from s_only.encoding import encode
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit
from s_only.root_selector import erase, execute, step
from s_only.selector_parts.graph import Command
from s_only.succinct_periodic import compile_table
from s_only.succinct_probes import compile_pattern
from s_only.succinct_selector import (
    SuccinctGraphBuilder, SuccinctSelectorTable, _DirectRow, _Fragment,
    compile_table as small_compile,
)
from s_only.terms import App, S


ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = (('01', '', '01'), ('10', '1', '', '10'),
            ('01', '', '1', '01', '001'))
COUNTS = ((694400, 621444, 426, 70326),
          (1201863, 1086283, 482, 113584),
          (2134486, 1945270, 538, 182697))


def forged_program(appendants):
    program = object.__new__(Program)
    object.__setattr__(program, 'appendants', appendants)
    return program


class SuccinctPeriodicValidationTests(unittest.TestCase):
    def test_default_and_lowered_caps_forward_to_one_shared_assembly(self):
        program = Program(('01', '', '1'))
        with patch('s_only.succinct_periodic._assemble_program', return_value='sentinel') as assemble:
            self.assertEqual(compile_table(program), 'sentinel')
            assemble.assert_called_once_with(program, max_metadata_records=250000,
                                             max_compile_seconds=10)
            assemble.reset_mock()
            self.assertEqual(compile_table(program, max_phases=3, max_appendant_bits=3,
                                           max_metadata_records=80000,
                                           max_compile_seconds=2.5), 'sentinel')
            assemble.assert_called_once_with(program, max_metadata_records=80000,
                                             max_compile_seconds=2.5)

    def test_phase_and_bit_budgets_are_mandatory_and_cannot_be_raised(self):
        program = Program(('', '', ''))
        with patch('s_only.succinct_periodic._assemble_program') as assemble:
            for cap in (None, True, 0, -1, 6, 1.0):
                with self.subTest(phases=cap), self.assertRaises(ValueError):
                    compile_table(program, max_phases=cap)
            for cap in (None, True, -1, 9, 0.0):
                with self.subTest(bits=cap), self.assertRaises(ValueError):
                    compile_table(program, max_appendant_bits=cap)
            for source, bounds in ((Program(('',) * 6), {}),
                                   (program, {'max_phases': 2}),
                                   (Program(('1' * 9,)), {}),
                                   (Program(('01', '', '1')), {'max_appendant_bits': 2})):
                with self.subTest(source=source, bounds=bounds), self.assertRaises(CompilationLimit):
                    compile_table(source, **bounds)
            assemble.assert_not_called()

    def test_exact_program_and_nested_plain_immutable_binary_syntax(self):
        class DerivedProgram(Program):
            pass
        class Words(tuple):
            pass
        class Word(str):
            pass
        for bad in (None, ('',), DerivedProgram(('',))):
            with self.subTest(program=bad), self.assertRaises(TypeError):
                compile_table(bad)
        for appendants in ([], [''], (), Words(('',)), (Word('01'),),
                           (0,), ('012',), ('x',)):
            with self.subTest(appendants=appendants), self.assertRaises(ValueError):
                compile_table(forged_program(appendants))

    def test_identity_whitelists_never_call_custom_class_comparisons(self):
        class Poison(type):
            def __eq__(self, other):
                raise AssertionError('custom metaclass equality called')
            def __ne__(self, other):
                raise AssertionError('custom metaclass inequality called')
        class Unknown(metaclass=Poison):
            def __float__(self):
                raise AssertionError('custom numeric conversion called')
        class FakeProgram(Program, metaclass=Poison):
            pass
        class FakeInt(int, metaclass=Poison):
            pass
        for bad in (Unknown(), FakeProgram(('',))):
            with self.assertRaises(TypeError):
                compile_table(bad)
        for name in ('max_phases', 'max_appendant_bits', 'max_metadata_records',
                     'max_compile_seconds'):
            for bad in (Unknown(), FakeInt(1)):
                with self.subTest(name=name), self.assertRaises(ValueError):
                    compile_table(Program(('',)), **{name: bad})
        for constructor in (
                lambda: compile_table(forged_program((Unknown(),))),
                lambda: compile_table(forged_program(Unknown())),
                lambda: SuccinctGraphBuilder().embed(Unknown(), 0, 0),
                lambda: SuccinctSelectorTable((Unknown(),), 0)):
            with self.assertRaises(ValueError):
                constructor()

    def test_metadata_and_time_budget_checks_precede_pattern_construction(self):
        with patch('s_only.program_selector_parts.patterns.PatternFamily',
                   side_effect=AssertionError('constructed source patterns')):
            for cap in (None, True, 0, -1, 1.5):
                with self.subTest(metadata=cap), self.assertRaises(ValueError):
                    compile_table(Program(('',)), max_metadata_records=cap)
            for seconds in (None, True, 0, -1, float('inf'), float('nan')):
                with self.subTest(seconds=seconds), self.assertRaises(ValueError):
                    compile_table(Program(('',)), max_compile_seconds=seconds)
            with self.assertRaises(CompilationLimit):
                compile_table(Program(('',)), max_metadata_records=7)
            with patch('s_only.succinct_selector.time.monotonic', side_effect=(0, 2)):
                with self.assertRaises(CompilationLimit):
                    compile_table(Program(('',)), max_compile_seconds=1)

    def test_exact_metadata_boundary_and_empty_word_five_phase_syntax(self):
        program = Program(('',) * 5)
        table = compile_table(program, max_appendant_bits=0)
        self.assertEqual(compile_table(program, max_appendant_bits=0,
                                       max_metadata_records=table.metadata_records), table)
        with self.assertRaises(CompilationLimit):
            compile_table(program, max_metadata_records=table.metadata_records - 1)

    def test_small_api_contract_defaults_scope_and_graph_are_unchanged(self):
        with self.assertRaises(CompilationLimit):
            small_compile(Program(('',) * 3))
        with self.assertRaises(CompilationLimit):
            small_compile(Program(('1' * 9,)))
        with patch('s_only.succinct_selector._assemble_program', return_value='sentinel') as assemble:
            program = Program(('',))
            self.assertEqual(small_compile(program), 'sentinel')
            assemble.assert_called_once_with(program, max_metadata_records=100000,
                                             max_compile_seconds=10)
        for appendants in (('01',), ('1', '')):
            with self.subTest(appendants=appendants):
                program = Program(appendants)
                self.assertEqual(compile_table(program), small_compile(program))


class SuccinctPeriodicAssemblyTests(unittest.TestCase):
    def test_synthetic_original_order_constructors_and_root_resets(self):
        program = Program(('01', '', '1'))
        calls = []
        family = object()
        def make_family(source, *, required_period):
            self.assertIs(source, program)
            self.assertIsNone(required_period)
            calls.append(('family',))
            return family
        def worker(name):
            def make(builder, patterns, selected, fallback):
                self.assertIs(patterns, family)
                self.assertEqual(selected, 2)
                calls.append((name, builder.state_count, fallback))
                return builder.match(('S', '_'), selected, fallback)
            return make
        with patch('s_only.program_selector_parts.patterns.PatternFamily', side_effect=make_family), \
             patch('s_only.program_selector_parts.active.compile_active', side_effect=worker('active')), \
             patch('s_only.program_selector_parts.priority.compile_marked', side_effect=worker('marked')), \
             patch('s_only.program_selector_parts.priority.compile_fresh', side_effect=worker('fresh')):
            table = compile_table(program)
        self.assertEqual([entry[0] for entry in calls], ['family', 'active', 'marked', 'fresh'])
        self.assertEqual([table.status(q) for q in range(3)], ['normal', 'contracted', 'Rdx'])
        self.assertEqual(table.transition(2, 'S', 'root'), Command('Rdx', 1))
        for _, count, fallback in calls[1:]:
            self.assertLess(fallback, count)
            self.assertEqual(table.transition(fallback, 'S', 'L'), Command('U', fallback))
        self.assertEqual(table.materialize(max_states=table.state_count).start, table.start)

    def test_synthetic_fragment_constructor_rejects_mutable_impostors(self):
        class Pretend(type):
            def __eq__(self, other):
                return True
        class Mutable(metaclass=Pretend):
            start = 2
            state_count = 3
            origin = 0
            stop = 1
            patterns = ()
            blocks = ()
            row = (Command('normal'),) * 6
            def __post_init__(self):
                pass
        normal = _DirectRow(0, (Command('normal'),) * 6)
        probe = compile_pattern('S')
        good = _Fragment(1, probe, 0, 0)
        self.assertEqual(SuccinctSelectorTable((normal, good), 1).state_count, 2)
        for construct in (lambda: SuccinctSelectorTable((Mutable(),), 0),
                          lambda: SuccinctSelectorTable((normal, replace(good, table=Mutable())), 0),
                          lambda: SuccinctGraphBuilder().embed(Mutable(), 0, 0)):
            with self.assertRaises(ValueError):
                construct()


class SuccinctPeriodicControllerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tables = tuple(compile_table(Program(words)) for words in PROGRAMS)
        cls.archive = json.loads((ROOT / 'results/positive_period_programs.json').read_text())

    def test_archived_counts_new_representation_counts_and_boundary_entries(self):
        for words, table, counts in zip(PROGRAMS, self.tables, COUNTS):
            with self.subTest(appendants=words):
                self.assertEqual((table.state_count, table.start, len(table.blocks),
                                  table.metadata_records), counts)
                archived = next(p for p in self.archive['programs'] if p['appendants'] == list(words))
                self.assertEqual(table.state_count, archived['finite_control_states'])
                self.assertFalse(hasattr(table, 'states'))
                self.assertEqual(table.linear_coefficient, table.state_count + 1)
                for block in table.blocks:
                    for q in (block.origin, block.stop - 1):
                        for obs in OBSERVATIONS:
                            entry = table.transition(q, *obs)
                            self.assertIs(type(entry), Command)
                            if entry.next_state is not None:
                                self.assertTrue(0 <= entry.next_state < table.state_count)
                with self.assertRaises(CompilationLimit):
                    table.materialize(max_states=1000)

    def test_all_finished_code_is_exact_frozen_data_without_program_or_cache(self):
        for table in self.tables:
            self.assertEqual(tuple(field.name for field in fields(table)), ('blocks', 'start'))
            pending, seen = [table], set()
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
                    self.assertIsNot(type(value), Program)
                    pending.extend(getattr(value, field.name) for field in fields(value))

    def test_lookup_and_unchanged_runtime_do_not_recompile_or_read_source(self):
        table = self.tables[0]
        controls = (table.start, 0, 1, 2, table.state_count - 1, table.start)
        expected = [tuple(table.transition(q, *obs) for obs in OBSERVATIONS) for q in controls]
        with ExitStack() as patches:
            for target in ('s_only.succinct_periodic.compile_table',
                           's_only.succinct_selector._assemble_program',
                           's_only.succinct_selector.compile_pattern',
                           's_only.succinct_selector.compile_rows',
                           's_only.succinct_selector.compile_inverse_rows',
                           's_only.succinct_selector.compile_descent',
                           's_only.succinct_selector.compile_ascent',
                           's_only.program_selector_parts.patterns.PatternFamily',
                           's_only.cts.step', 's_only.encoding.encode',
                           's_only.succinct_selector.time.monotonic', 'builtins.open'):
                patches.enter_context(patch(target, side_effect=AssertionError('runtime source access')))
            self.assertEqual([tuple(table.transition(q, *obs) for obs in OBSERVATIONS)
                              for q in controls], expected)
            redex = App(App(App(S, S), S), S)
            result = execute(redex, table)
            self.assertEqual(erase(result.cursor), App(App(S, S), App(S, S)))
            self.assertIs(step(table, result), result)
            self.assertEqual(table.status(execute(S, table).control), 'normal')

    def test_first_twelve_seed11_selections_match_archived_paths(self):
        for words, table in zip(PROGRAMS, self.tables):
            archived = next(p for p in self.archive['programs'] if p['appendants'] == list(words))
            expected = next(run for run in archived['runs'] if run['seed'] == '11')
            term = encode(Program(words), '11')
            for path in expected['selected_addresses'][:12]:
                state = Configuration(table.start, Cursor.at(term))
                for ticks in range(200001):
                    if table.status(state.control) is not None:
                        break
                    self.assertLess(ticks, 200000, 'external selection-tick bound reached')
                    state = step(table, state)
                else:
                    self.fail('external 200,000-selection-tick bound reached')
                self.assertEqual(table.status(state.control), 'Rdx')
                self.assertEqual(''.join(map(str, state.cursor.path)), path)
                terminal = step(table, state)
                self.assertEqual(table.status(terminal.control), 'contracted')
                self.assertIs(step(table, terminal), terminal)
                term = erase(terminal.cursor)


if __name__ == '__main__':
    unittest.main()
