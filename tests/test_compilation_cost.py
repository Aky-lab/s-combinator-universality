"""Independent allocation checks; the large fixture is never compiled."""
from contextlib import ExitStack, redirect_stderr, redirect_stdout
from io import StringIO
import itertools
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from s_only.compilation_cost import (compilation_cost, dispatcher_leaf_depths,
                                     literal_matcher_states)
from s_only.cts import Program
from s_only import encoding
from s_only.probes import HOLE, LITERAL_S, compile_pattern, compile_rows
from s_only.program_selector_parts.compiler import compile_table
from s_only.program_selector_parts.patterns import PatternFamily, literal
from s_only.selector_parts.graph import GraphBuilder
from s_only.terms import nodes
from tools.compilation_cost_report import main, report


ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = (('',), ('0',), ('1',), ('01',), ('10',), ('1', ''),
            ('00', '00'), ('', '', ''), ('0', '', '0'), ('01', '', '01'),
            ('10', '1', '', '10'), ('01', '', '1', '01', '001'))


def structural_matcher_count(pattern):
    """Count every pattern occurrence directly, without the symbolic formula."""
    pending, applications, literals = [pattern], 0, 0
    while pending:
        item = pending.pop()
        if item == LITERAL_S:
            literals += 1
        elif item != HOLE:
            applications += 1
            pending.extend(item)
    return 6 * applications + literals


class CompilationCostTests(unittest.TestCase):
    def test_matcher_recurrence_and_graph_embedding(self):
        patterns = (HOLE, LITERAL_S, (HOLE, HOLE), (LITERAL_S, HOLE),
                    (HOLE, LITERAL_S), (LITERAL_S, LITERAL_S))
        for left, right in itertools.product(patterns, repeat=2):
            pattern = (left, right)
            expected = 6 + structural_matcher_count(left) + structural_matcher_count(right)
            self.assertEqual(structural_matcher_count(pattern), expected)
            self.assertEqual(len(compile_pattern(pattern).states), 2 + expected)
            builder = GraphBuilder()
            yes, no = builder.uniform('contracted'), builder.uniform('normal')
            before = len(builder.states)
            builder.match(pattern, yes, no)
            self.assertEqual(len(builder.states) - before, expected)
        # Identical shared Python objects still compile once per occurrence/row.
        repeated = ((LITERAL_S, LITERAL_S), HOLE)
        table = compile_rows(((repeated, ()), (repeated, ())))
        self.assertEqual(len(table.states) - 2, 2 * structural_matcher_count(repeated))

    def test_closed_literal_size_formula(self):
        terms = [encoding.B, encoding.PI, encoding.C0, encoding.HALT,
                 *encoding.VALUES, *encoding.LIVE]
        terms += [encoding.append_routine(''.join(bits)) for length in range(4)
                  for bits in itertools.product('01', repeat=length)]
        for term in terms:
            self.assertEqual(literal_matcher_states(nodes(term)),
                             len(compile_pattern(literal(term)).states) - 2)
        for bad in (-1, 0, 2, 4, True, 3.0, '3', None):
            with self.assertRaises(ValueError):
                literal_matcher_states(bad)

    def test_largest_power_depths_match_actual_labelled_layout(self):
        for period in (*range(1, 18), 31, 32, 33):
            p = PatternFamily(Program(('0',) * period), required_period=None)
            expected = dispatcher_leaf_depths(2 * period)
            records = p.dispatch_records()
            self.assertEqual(len(records), 2 * period)
            for index, (_, route, label) in enumerate(records):
                self.assertEqual(label, divmod(index, 2))
                self.assertEqual(route, p.route_for(label))
                self.assertEqual(len(route), expected[index])
        self.assertEqual(dispatcher_leaf_depths(1), (0,))
        self.assertEqual(dispatcher_leaf_depths(6), (3, 3, 3, 3, 2, 2))
        self.assertEqual(dispatcher_leaf_depths(10), (4,) * 8 + (2,) * 2)
        for bad in (0, -1, True, 2.0, None):
            with self.assertRaises(ValueError):
                dispatcher_leaf_depths(bad)

    def test_dispatch_branch_and_sibling_costs_against_real_patterns(self):
        for words in PROGRAMS:
            p = PatternFamily(Program(words), required_period=None)
            stats = compilation_cost(p.program)
            self.assertEqual(stats.dispatcher_nodes, nodes(p.dispatch.code))
            self.assertEqual(stats.dispatcher_matcher_states,
                             structural_matcher_count(literal(p.dispatch.code)))
            for phase in stats.phases:
                current, sibling_total = p.dispatch, 0
                for side in p.route_for((phase.phase, 1)):
                    left, right = current.left, current.right
                    self.assertEqual(structural_matcher_count(literal(current.code)),
                                     27 + structural_matcher_count(literal(left.code))
                                     + structural_matcher_count(literal(right.code)))
                    sibling = right if side == 0 else left
                    sibling_total += len(compile_pattern(literal(sibling.code)).states) - 2
                    current = left if side == 0 else right
                self.assertEqual(current.label, (phase.phase, 1))
                self.assertEqual(phase.dormant_literal_matcher_states_per_row, sibling_total)

    def test_exact_selected_rows_and_both_lower_bounds(self):
        for words in PROGRAMS:
            with self.subTest(words=words):
                p = PatternFamily(Program(words), required_period=None)
                stats = compilation_cost(p.program)
                rows = p.selected_action_rows()
                self.assertEqual(len(rows), stats.selected_action_rows)
                for word in words:
                    self.assertEqual(len(p.appender_rows(word)), max(0, 2 * len(word) - 1))
                matchers = sum(structural_matcher_count(pattern) for pattern, _ in rows)
                addresses = sum(len(address) for _, address in rows)
                self.assertEqual(stats.selected_action_matcher_states, matchers)
                self.assertEqual(stats.selected_action_address_states, addresses)
                self.assertEqual(len(compile_rows(rows).states) - 2,
                                 stats.selected_action_embedded_states)
                builder = GraphBuilder()
                yes, no = builder.uniform('contracted'), builder.uniform('normal')
                before = len(builder.states)
                builder.rows(rows, yes, no)
                self.assertEqual(len(builder.states) - before, stats.selected_action_embedded_states)
                self.assertLessEqual(stats.dormant_literal_state_lower_bound, matchers)
                self.assertEqual(sum(item.selected_rows for item in stats.phases), len(rows))

    def test_exhaustive_small_appender_response_formula(self):
        for length in range(5):
            for bits in itertools.product('01', repeat=length):
                word = ''.join(bits)
                p = PatternFamily(Program((word,)), required_period=None)
                stats = compilation_cost(p.program)
                actual = sum(structural_matcher_count(pattern) + len(address)
                             for pattern, address in p.selected_action_rows())
                self.assertEqual(stats.selected_action_embedded_states, actual, word)
        # The weaker sibling bound uses lengths/ones. The exact component also
        # sees where ones occur, because suffix literals repeat in stage rows.
        first, second = (compilation_cost(Program((word,))) for word in ('01', '10'))
        self.assertEqual(first.dormant_literal_state_lower_bound, second.dormant_literal_state_lower_bound)
        self.assertEqual(first.selected_action_embedded_states - second.selected_action_embedded_states, 14)

    def test_exact_small_whole_graph_and_recorded_controllers(self):
        # One actual whole graph, kept small; existing reports independently
        # record larger complete graphs, including repeated and odd-period cases.
        program = Program(('01',))
        table = compile_table(program, required_period=None, max_states=150_000,
                              max_appendant_bits=2, max_phases=1)
        self.assertEqual(len(table.states), 129_268)
        self.assertLess(compilation_cost(program).selected_action_embedded_states, len(table.states))
        for filename in ('two_phase_programs.json', 'positive_period_programs.json'):
            document = json.loads((ROOT / 'results' / filename).read_text())
            for record in document['programs']:
                stats = compilation_cost(Program(tuple(record['appendants'])))
                self.assertLessEqual(stats.dormant_literal_state_lower_bound,
                                     stats.selected_action_embedded_states)
                self.assertLess(stats.selected_action_embedded_states, record['finite_control_states'])

    def test_fixture_statistics_without_any_construction(self):
        document = json.loads((ROOT / 'artifacts/neary-left-toggle/program.json').read_text())
        program = Program(tuple(document['appendants'] if isinstance(document, dict) else document))
        with ExitStack() as patches:
            for target in ('s_only.encoding.compile_program',
                           's_only.encoding.append_routine',
                           's_only.program_selector_parts.patterns.PatternFamily',
                           's_only.selector_parts.graph.GraphBuilder',
                           's_only.probes.compile_pattern', 's_only.probes.compile_rows'):
                patches.enter_context(patch(target, side_effect=AssertionError('construction forbidden')))
            stats = compilation_cost(program)
            result = report(program)
        self.assertEqual((stats.phase_count, stats.total_appendant_bits, stats.total_appendant_ones,
                          stats.unique_appendant_count, stats.nonempty_appendant_count,
                          stats.max_appendant_bits), (482, 63_644, 140, 41, 126, 1998))
        self.assertEqual(stats.dispatcher_nodes, 1_288_577)
        self.assertEqual(stats.dispatcher_matcher_states, 4_510_017)
        self.assertEqual(stats.selected_action_rows, 127_288)
        self.assertEqual(stats.dormant_literal_state_lower_bound, 568_498_572_096)
        self.assertEqual(stats.selected_action_embedded_states, 571_594_401_546)
        self.assertEqual(stats.selected_action_address_states, 42_514_486)
        saved = json.loads((ROOT / 'results/neary_compilation_cost.json').read_text())
        saved.pop('program_file_sha256')
        self.assertEqual(result, saved)
        self.assertEqual(result['leaf_depth_histogram'], {'10': 960, '6': 4})
        self.assertNotIn('phases', result)
        self.assertEqual(len(report(program, include_phases=True)['phases']), 482)

    def test_empty_program_actions_and_invalid_type(self):
        for period in (1, 2, 3, 7):
            stats = compilation_cost(Program(('',) * period))
            self.assertEqual(stats.selected_action_rows, 0)
            self.assertEqual(stats.selected_action_embedded_states, 0)
            self.assertEqual(stats.dormant_literal_state_lower_bound, 0)
        for bad in (None, ('1',), ['1'], '1'):
            with self.assertRaises(TypeError):
                compilation_cost(bad)

    def test_report_cli_reproducible_and_bounded(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'program.json'
            destination = Path(directory) / 'result.json'
            path.write_text('["0", "", "0"]')
            with redirect_stdout(StringIO()) as output:
                first = main(['--program', str(path), '--include-phases'])
            self.assertEqual(json.loads(output.getvalue()), first)
            second = main(['--program', str(path), '--include-phases', '--output', str(destination)])
            self.assertEqual(first, second)
            self.assertEqual(json.loads(destination.read_text()), second)
            for arguments in (['--max-input-bytes', '1'], ['--max-phases', '2'],
                              ['--max-appendant-bits', '1'], ['--max-input-bytes', '-1']):
                with redirect_stderr(StringIO()), self.assertRaises(SystemExit):
                    main(['--program', str(path), *arguments])
            for invalid in ('{}', '[]', '["2"]', '[false]', 'not json'):
                path.write_text(invalid)
                with redirect_stderr(StringIO()), self.assertRaises(SystemExit):
                    main(['--program', str(path)])


if __name__ == '__main__':
    unittest.main()
