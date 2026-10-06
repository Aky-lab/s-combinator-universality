"""Check report limits and the explicit empty-word comparison convention."""
import contextlib
import io
import json
import math
import time
import unittest
from unittest.mock import Mock, patch

from s_only.cts import Configuration as SourceState, Program
from s_only.root_selector import SelectorTable
from s_only.selector_parts.graph import Command
from s_only.terms import App, S, nodes
from tools import program_selector_report as runner


class ProgramReportTests(unittest.TestCase):
    def test_invalid_bounds_precede_compilation(self):
        cases = [dict(**{name: value})
                 for name in ('max_states', 'max_steps', 'max_ticks', 'max_nodes')
                 for value in (0, -1, True, 0.5)]
        cases += [dict(max_seconds=value) for value in (0, -1, True, math.inf, math.nan)]
        with patch.object(runner, 'selector_table', side_effect=AssertionError('compiled')):
            for arguments in cases:
                with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                    runner.report(**arguments)

    def test_totalization_is_only_the_empty_case(self):
        program = Program(('01', '001'))
        self.assertEqual(runner.totalized_source_step(program, SourceState('11')),
                         SourceState('101', 1))
        with patch.object(runner, 'source_step', side_effect=AssertionError('ordinary empty step')):
            self.assertEqual(runner.totalized_source_step(program, SourceState('', 0)),
                             SourceState('', 1))
            self.assertEqual(runner.totalized_source_step(program, SourceState('', 1)),
                             SourceState('', 0))

    def test_growth_limit_is_checked_before_contraction(self):
        z = App(App(App(S, S), S), S)
        term = App(App(App(S, S), S), z)
        table = SelectorTable(((Command('Rdx', 1),) * 6,
                               (Command('contracted'),) * 6), 0)
        with patch.object(runner, 'encode', return_value=term), \
             patch.object(runner, 'step', side_effect=AssertionError('contracted')):
            with self.assertRaisesRegex(runner.ExperimentLimit, 'next contraction'):
                runner.run_one(Program(('', '')), table, Mock(decode=lambda _: None), '',
                               target_horizon=2, max_steps=1, max_ticks=1,
                               max_nodes=nodes(term), deadline=time.monotonic() + 5)

    def test_native_step_limit_stops_after_exactly_one_contraction(self):
        z = App(App(App(S, S), S), S)
        term = App(App(App(S, S), S), z)
        table = SelectorTable(((Command('Rdx', 1),) * 6,
                               (Command('contracted'),) * 6), 0)
        with patch.object(runner, 'encode', return_value=term), \
             patch.object(runner, 'erase', wraps=runner.erase) as erase:
            with self.assertRaisesRegex(runner.ExperimentLimit, 'native-contraction'):
                runner.run_one(Program(('', '')), table, Mock(decode=lambda _: None), '',
                               target_horizon=2, max_steps=1, max_ticks=1,
                               max_nodes=100, deadline=time.monotonic() + 5)
            self.assertEqual(erase.call_count, 1)

    def test_deterministic_output_omits_only_elapsed_time(self):
        result = {'elapsed_seconds': 4.5, 'run_count': 20}
        output = io.StringIO()
        with patch('sys.argv', ['report', '--deterministic']), \
             patch.object(runner, 'report', return_value=result), contextlib.redirect_stdout(output):
            runner.main()
        self.assertEqual(json.loads(output.getvalue()), {'run_count': 20})


if __name__ == '__main__':
    unittest.main()
