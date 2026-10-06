"""External report boundaries; no large controller is needed for these tests."""
import contextlib
import io
import json
import math
import unittest
from unittest.mock import Mock, patch

from tools import periodic_selector_report as runner


class PeriodicReportTests(unittest.TestCase):
    def test_invalid_bounds_precede_compilation(self):
        cases = [dict(**{name: value})
                 for name in ('max_states', 'max_steps', 'max_ticks', 'max_nodes')
                 for value in (0, -1, True, 0.5)]
        cases += [dict(max_seconds=value) for value in (0, -1, True, math.inf, math.nan)]
        with patch.object(runner, 'selector_table', side_effect=AssertionError('compiled')):
            for arguments in cases:
                with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                    runner.report(**arguments)

    def test_deterministic_cli_and_bound_routing(self):
        output = io.StringIO()
        with patch('sys.argv', ['report', '--deterministic', '--max-states', '77',
                               '--max-steps', '23', '--max-microticks', '101',
                               '--max-nodes', '151', '--max-seconds', '5']), \
             patch.object(runner, 'report', return_value={'elapsed_seconds': 1, 'run_count': 12}) as report, \
             contextlib.redirect_stdout(output):
            runner.main()
        report.assert_called_once_with(max_states=77, max_steps=23, max_ticks=101,
                                       max_nodes=151, max_seconds=5)
        self.assertEqual(json.loads(output.getvalue()), {'run_count': 12})

    def test_lower_compile_cap_failure_is_retained_before_success(self):
        table = Mock(states=((), ()))
        compile_table = Mock(side_effect=[runner.CompilationLimit('controller exceeds 2000000 states'), table])
        run = {'native_contractions': 2, 'samples_checked': 3, 'checkpoints': [{}, {}, {}]}
        with patch.object(runner, 'PROGRAMS', (('01', '', '1', '01', '001'),)), \
             patch.object(runner, 'SEEDS', ('11',)), \
             patch.object(runner, 'selector_table', compile_table), \
             patch.object(runner, 'compile_reader'), patch.object(runner, '_graph_digest', return_value='digest'), \
             patch.object(runner, 'run_one', return_value=run):
            result = runner.report()
        self.assertEqual([call.kwargs['max_states'] for call in compile_table.call_args_list],
                         [2_000_000, 3_000_000])
        attempts = result['programs'][0]['compilation_attempts']
        self.assertEqual([item['status'] for item in attempts], ['construction_limit', 'compiled'])
        self.assertEqual(result['accepted_samples'], 3)

    def test_failed_final_compile_cap_cannot_emit_success(self):
        compile_table = Mock(side_effect=runner.CompilationLimit('state cap'))
        with patch.object(runner, 'PROGRAMS', (('01', '', '1', '01', '001'),)), \
             patch.object(runner, 'selector_table', compile_table), \
             patch.object(runner, 'run_one', side_effect=AssertionError('executed')):
            with self.assertRaisesRegex(runner.CompilationLimit, 'exhausted'):
                runner.report(max_states=2_000_000)
        self.assertEqual(compile_table.call_count, 1)


if __name__ == '__main__':
    unittest.main()
