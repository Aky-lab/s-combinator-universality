"""Bounds and deterministic presentation are outside selector control."""
import contextlib
import io
import json
import math
import unittest
from unittest.mock import patch

from tools import root_selector_report as runner


class RootReportTests(unittest.TestCase):
    def test_invalid_bounds_fail_before_compilation(self):
        cases = [dict(max_ticks=x) for x in (0, -1, True, 0.5)]
        cases += [dict(max_seconds=x) for x in (0, -1, True, math.inf, math.nan)]
        cases += [dict(malformed_leaves=x) for x in (0, -1, True, 1.5)]
        with patch.object(runner, 'selector_table', side_effect=AssertionError('compiled')):
            for arguments in cases:
                with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                    runner.report(**arguments)

    def test_deterministic_output_omits_only_wall_durations(self):
        result = {'compile_seconds': 1.2, 'elapsed_seconds': 3.4, 'finite_control_states': 7}
        stream = io.StringIO()
        with patch('sys.argv', ['report', '--deterministic']), \
             patch.object(runner, 'report', return_value=result), contextlib.redirect_stdout(stream):
            runner.main()
        self.assertEqual(json.loads(stream.getvalue()), {'finite_control_states': 7})

    def test_default_output_retains_measured_wall_durations(self):
        result = {'compile_seconds': 1.2, 'elapsed_seconds': 3.4, 'finite_control_states': 7}
        stream = io.StringIO()
        with patch('sys.argv', ['report']), patch.object(runner, 'report', return_value=result), \
             contextlib.redirect_stdout(stream):
            runner.main()
        self.assertEqual(json.loads(stream.getvalue()), result)


if __name__ == '__main__':
    unittest.main()
