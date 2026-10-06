"""Regression of reproducible, bounded selector measurements."""
import unittest
from tools.compare_strategies import compare


class StrategyComparisonTests(unittest.TestCase):
    def test_exact_published_comparison(self):
        result = compare()
        self.assertEqual(result["common_trajectory_steps"], 85)
        for strategy, count, first in (("normal", 8, 3), ("applicative", 3, 4), ("head", 8, 3)):
            stats = result["choices_on_common_trajectory"][strategy]
            self.assertEqual(stats["matching_choices"], count)
            self.assertEqual(stats["first_difference"]["contraction"], first)
        self.assertEqual([run["final_nodes"] for run in result["separate_runs"]], [26101, 4351, 26101])
        for run in result["separate_runs"]:
            self.assertEqual(run["steps"], 100)
            self.assertEqual(run["status"], "step_limit")
            self.assertEqual(run["observations"], [{"contraction": 0, "horizon": 0, "phase": 0, "data": "101"}])


if __name__ == "__main__":
    unittest.main()
