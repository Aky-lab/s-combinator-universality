"""The UT19 instance is a regular syntax language, with bounded replay only."""
import json
from pathlib import Path
import tempfile
import unittest

from s_only.pattern_automaton import compile_pattern
from tools.ut19_event_language_report import (
    FIRST_ADDRESSES, LABEL, ROUTE, _same_patterns, build_event_pattern, make_report,
)


class UT19EventLanguageReportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Minimal independent replay fixture; never depends on a /tmp file.
        cls.trace = {
            "schema": "ut19-native-bounded-attempt-v1",
            "seed_sha256": "b8fb1a29238d02cbe5249637205fe999646ec54f918418f158d279977f983155",
            "state_count": 2122868774,
            "records": [
                {"native_step": step, "address": address, "expanded_nodes": count}
                for step, (address, count) in enumerate(zip(
                    ("0", "0", "01", "", "0", "", "10", "10"),
                    (44077, 44089, 44101, 88149, 132197, 176281, 220329, 264381)), 1)
            ],
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "trace.json"
            path.write_text(json.dumps(cls.trace))
            cls.report = make_report(path)

    def test_exact_fixed_instance_and_labelled_record(self):
        family, pattern = build_event_pattern()
        self.assertEqual(LABEL, (17, 1))
        self.assertEqual(ROUTE, (0, 1, 0, 0, 0, 1, 1))
        self.assertEqual(family.required_period, None)
        self.assertEqual(family.program.appendants[17], "0" * 17 + "10")
        records = {label: (entry, route) for entry, route, label in family.dispatch_records()}
        self.assertEqual(len(records), 76)
        self.assertEqual(records[LABEL][1], ROUTE)
        self.assertTrue(_same_patterns(pattern, family.local_pattern("fresh", records[LABEL][0])))
        self.assertFalse(_same_patterns(pattern, family.local_pattern("marked", records[LABEL][0])))
        self.assertFalse(_same_patterns(pattern, family.local_pattern("fresh", records[(17, 0)][0])))
        automaton = compile_pattern(pattern)
        self.assertEqual(len(automaton.nodes), 1750)
        self.assertEqual(automaton.state_bits, 1751)

    def test_syntax_positives_negatives_and_initial_arity_exclusion(self):
        report = self.report
        self.assertIn("no source-event or reachability theorem", report["scope"])
        self.assertTrue(report["independent_dispatch_record_equality"])
        self.assertTrue(report["fabricated_positive"]["root_match"])
        self.assertTrue(report["fabricated_positive"]["descendant_match"])
        self.assertFalse(report["atomic_negative"]["descendant_match"])
        self.assertEqual(report["samples"][0]["maximum_head_arity"], 4)
        self.assertEqual(report["samples"][0]["expanded_nodes"], 44069)
        self.assertEqual(report["seed"]["bits"], 1710)
        self.assertEqual(report["automaton"]["state_count_bound"], "2^1751")
        self.assertFalse(report["automaton"]["state_space_materialized"])
        self.assertFalse(report["automaton"]["minimality_claim"])

    def test_eight_native_rewrites_with_recorded_sizes_but_no_selector_run(self):
        report = self.report
        self.assertEqual(FIRST_ADDRESSES, ("0", "0", "01", "", "0", "", "10", "10"))
        self.assertEqual(report["replay"]["native_contractions_replayed"], 8)
        self.assertFalse(report["replay"]["selector_reexecuted"])
        self.assertEqual([sample["native_step"] for sample in report["samples"]], list(range(9)))
        self.assertEqual([sample["expanded_nodes"] for sample in report["samples"][1:]],
                         [record["expanded_nodes"] for record in self.trace["records"]])
        self.assertFalse(any(sample["descendant_match"] for sample in report["samples"]))


if __name__ == "__main__":
    unittest.main()
