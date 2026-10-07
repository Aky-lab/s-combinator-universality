"""Consistency checks for the preserved Lean source/event replay evidence."""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]

class FormalEventInterfacesEvidence(unittest.TestCase):
    def setUp(self):
        self.result = json.loads((ROOT / 'results/formal_event_interfaces.json').read_text())
        self.evidence = ROOT / self.result['evidence_directory']

    def test_complete_replay_and_integrity(self):
        self.assertEqual(self.result['status'], 'passed')
        self.assertEqual(self.result['upstream_commit'], '85a867988442fc423279341200f81634a1e65582')
        self.assertEqual(self.result['fresh_kernel_replay']['exit_code'], 0)
        self.assertIsNone(self.result['fresh_kernel_replay']['stop_reason'])
        self.assertTrue(self.result['post_replay_integrity']['all_checks_passed'])
        self.assertEqual(len(self.result['modules']), 9)

    def test_exact_module_sources_and_successful_builds(self):
        for module in self.result['modules']:
            data = (ROOT / module['source']).read_bytes()
            self.assertEqual(len(data), module['source_bytes'], module['module'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), module['source_sha256'])
            guard = json.loads((self.evidence / module['build_guard']).read_text())
            self.assertEqual(guard['exit_code'], 0, module['module'])
            self.assertIsNone(guard['stop_reason'])
            text = data.decode()
            self.assertIsNone(re.search(r'^\s*(axiom|unsafe|partial)\b', text, re.M))
            self.assertIsNone(re.search(r'\b(sorry|admit|native_decide)\b', text))

    def test_all_recorded_axiom_queries_are_resolved(self):
        report = json.loads((self.evidence / 'axioms.json').read_text())
        declarations = report['declarations']
        self.assertEqual(len(declarations), 242)
        self.assertEqual(len({x['declaration'] for x in declarations}), 242)
        self.assertEqual(report['count'], self.result['axiom_query_count'])
        allowed = {'propext', 'Quot.sound', 'Classical.choice'}
        for row in declarations:
            self.assertLessEqual(set(row['axioms']), allowed)
        self.assertIn(self.result['principal_theorem'], {x['declaration'] for x in declarations})

    def test_artifact_bytes_match_manifest(self):
        manifest = json.loads((self.evidence / 'manifest.json').read_text())
        for row in manifest:
            data = (self.evidence / row['path']).read_bytes()
            self.assertEqual(len(data), row['bytes'], row['path'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'], row['path'])

    def test_replay_wrapper_has_only_the_frozen_roots(self):
        lines = (self.evidence / 'SOnlyBridgesReplay.lean').read_text().splitlines()
        self.assertEqual(lines, ['import SOnlyStageEvents', 'import SOnlyInitial',
                                 'import SOnlyProvenance', 'import SOnlyCounter'])

if __name__ == '__main__':
    unittest.main()
