"""Consistency checks for the extended formal proof snapshot and replay."""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]

class ExtendedKernelEvidence(unittest.TestCase):
    def setUp(self):
        self.result = json.loads((ROOT / 'results/formal_extended_kernels.json').read_text())
        self.evidence = ROOT / self.result['evidence_directory']

    def test_union_replay_is_successful(self):
        self.assertEqual(self.result['status'], 'passed')
        self.assertEqual(self.result['combined_project_module_count'], 16)
        self.assertEqual(len(self.result['new_modules']), 7)
        self.assertEqual(self.result['fresh_kernel_replay']['exit_code'], 0)
        self.assertIsNone(self.result['fresh_kernel_replay']['stop_reason'])
        self.assertTrue(self.result['post_replay_integrity']['all_checks_passed'])

    def test_sources_and_build_receipts_match(self):
        for module in self.result['new_modules']:
            data = (ROOT / module['source']).read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), module['source_sha256'])
            self.assertEqual(len(data), module['source_bytes'])
            guard = json.loads((self.evidence / module['build_guard']).read_text())
            self.assertEqual(guard['exit_code'], 0)
            self.assertIsNone(guard['stop_reason'])
            self.assertIsNone(re.search(r'^\s*(axiom|unsafe|partial)\b|\b(sorry|admit|native_decide)\b', data.decode(), re.M))

    def test_160_extension_axiom_queries(self):
        audit = json.loads((self.evidence / 'axioms.json').read_text())
        self.assertEqual(audit['count'], 160)
        self.assertEqual(len(audit['declarations']), 160)
        self.assertEqual(len({r['declaration'] for r in audit['declarations']}), 160)
        for row in audit['declarations']:
            self.assertLessEqual(set(row['axioms']), {'propext', 'Quot.sound', 'Classical.choice'})
        base = json.loads((ROOT / self.result['base_checkpoint']).read_text())
        self.assertEqual(base['axiom_query_count'] + audit['count'], self.result['combined_axiom_query_count'])

    def test_artifact_manifest(self):
        for row in json.loads((self.evidence / 'manifest.json').read_text()):
            data = (self.evidence / row['path']).read_bytes()
            self.assertEqual(len(data), row['bytes'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'])

    def test_import_only_replay_wrapper(self):
        self.assertEqual((self.evidence / 'SOnlyExtendedReplay.lean').read_text().splitlines(),
                         ['import SOnlyBridgesReplay', 'import SOnlyMemory',
                          'import SOnlyProvenanceRows', 'import SOnlyResponseLabels',
                          'import SOnlyCurrentDecoder'])

if __name__ == '__main__':
    unittest.main()
