"""Identity and negative-control checks for the end-to-end Lean certificate."""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]

class EndToEndProofEvidence(unittest.TestCase):
    def setUp(self):
        self.result = json.loads((ROOT / 'results/formal_universality.json').read_text())
        self.evidence = ROOT / self.result['evidence_directory']

    def test_all_56_sources_and_clean_builds(self):
        self.assertEqual(self.result['project_module_count'], 56)
        self.assertEqual(len(self.result['modules']), 56)
        for row in self.result['modules']:
            data = (ROOT / 'formal' / row['path']).read_bytes()
            self.assertEqual(len(data), row['bytes'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'], row['module'])
            self.assertIsNone(re.search(r'^\s*(?:noncomputable|axiom|unsafe|partial)\b', data.decode(), re.M))
            self.assertIsNone(re.search(r'\b(?:sorry|admit|native_decide)\b', data.decode()))
        records = json.loads((self.evidence / 'build-records.json').read_text())
        self.assertEqual(len(records), 57)
        self.assertTrue(all(row['exit_code'] == 0 for row in records))

    def test_fresh_replay_and_integrity(self):
        replay = self.result['fresh_kernel_replay']
        self.assertEqual(replay['exit_code'], 0)
        self.assertIsNone(replay['stop_reason'])
        self.assertIn('--fresh', replay['command'])
        integrity = self.result['post_replay_integrity']
        self.assertTrue(integrity['all_checks_passed'])
        self.assertEqual(integrity['counts']['pinned_sources'], 426)
        self.assertEqual(integrity['counts']['official_toolchain'], 17505)
        self.assertEqual(integrity['counts']['final_source_output_wrapper_files'], 115)

    def test_all_1142_declared_queries(self):
        audit = json.loads((self.evidence / 'declaration-axioms.json').read_text())
        self.assertEqual(audit['count'], 1142)
        self.assertEqual(len(audit['declarations']), 1142)
        self.assertEqual(len({r['declaration'] for r in audit['declarations']}), 1142)
        for row in audit['declarations']:
            self.assertLessEqual(set(row['axioms']), {'propext', 'Quot.sound', 'Classical.choice'})

    def test_computable_data_have_no_choice_axiom(self):
        data = self.result['computable_data_dependencies']
        self.assertIn('SOnlyUniversality.encode', data)
        self.assertIn('SOnlyUniversality.decode', data)
        for name, axioms in data.items():
            self.assertLessEqual(set(axioms), {'propext', 'Quot.sound'}, name)

    def test_main_certificate_interfaces_are_present(self):
        audit = json.loads((self.evidence / 'declaration-axioms.json').read_text())
        names = {row['declaration'] for row in audit['declarations']}
        required = {'SOnlyUniversality.result_iff_first_event',
                    'SOnlyUniversality.halting_iff_event', 'SOnlyUniversality.root_reset',
                    'SOnlyUniversality.no_interinvocation_state',
                    'SOnlyUniversality.every_step_native', 'SOnlyUniversality.all_input_linear',
                    'SOnlyObserver.event_finite_cover'}
        self.assertLessEqual(required, names)
        self.assertTrue(any(name.startswith('SOnlyDecoderBoundCurrent.') for name in names))
        text = (self.evidence / 'main-theorem-types.txt').read_text()
        self.assertIn('(value : Nat)', text)
        self.assertIn('input : Fin (d + 1) → Nat', text)
        self.assertIn('controller.InterInvocationState = Unit', text)

    def test_positive_and_negative_controls(self):
        controls = json.loads((self.evidence / 'canary-result.json').read_text())
        self.assertEqual(controls['status'], 'passed')
        self.assertEqual(controls['valid_proof_fresh_replay_exit'], 0)
        self.assertEqual(controls['ordinary_invalid_source_exit'], 1)
        self.assertEqual(controls['injected_invalidFalse_fresh_replay_exit'], 1)
        self.assertTrue(controls['canaries_separate_from_proof_search_path'])
        log = (self.evidence / 'final-canary-invalid-replay.txt').read_text()
        self.assertIn("declaration 'invalidFalse'", log)
        self.assertIn('declaration type mismatch', log)
        self.assertIn('Prop', log)
        self.assertIn('False', log)

    def test_every_preserved_artifact_matches(self):
        rows = json.loads((self.evidence / 'manifest.json').read_text())
        for row in rows:
            data = (self.evidence / row['path']).read_bytes()
            self.assertEqual(len(data), row['bytes'], row['path'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'], row['path'])

    def test_proof_wrapper_excludes_canaries(self):
        lines = (self.evidence / 'SOnlyUniversalityReplay.lean').read_text().splitlines()
        self.assertEqual(len(lines), 56)
        self.assertTrue(all(line.startswith('import SOnly') for line in lines))
        self.assertFalse(any('Canary' in line or 'InvalidProof' in line for line in lines))

if __name__ == '__main__':
    unittest.main()
