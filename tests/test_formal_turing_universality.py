"""Identity and scope checks for the conventional-Turing-machine Lean result."""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ConventionalTuringProofEvidence(unittest.TestCase):
    def setUp(self):
        self.result = json.loads((ROOT / 'results/formal_turing_universality.json').read_text())
        self.evidence = ROOT / self.result['evidence_directory']
        self.audit = json.loads((self.evidence / 'declaration-axioms.json').read_text())

    def test_67_source_identities_and_68_clean_builds(self):
        self.assertEqual(self.result['project_module_count'], 67)
        self.assertEqual(len(self.result['modules']), 67)
        for row in self.result['modules']:
            data = (ROOT / 'formal' / row['path']).read_bytes()
            self.assertEqual(len(data), row['bytes'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'], row['module'])
            self.assertIsNone(re.search(r'^\s*(?:noncomputable|axiom|unsafe|partial)\b', data.decode(), re.M))
            self.assertIsNone(re.search(r'\b(?:sorry|admit|native_decide)\b', data.decode()))
        records = json.loads((self.evidence / 'build-records.json').read_text())
        self.assertEqual(len(records), 68)
        self.assertTrue(all(row['exit_code'] == 0 for row in records))

    def test_fresh_replay_and_all_input_integrity(self):
        replay = self.result['fresh_kernel_replay']
        self.assertEqual(replay['exit_code'], 0)
        self.assertIsNone(replay['stop_reason'])
        self.assertIn('--fresh', replay['command'])
        integrity = self.result['post_replay_integrity']
        self.assertTrue(integrity['all_checks_passed'])
        expected = {'pinned_sources': 426, 'pinned_dependency_outputs': 424,
                    'official_toolchain': 17505, 'project_sources': 67,
                    'final_source_output_wrapper_files': 136}
        for key, count in expected.items():
            self.assertEqual(integrity['counts'][key], count)

    def test_all_1359_declared_queries(self):
        self.assertEqual(self.audit['count'], 1359)
        rows = self.audit['declarations']
        self.assertEqual(len(rows), 1359)
        self.assertEqual(len({row['declaration'] for row in rows}), 1359)
        for row in rows:
            self.assertLessEqual(set(row['axioms']), {'propext', 'Quot.sound', 'Classical.choice'})

    def test_executable_encoder_compiler_observer_decoder(self):
        dependencies = self.result['computable_data_dependencies']
        required = {'SOnlyTuringUniversality.encode', 'SOnlyTapeCompiler.compile',
                    'SOnlyTapeCompiler.pc', 'SOnlyTapeCompiler.inputValues',
                    'SOnlyTuringUniversality.event', 'SOnlyTuringUniversality.decode'}
        self.assertLessEqual(required, dependencies.keys())
        for name, axioms in dependencies.items():
            self.assertLessEqual(set(axioms), {'propext', 'Quot.sound'}, name)

    def test_conventional_tape_and_literal_compiler_interfaces(self):
        names = {row['declaration'] for row in self.audit['declarations']}
        required = {'SOnlyTapeStacks.apply_represents', 'SOnlyTapeStacks.represents_read',
                    'SOnlyTapeStacks.input_haltsAfter_iff', 'SOnlyTapeStacks.stackCode_injective',
                    'SOnlyTapeCompiler.action_executes', 'SOnlyTapeCompiler.input_halting_iff',
                    'SOnlyTapeCompiler.input_left_stack_result_iff',
                    'SOnlyTapeCompiler.instruction_independent', 'SOnlyTapeCompiler.labelCount_eq',
                    'SOnlyTapeCompilerCheckpoints.reflects_halt_bounded',
                    'SOnlyTuringUniversality.halting_iff_event',
                    'SOnlyTuringUniversality.selector_executes',
                    'SOnlyTuringUniversality.left_stack_result_iff_first_event'}
        self.assertLessEqual(required, names)
        types = (self.evidence / 'main-theorem-types.txt').read_text()
        self.assertIn('input : List (Fin symbols)', types)
        self.assertIn('machine : SOnlyTuringUniversality.TapeMachine states symbols', types)
        self.assertIn('controller.InterInvocationState = Unit', types)
        self.assertIn('LeftStackResult', types)

    def test_complete_artifact_manifest(self):
        rows = json.loads((self.evidence / 'manifest.json').read_text())
        for row in rows:
            data = (self.evidence / row['path']).read_bytes()
            self.assertEqual(len(data), row['bytes'], row['path'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'], row['path'])

    def test_wrapper_excludes_canaries_and_unused_experiment(self):
        lines = (self.evidence / 'SOnlyTuringUniversalityReplay.lean').read_text().splitlines()
        self.assertEqual(len(lines), 67)
        self.assertEqual(lines, ['import ' + row['module'] for row in self.result['modules']])
        self.assertFalse(any('Canary' in line or 'InvalidProof' in line or
                             'SOnlyMacroSimulation' in line for line in lines))

    def test_same_checker_negative_controls_and_output_scope(self):
        self.assertEqual(self.result['negative_controls']['status'], 'passed')
        controls = json.loads((ROOT / self.result['negative_controls']['receipt']).read_text())
        self.assertEqual(controls['injected_invalidFalse_fresh_replay_exit'], 1)
        self.assertEqual(controls['valid_proof_fresh_replay_exit'], 0)
        self.assertIn('left stack', self.result['output_convention'])
        self.assertIn('visited extent', self.result['output_convention'])


if __name__ == '__main__':
    unittest.main()
