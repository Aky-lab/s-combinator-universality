"""Fast source-packet tests; no elaboration or full kernel replay is performed."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('replay_formal', ROOT / 'tools/replay_formal.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)


def source_fixture(target):
    project = {f'Project/P{i}.lean': b'prelude\n' for i in range(target.project_module_count)}
    upstream = {f'Upstream/U{i}.lean': b'prelude\n' for i in range(r.UPSTREAM_MODULE_COUNT)}
    upstream.update({name: b'configuration' for name in r.CONFIGS})
    return project, upstream


class ReplayProfileTests(unittest.TestCase):
    def test_default_and_explicit_target_selection(self):
        args = ['--lean-bin', '/toolchain/bin', '--upstream-source', '/upstream', '--check-only']
        self.assertEqual(r.parse_arguments(args).target, 'register')
        for name in ('register', 'turing'):
            with self.subTest(target=name):
                self.assertEqual(r.parse_arguments(args + ['--target', name]).target, name)
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            r.parse_arguments(args + ['--target', 'unpinned'])

    def test_exact_profiles_and_module_counts(self):
        for name, count, manifest, wrapper in (
                ('register', 56, 'results/formal_universality.json', 'SOnlyUniversalityReplay'),
                ('turing', 67, 'results/formal_turing_universality.json', 'SOnlyTuringUniversalityReplay')):
            with self.subTest(target=name):
                target = r.TARGETS[name]
                self.assertEqual(target.project_module_count, count)
                self.assertEqual(target.manifest_path, manifest)
                self.assertEqual(target.wrapper, wrapper)
                project, upstream = source_fixture(target)
                self.assertEqual(len(r.collect_modules(project, upstream, target)), count + 423)
        self.assertEqual(r.TARGETS['register'].manifest_sha256, r.PROJECT_MANIFEST_SHA256)
        self.assertEqual(r.select_target('register').wrapper, r.WRAPPER)

    def test_published_manifests_match_pinned_profile_identities(self):
        for name in r.TARGETS:
            with self.subTest(target=name):
                target = r.select_target(name)
                manifest = r.read_manifest(ROOT / target.manifest_path, target.manifest_sha256)
                self.assertEqual(len(manifest['modules']), target.project_module_count)
                self.assertEqual(manifest['project_module_count'], target.project_module_count)

    def test_unpinned_profile_is_never_replayed(self):
        unpinned = r.TARGETS['turing']._replace(manifest_sha256=None)
        with mock.patch.dict(r.TARGETS, {'turing': unpinned}), self.assertRaisesRegex(
                r.ReplayError, 'no reviewed manifest identity'):
            r.main(['--target', 'turing', '--lean-bin', '/missing',
                    '--upstream-source', '/missing', '--check-only'])

    def test_profile_counts_cannot_be_interchanged(self):
        for name, other in (('register', 'turing'), ('turing', 'register')):
            project, upstream = source_fixture(r.TARGETS[other])
            with self.subTest(target=name), self.assertRaisesRegex(r.ReplayError, 'project and 426 upstream'):
                r.collect_modules(project, upstream, r.TARGETS[name])

    def test_upstream_count_and_config_set_are_fixed(self):
        target = r.TARGETS['register']
        project, upstream = source_fixture(target)
        upstream.pop('lean-toolchain')
        with self.assertRaisesRegex(r.ReplayError, '426 upstream'):
            r.collect_modules(project, upstream, target)
        upstream['unreviewed-config'] = b''
        with self.assertRaisesRegex(r.ReplayError, 'configuration-file set'):
            r.collect_modules(project, upstream, target)

    def test_duplicate_reserved_and_wrapper_modules_are_rejected(self):
        target = r.TARGETS['register']
        for filename in ('Upstream/U0.lean', 'Std/Fake.lean', f'{target.wrapper}.lean'):
            with self.subTest(filename=filename):
                project, upstream = source_fixture(target)
                project[filename] = project.pop('Project/P0.lean')
                with self.assertRaises(r.ReplayError):
                    r.collect_modules(project, upstream, target)

    def test_cli_requires_fresh_build_path(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            r.parse_arguments(['--lean-bin', '/toolchain/bin', '--upstream-source', '/upstream'])
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            (build / 'old.olean').write_bytes(b'stale')
            with self.assertRaisesRegex(r.ReplayError, 'absent or empty'):
                r.main(['--lean-bin', '/missing', '--upstream-source', '/missing', '--build-dir', tmp])

    def test_mocked_build_uses_selected_profile_and_only_fresh_outputs(self):
        """Exercise orchestration with a fake compiler, not proof verification."""
        for name in ('register', 'turing'):
            with self.subTest(target=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                repo, upstream_root, lean_bin = root / 'repo', root / 'upstream', root / 'lean' / 'bin'
                (repo / 'formal').mkdir(parents=True)
                upstream_root.mkdir()
                lean_bin.mkdir(parents=True)
                (lean_bin.parent / 'lib' / 'lean').mkdir(parents=True)
                for tool in ('lean', 'leanchecker'):
                    (lean_bin / tool).touch(mode=0o700)
                build = root / 'new-build'
                # Fixture identity is synthetic; production profiles never learn it.
                target = r.TARGETS[name]._replace(manifest_sha256='d' * 64)
                project, upstream = source_fixture(target)
                rows = [{'module': path[:-5].replace('/', '.'), 'path': path} for path in project]
                manifest = {'modules': rows, 'upstream': {'commit': r.UPSTREAM_COMMIT},
                            'toolchain': {'version': r.VERSION}}
                runs, queried_environments = [], []

                def fake_query(command, **kwargs):
                    queried_environments.append(dict(kwargs['env']))
                    if command[-1] == '--version':
                        return f'Lean (version {r.VERSION}, x86_64, commit {r.LEAN_COMMIT}, Release)'
                    self.assertEqual(command[-1], '--print-prefix')
                    return str(lean_bin.parent)

                def fake_run(command, **kwargs):
                    runs.append((command, kwargs))
                    if '-o' in command:
                        Path(command[command.index('-o') + 1]).write_bytes(b'simulated compiled output')
                    return SimpleNamespace(returncode=0)

                text = io.StringIO()
                with (mock.patch.dict(r.TARGETS, {name: target}),
                      mock.patch.dict(os.environ, {'LEAN_PATH': '/stale/olean', 'ELAN_TOOLCHAIN': 'wrong',
                                                   'LD_PRELOAD': '/stale/loader.so'}),
                      mock.patch.object(r, 'read_manifest', side_effect=[manifest, []]) as read,
                      mock.patch.object(r, 'verified_sources', side_effect=[project, upstream]),
                      mock.patch.object(r.subprocess, 'check_output', side_effect=fake_query),
                      mock.patch.object(r.subprocess, 'run', side_effect=fake_run),
                      contextlib.redirect_stdout(text)):
                    args = ['--lean-bin', str(lean_bin), '--upstream-source', str(upstream_root),
                            '--repo-root', str(repo), '--build-dir', str(build)]
                    if name != 'register':
                        args.extend(['--target', name])
                    self.assertEqual(r.main(args), 0)
                read.assert_any_call(repo / target.manifest_path, target.manifest_sha256)
                read.assert_any_call(repo / 'artifacts/formal-replay-2026-10-06/source-manifest.json',
                                     r.UPSTREAM_MANIFEST_SHA256)
                summary = json.loads((build / 'replay-result.json').read_text())
                self.assertEqual(summary['target'], name)
                self.assertEqual(summary['project_sources'], target.project_module_count)
                self.assertEqual(summary['upstream_modules'], 423)
                self.assertEqual(summary['upstream_configs'], 3)
                self.assertEqual(len(summary['compile_order']), target.project_module_count + 423)
                self.assertEqual(summary['wrapper_module'], target.wrapper)
                self.assertEqual(summary['project_manifest_sha256'], target.manifest_sha256)
                self.assertIn(f'Verified {target.project_module_count} project + 423 upstream', text.getvalue())
                wrapper = ''.join(f"import {row['module']}\n" for row in rows).encode()
                self.assertEqual((build / 'source' / f'{target.wrapper}.lean').read_bytes(), wrapper)
                self.assertEqual(summary['wrapper_sha256'], r.sha256(wrapper))
                self.assertEqual(len(runs), target.project_module_count + 423 + 2)
                self.assertEqual(runs[-1][0], [str(lean_bin / 'leanchecker'), '--fresh', '-v', target.wrapper])
                expected_path = os.pathsep.join((str(build / 'olean'), str(lean_bin.parent / 'lib' / 'lean')))
                for _, call in runs:
                    self.assertEqual(call['env']['LEAN_PATH'], expected_path)
                    self.assertEqual(call['env']['HOME'], str(build / 'home'))
                    self.assertEqual(call['env']['TMPDIR'], str(build / 'tmp'))
                    self.assertNotIn('ELAN_TOOLCHAIN', call['env'])
                    self.assertNotIn('LD_PRELOAD', call['env'])
                self.assertEqual(queried_environments, [
                    {'PATH': str(lean_bin), 'LEAN_NUM_THREADS': '2', 'LANG': 'C.UTF-8'}] * 2)


class ReplayPreflightTests(unittest.TestCase):
    def test_all_import_forms_and_body_boundary(self):
        source = b'''/- outer /- nested -/ -- ignored\n -/\nmodule\npublic import A.B\nimport all C.D\nmeta import E.F\npublic meta import G.H\nimport\n  I.J -- line comment\npublic theorem sample : True := by trivial\n'''
        self.assertEqual(r.parse_imports(source), ['Init', 'A.B', 'C.D', 'E.F', 'G.H', 'I.J'])

    def test_comments_and_fake_imports(self):
        source = b'-- import Fake\n/- import Fake2 -/\nimport Real\ndef s := "import Fake3"\n'
        self.assertEqual(r.parse_imports(source), ['Init', 'Real'])

    def test_prelude(self):
        self.assertEqual(r.parse_imports(b'prelude\nimport A\n'), ['A'])

    def test_invalid_header(self):
        for source in (b'/- unfinished', b'import ', b'import all ', b'import import'):
            with self.subTest(source=source), self.assertRaises(r.ReplayError):
                r.parse_imports(source)

    def test_paths(self):
        for value in ('../x', '/x', 'a/../b', 'a\\b', '', 'a//b', './a'):
            with self.subTest(value=value), self.assertRaises(r.ReplayError):
                r.safe_relative(value)
        self.assertEqual(r.safe_relative('A/B.lean'), Path('A/B.lean'))

    def test_build_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            r.validate_build_directory(root / 'absent')
            r.validate_build_directory(root)
            (root / 'old.olean').write_bytes(b'stale')
            with self.assertRaises(r.ReplayError):
                r.validate_build_directory(root)
            alias = root / 'alias'
            alias.symlink_to(root, target_is_directory=True)
            with self.assertRaises(r.ReplayError):
                r.validate_build_directory(alias)

    def test_identity_and_tampering(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            data = b'import Std\n'
            path = root / 'A.lean'
            path.write_bytes(data)
            rows = [{'path': 'A.lean', 'bytes': len(data), 'sha256': r.sha256(data)}]
            self.assertEqual(r.verified_sources(root, rows), {'A.lean': data})
            path.write_bytes(b'import Bad\n')
            with self.assertRaises(r.ReplayError):
                r.verified_sources(root, rows)

    def test_manifest_identity_includes_exact_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'manifest.json'
            data = b'{"sources": []}\n'
            path.write_bytes(data)
            self.assertEqual(r.read_manifest(path, r.sha256(data)), {'sources': []})
            path.write_bytes(data + b' ')
            with self.assertRaisesRegex(r.ReplayError, 'Manifest identity mismatch'):
                r.read_manifest(path, r.sha256(data))

    def test_git_blob_identity_and_duplicate_source_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            data = b'prelude\n'
            (root / 'A.lean').write_bytes(data)
            blob = b'blob ' + str(len(data)).encode() + b'\0' + data
            row = {'path': 'A.lean', 'bytes': len(data), 'sha256': r.sha256(data),
                   'git_blob_sha1': hashlib.sha1(blob).hexdigest()}
            self.assertEqual(r.verified_sources(root, [row]), {'A.lean': data})
            with self.assertRaisesRegex(r.ReplayError, 'Duplicate manifest path'):
                r.verified_sources(root, [row, row])
            row['git_blob_sha1'] = '0' * 40
            with self.assertRaisesRegex(r.ReplayError, 'Git blob identity mismatch'):
                r.verified_sources(root, [row])

    def test_source_symlink_cannot_escape_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            root = base / 'source'
            root.mkdir()
            outside = base / 'outside.lean'
            outside.write_bytes(b'prelude\n')
            (root / 'A.lean').symlink_to(outside)
            row = {'path': 'A.lean', 'bytes': 8, 'sha256': r.sha256(b'prelude\n')}
            with self.assertRaisesRegex(r.ReplayError, 'escapes its supplied root'):
                r.verified_sources(root, [row])

    def test_order_unknown_dependencies_and_cycles(self):
        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp)
            (lib / 'Init.olean').write_bytes(b'')
            order, external = r.dependency_order({'A': b'import B\n', 'B': b'\n'}, lib)
            self.assertEqual(order, ['B', 'A'])
            self.assertEqual(external, ['Init'])
            with self.assertRaises(r.ReplayError):
                r.dependency_order({'A': b'import B\n', 'B': b'import A\n'}, lib)
            with self.assertRaises(r.ReplayError):
                r.dependency_order({'A': b'import Unpinned\n'}, lib)
            with self.assertRaises(r.ReplayError):
                r.dependency_order({'A': b'import Std.Missing\n'}, lib)


if __name__ == '__main__':
    unittest.main()
