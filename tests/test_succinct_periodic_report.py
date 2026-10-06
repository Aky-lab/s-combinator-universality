"""Fast adversarial checks for the bounded positive-period report driver."""
from contextlib import ExitStack, contextmanager, redirect_stderr, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch
import weakref

from tools import succinct_periodic_report as runner


ARCHIVE_BYTES = (runner.ROOT / runner.ARCHIVE_PATH).read_bytes()
ARCHIVE = json.loads(ARCHIVE_BYTES)


def forbidden(*args, **kwargs):
    raise AssertionError('expensive work must not begin')


@contextmanager
def fake_experiment(*, damage_table=None, damage_run=None):
    """No real graph allocation; verify references die before following work."""
    references, calls = [], []
    cases = {words: case for case in runner.CASES for words in (case[0],)}
    class Reference:
        pass
    def compact(program, **limits):
        if any(ref() is not None for ref in references):
            raise AssertionError('previous materialized reference retained')
        case = cases[program.appendants]
        table = SimpleNamespace(state_count=case[1], start=case[2], blocks=(None,) * case[3],
                                metadata_records=case[4], lookup_depth_bound=case[5],
                                words=program.appendants)
        if damage_table:
            damage_table(table)
        calls.append(('compact', program.appendants, dict(limits)))
        return table
    def dense(program, **limits):
        if any(ref() is not None for ref in references):
            raise AssertionError('two materialized references retained')
        reference = Reference()
        reference.words = program.appendants
        references.append(weakref.ref(reference))
        calls.append(('dense', program.appendants, dict(limits)))
        return reference
    def verify(table, reference, **limits):
        if table.words != reference.words:
            raise AssertionError('wrong reference program')
        case = cases[table.words]
        if limits['expected_sha256'] != case[6]:
            raise AssertionError('wrong graph digest')
        calls.append(('graph', table.words, dict(limits)))
        return {'control_table_sha256': case[6], 'entries_checked': 6 * case[1],
                'statuses_checked': case[1],
                'status_counts': {'read_only': case[1] - 3, 'normal': 1, 'contracted': 1, 'Rdx': 1}}
    def reader(program):
        return program.appendants
    def native(program, table, readout, seed, **limits):
        if any(ref() is not None for ref in references):
            raise AssertionError('materialized reference retained during native execution')
        if readout != program.appendants or table.words != program.appendants or seed != '11':
            raise AssertionError('wrong native runtime inputs')
        calls.append(('native', program.appendants, dict(limits)))
        result = deepcopy(next(p['runs'][0] for p in ARCHIVE['programs']
                               if p['appendants'] == list(program.appendants)))
        if damage_run:
            damage_run(result)
        return result
    with ExitStack() as patches:
        for name, replacement in (('compile_table', compact), ('dense_compile', dense),
                                  ('verify_graph', verify), ('compile_reader', reader), ('run_one', native)):
            patches.enter_context(patch.object(runner, name, new=replacement))
        yield calls, references


class SuccinctPeriodicReportTests(unittest.TestCase):
    def test_invalid_options_precede_archive_and_expensive_work(self):
        cases = [{name: value} for name in ('max_states', 'max_metadata_records', 'max_steps',
                                            'max_ticks', 'max_nodes')
                 for value in (None, True, 0, -1, 1.5)]
        cases += [{name: value} for name in ('max_seconds', 'max_compile_seconds')
                  for value in (None, True, 0, -1, float('inf'), float('nan'), 10**400)]
        cases += [{'max_phases': value} for value in (None, True, 0, -1, 6, 1.5)]
        cases += [{'max_appendant_bits': value} for value in (None, True, -1, 9, 1.5)]
        with patch.object(runner, '_load_archive', new=forbidden), \
             patch.object(runner, 'compile_table', new=forbidden), \
             patch.object(runner, 'dense_compile', new=forbidden):
            for arguments in cases:
                with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                    runner.report(**arguments)

    def test_identity_duration_whitelist_rejects_custom_comparisons_and_conversions(self):
        class Poison(type):
            def __eq__(self, other):
                raise AssertionError('custom type comparison')
            def __ne__(self, other):
                raise AssertionError('custom type comparison')
        class Unknown(metaclass=Poison):
            def __float__(self):
                raise AssertionError('custom float conversion')
        class Number(int, metaclass=Poison):
            pass
        for value in (Unknown(), Number(1)):
            for name in ('max_seconds', 'max_compile_seconds'):
                with self.assertRaises(ValueError):
                    runner.report(**{name: value})
        for value in (1, 0.001, 1e308):
            runner._seconds(value, 'seconds')

    def test_insufficient_fixed_coverage_budgets_precede_compilation(self):
        cases = {'max_states': 2134485, 'max_phases': 4, 'max_appendant_bits': 7,
                 'max_metadata_records': 182696, 'max_steps': 110,
                 'max_ticks': 164433, 'max_nodes': 1687062}
        with patch.object(runner, 'compile_table', new=forbidden), \
             patch.object(runner, 'dense_compile', new=forbidden):
            for name, value in cases.items():
                with self.subTest(name=name), self.assertRaisesRegex(runner.ExperimentLimit, 'report requires'):
                    runner.report(**{name: value})

    def test_archive_structure_is_validated_before_expensive_work(self):
        mutations = (
            lambda a: a.update(schema='other'),
            lambda a: a.update(source_commit='bad'),
            lambda a: a.update(programs=a['programs'][:-1]),
            lambda a: a['programs'][0].update(appendants=['10']),
            lambda a: a['programs'][0].update(period=True),
            lambda a: a['programs'][0].update(finite_control_states=True),
            lambda a: a['programs'][0].update(control_table_sha256='0' * 64),
            lambda a: a['programs'][0].update(runs=[]),
            lambda a: a['programs'][0]['runs'][0].update(seed='1'),
            lambda a: a['programs'][0]['runs'][0].update(extra='unexpected'),
            lambda a: a['programs'][0]['runs'][0].update(selection_microticks=True),
            lambda a: a['programs'][0]['runs'][0].update(native_contractions=1.0),
            lambda a: a['programs'][0]['runs'][0].update(samples_checked=1),
            lambda a: a['programs'][0]['runs'][0].update(noncheckpoint_samples=1),
            lambda a: a['programs'][0]['runs'][0].update(selected_addresses=['x']),
            lambda a: a['programs'][0]['runs'][0].update(checkpoints=[]),
            lambda a: a['programs'][0]['runs'][0]['checkpoints'][0].update(horizon=True),
            lambda a: a['programs'][0]['runs'][0]['checkpoints'][0].update(phase=1),
            lambda a: a['programs'][0]['runs'][0]['checkpoints'][0].update(data='x'),
            lambda a: a['programs'][0]['runs'][0]['checkpoints'][0].update(prefix_sha256='bad'),
            lambda a: a['programs'][0]['runs'][0]['checkpoints'][0].update(native_contractions=True),
            lambda a: a['programs'][0]['runs'][0]['checkpoints'][0].update(expanded_nodes=0),
        )
        with patch.object(runner, 'compile_table', new=forbidden), \
             patch.object(runner, 'dense_compile', new=forbidden):
            for mutate in mutations:
                archive = deepcopy(ARCHIVE)
                mutate(archive)
                with patch.object(Path, 'read_bytes', return_value=json.dumps(archive).encode()), \
                     self.subTest(mutation=mutate), self.assertRaises(ValueError):
                    runner.report()
        for bad in ([], None, {'schema': 's-only-positive-period-programs-v1'}):
            with self.assertRaises(ValueError):
                runner._validate_archive(bad)

    def test_frozen_archive_checksum_and_sources(self):
        archive, digest = runner._load_archive()
        self.assertEqual(archive, ARCHIVE)
        self.assertEqual(digest, runner.ARCHIVE_SHA256)
        with patch.object(Path, 'read_bytes', return_value=ARCHIVE_BYTES + b'\n'), \
             self.assertRaisesRegex(ValueError, 'checksum'):
            runner._load_archive()

    def test_full_coverage_aggregates_bounds_and_serial_reference_release(self):
        with fake_experiment() as (calls, references):
            result = runner.report()
        self.assertTrue(all(ref() is None for ref in references))
        self.assertEqual([call[0] for call in calls],
                         ['compact', 'dense', 'graph'] + ['compact', 'dense', 'graph', 'native'] * 3)
        self.assertEqual((result['graph_count'], result['run_count']), (4, 3))
        self.assertEqual((result['entries_checked'], result['statuses_checked']), (24960102, 4160017))
        self.assertEqual((result['native_contractions_checked'], result['selection_microticks_checked']),
                         (317, 11178672))
        self.assertEqual((result['structural_samples_checked'], result['checkpoints_checked']), (320, 9))
        self.assertTrue(result['full_archived_seed11_runs_match'])
        self.assertFalse(result['cross_fragment_interning'])
        self.assertEqual(result['sources']['archive_sha256'], runner.ARCHIVE_SHA256)
        self.assertEqual(result['sources']['archive_source_commit'], runner.SOURCE_COMMIT)
        self.assertIn('external launcher', result['external_process_envelope']['enforcement'])
        self.assertEqual(result['external_bounds']['implied_selection_microticks_per_run'], 24000000)
        for kind, words, bounds in calls:
            if kind == 'compact':
                self.assertEqual(bounds, dict(max_phases=5, max_appendant_bits=8,
                                               max_metadata_records=250000, max_compile_seconds=15))
            elif kind == 'dense':
                self.assertEqual(bounds, dict(required_period=None, max_states=3000000,
                                               max_appendant_bits=8, max_phases=5))
            elif kind == 'native':
                self.assertEqual({k: v for k, v in bounds.items() if k != 'deadline'},
                                 dict(target_horizon=2, max_steps=120, max_ticks=200000, max_nodes=2000000))
        self.assertNotIn('seed11_run', result['programs'][0])
        for actual, source in zip(result['programs'][1:], ARCHIVE['programs'][1:]):
            self.assertEqual(actual['seed11_run'], source['runs'][0])

    def test_exact_minimum_budget_boundaries_are_admitted(self):
        with fake_experiment():
            result = runner.report(max_states=2134486, max_metadata_records=182697,
                                   max_steps=111, max_ticks=164434, max_nodes=1687063)
        self.assertEqual(result['external_bounds']['comparison_states'], 2134486)
        self.assertEqual(result['native_contractions_checked'], 317)

    def test_every_fixed_representation_count_is_checked_before_reference_allocation(self):
        changes = {'state_count': 1, 'start': 1, 'blocks': (),
                   'metadata_records': 1, 'lookup_depth_bound': 1}
        for name, value in changes.items():
            with self.subTest(name=name), fake_experiment(
                    damage_table=lambda t: setattr(t, name, value)) as (calls, references), \
                 self.assertRaisesRegex(AssertionError, 'representation counts'):
                runner.report()
            self.assertEqual([call[0] for call in calls], ['compact'])
            self.assertEqual(references, [])

    def test_native_run_comparison_checks_entire_record(self):
        mutations = (
            lambda r: r.update(selection_microticks=r['selection_microticks'] + 1),
            lambda r: r.update(peak_expanded_nodes=r['peak_expanded_nodes'] + 1),
            lambda r: r['selected_addresses'].__setitem__(0, '1'),
            lambda r: r['checkpoints'][1].update(prefix_sha256='0' * 64),
        )
        for mutate in mutations:
            with self.subTest(mutation=mutate), fake_experiment(damage_run=mutate), \
                 self.assertRaisesRegex(AssertionError, 'seed-11 run differs'):
                runner.report()

    def test_soft_deadlines_stop_before_and_between_expensive_steps(self):
        for clock, expected_kinds in (((0, 1000), []),
                                      ((0, 0, 1000), ['compact']),
                                      ((0, 0, 0, 1000), ['compact', 'dense', 'graph'])):
            with self.subTest(clock=clock), fake_experiment() as (calls, _), \
                 patch.object(runner.time, 'monotonic', side_effect=clock), \
                 self.assertRaises(runner.ExperimentLimit):
                runner.report()
            self.assertEqual([call[0] for call in calls], expected_kinds)

    def test_deterministic_cli_removes_only_measured_time_and_matches_written_bytes(self):
        result = {'schema': 'test', 'elapsed_seconds': 1.23,
                  'external_bounds': {'soft_wall_seconds': 1000}, 'programs': [{'period': 3}]}
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / 'report.json'
            output = io.StringIO()
            with patch('sys.argv', ['report', '--deterministic', '--output', str(target)]), \
                 patch.object(runner, 'report', return_value=deepcopy(result)), redirect_stdout(output):
                runner.main()
            expected = {k: v for k, v in result.items() if k != 'elapsed_seconds'}
            self.assertEqual(json.loads(output.getvalue()), expected)
            self.assertEqual(target.read_text(), output.getvalue())
        output = io.StringIO()
        with patch('sys.argv', ['report']), patch.object(runner, 'report', return_value=deepcopy(result)), \
             redirect_stdout(output):
            runner.main()
        self.assertEqual(json.loads(output.getvalue()), result)

    def test_cli_failures_do_not_overwrite_an_existing_report(self):
        errors = (ValueError('bad input'), runner.CompilationLimit('compile cap'),
                  runner.ExperimentLimit('wall cap'), runner.NativeLimit('native cap'),
                  AssertionError('mismatch'))
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / 'report.json'
            target.write_text('previous report\n')
            for error in errors:
                with self.subTest(error=type(error)), patch('sys.argv', ['report', '--output', str(target)]), \
                     patch.object(runner, 'report', side_effect=error), redirect_stderr(io.StringIO()), \
                     self.assertRaises(SystemExit):
                    runner.main()
                self.assertEqual(target.read_text(), 'previous report\n')


if __name__ == '__main__':
    unittest.main()
