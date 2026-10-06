"""Bounded exact graphs and archived seed-11 runs for succinct periods 1/3/4/5.

One materialized reference is retained at a time and released before native
execution. Archive data, source readout, counters and hashes are external
checks; they never guide the primitive controller. Python deadlines are soft.
Use the documented external launcher for hard time/address-space bounds.
"""
import argparse
import gc
import hashlib
import json
import math
from pathlib import Path
import time

from s_only.cts import Program
from s_only.cts_reader import compile_reader
from s_only.program_selector_parts.compiler import CompilationLimit, compile_table as dense_compile
from s_only.succinct_periodic import compile_table
from tools.program_selector_report import ExperimentLimit as NativeLimit, run_one
from tools.succinct_selector_report import ExperimentLimit, _before_deadline, verify_graph

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_PATH = 'results/positive_period_programs.json'
ARCHIVE_SHA256 = 'e54cede3399a9902a66777a33ce63c7b87b3c6a46a51b1ef968112d4073cc017'
SOURCE_COMMIT = '85a867988442fc423279341200f81634a1e65582'
# Original same-index graph and measured immutable representation counts.
CASES = (
    (('01',), 129268, 111742, 314, 16431, 36,
     '01d339bb54065f6d0d9ca99a106fa21b59deb994c6a8bf09bddac74eee4b0ce5'),
    (('01', '', '01'), 694400, 621444, 426, 70326, 43,
     '38277ee9c55e38ced8ef2c18c4ca54a7e028a1290df1ca063a093624fe4307c1'),
    (('10', '1', '', '10'), 1201863, 1086283, 482, 113584, 42,
     '3bbceb900808d754490988a9d5738749e06abf15fdb8c686325c625e2491cef1'),
    (('01', '', '1', '01', '001'), 2134486, 1945270, 538, 182697, 47,
     '4d9401bb322822819001dc866bc3e9123e59824aa6d5d689787a1dcddd2f34b4'),
)
HARD_LIMIT_COMMAND = (
    "timeout 1200s sh -c 'ulimit -v 2097152; exec python -m "
    "tools.succinct_periodic_report --deterministic --output /tmp/succinct-periodic.json'")


def _positive(value, name):
    if type(value) is not int or value < 1:
        raise ValueError(f'{name} must be a positive integer')


def _seconds(value, name):
    if type(value) is not int and type(value) is not float:
        raise ValueError(f'{name} must be finite and positive')
    try:
        duration = float(value)
    except (OverflowError, ValueError):
        raise ValueError(f'{name} must fit a finite positive clock value') from None
    if not math.isfinite(duration) or duration <= 0:
        raise ValueError(f'{name} must be finite and positive')


def _binary(value):
    return type(value) is str and not set(value) - {'0', '1'}


def _sha256(value):
    return (type(value) is str and len(value) == 64 and
            not set(value) - set('0123456789abcdef'))


def _validate_run(run, period, seed):
    keys = {'seed', 'checkpoints', 'native_contractions', 'samples_checked',
            'noncheckpoint_samples', 'selected_addresses', 'selection_microticks',
            'max_selection_microticks', 'peak_expanded_nodes'}
    if type(run) is not dict or set(run) != keys or run['seed'] != seed:
        raise ValueError('unexpected archived run structure or seed')
    for name in keys - {'seed', 'checkpoints', 'selected_addresses'}:
        _positive(run[name], f'archived {name}')
    n = run['native_contractions']
    if (run['samples_checked'] != n + 1 or run['noncheckpoint_samples'] != n - 2 or
            type(run['selected_addresses']) is not list or
            len(run['selected_addresses']) != n or
            not all(_binary(path) for path in run['selected_addresses']) or
            type(run['checkpoints']) is not list or len(run['checkpoints']) != 3):
        raise ValueError('inconsistent archived run counts or paths')
    previous = -1
    for horizon, checkpoint in enumerate(run['checkpoints']):
        if (type(checkpoint) is not dict or set(checkpoint) !=
                {'horizon', 'phase', 'data', 'native_contractions',
                 'expanded_nodes', 'prefix_sha256'}):
            raise ValueError('unexpected archived checkpoint structure')
        if (type(checkpoint['horizon']) is not int or checkpoint['horizon'] != horizon or
                type(checkpoint['phase']) is not int or
                not 0 <= checkpoint['phase'] < period or not _binary(checkpoint['data']) or
                type(checkpoint['native_contractions']) is not int or
                not previous < checkpoint['native_contractions'] <= n or
                not _sha256(checkpoint['prefix_sha256'])):
            raise ValueError('invalid archived checkpoint data')
        _positive(checkpoint['expanded_nodes'], 'archived expanded_nodes')
        previous = checkpoint['native_contractions']
    if (run['checkpoints'][0]['native_contractions'] != 0 or previous != n or
            run['checkpoints'][0]['data'] != seed or run['checkpoints'][0]['phase'] != 0):
        raise ValueError('inconsistent initial/final archived checkpoints')


def _validate_archive(archive):
    if (type(archive) is not dict or archive.get('schema') != 's-only-positive-period-programs-v1' or
            archive.get('source_commit') != SOURCE_COMMIT or
            type(archive.get('programs')) is not list or len(archive['programs']) != len(CASES)):
        raise ValueError('unexpected positive-period archive structure')
    for archived, case in zip(archive['programs'], CASES):
        words, states, _, _, _, _, digest = case
        if (type(archived) is not dict or archived.get('appendants') != list(words) or
                type(archived.get('period')) is not int or archived['period'] != len(words) or
                type(archived.get('finite_control_states')) is not int or
                archived['finite_control_states'] != states or
                archived.get('control_table_sha256') != digest or
                type(archived.get('runs')) is not list or len(archived['runs']) != 3):
            raise ValueError('unexpected archived program/graph metadata')
        for run, seed in zip(archived['runs'], ('11', '1', '')):
            _validate_run(run, len(words), seed)


def _load_archive():
    raw = (ROOT / ARCHIVE_PATH).read_bytes()
    archive = json.loads(raw)
    _validate_archive(archive)
    checksum = hashlib.sha256(raw).hexdigest()
    if checksum != ARCHIVE_SHA256:
        raise ValueError('positive-period archive checksum differs from the frozen source')
    return archive, checksum


def _capacity(archive, *, max_states, max_phases, max_appendant_bits,
              max_metadata_records, max_steps, max_ticks, max_nodes):
    requirements = (
        ('comparison states', max_states, max(case[1] for case in CASES)),
        ('phases', max_phases, max(len(case[0]) for case in CASES)),
        ('appendant bits', max_appendant_bits, max(sum(map(len, case[0])) for case in CASES)),
        ('metadata records', max_metadata_records, max(case[4] for case in CASES)),
    )
    runs = [program['runs'][0] for program in archive['programs'][1:]]
    requirements += (
        ('native contractions', max_steps, max(run['native_contractions'] for run in runs)),
        ('selection microticks', max_ticks, max(run['max_selection_microticks'] for run in runs)),
        ('expanded nodes', max_nodes, max(run['peak_expanded_nodes'] for run in runs)),
    )
    for name, available, required in requirements:
        if available < required:
            raise ExperimentLimit(f'report requires at least {required} {name}; supplied {available}')


def report(*, max_states=3_000_000, max_phases=5, max_appendant_bits=8,
           max_metadata_records=250_000, max_compile_seconds=15,
           max_steps=120, max_ticks=200_000, max_nodes=2_000_000, max_seconds=1000):
    for name, value in (('max_states', max_states), ('max_metadata_records', max_metadata_records),
                        ('max_steps', max_steps), ('max_ticks', max_ticks), ('max_nodes', max_nodes)):
        _positive(value, name)
    if type(max_phases) is not int or not 1 <= max_phases <= 5:
        raise ValueError('max_phases must be an integer from 1 through 5')
    if type(max_appendant_bits) is not int or not 0 <= max_appendant_bits <= 8:
        raise ValueError('max_appendant_bits must be an integer from 0 through 8')
    _seconds(max_compile_seconds, 'max_compile_seconds')
    _seconds(max_seconds, 'max_seconds')
    started = time.monotonic()
    deadline = started + max_seconds
    archive, checksum = _load_archive()
    _capacity(archive, max_states=max_states, max_phases=max_phases,
              max_appendant_bits=max_appendant_bits, max_metadata_records=max_metadata_records,
              max_steps=max_steps, max_ticks=max_ticks, max_nodes=max_nodes)
    records = []
    for expected, case in zip(archive['programs'], CASES):
        _before_deadline(deadline)
        words, states, start, intervals, metadata, depth, digest = case
        program = Program(words)
        table = compile_table(program, max_phases=max_phases, max_appendant_bits=max_appendant_bits,
                              max_metadata_records=max_metadata_records,
                              max_compile_seconds=max_compile_seconds)
        _before_deadline(deadline)
        if (table.state_count, table.start, len(table.blocks), table.metadata_records,
                table.lookup_depth_bound) != (states, start, intervals, metadata, depth):
            raise AssertionError('succinct fixed-program representation counts changed')
        reference = dense_compile(program, required_period=None, max_states=max_states,
                                  max_appendant_bits=max_appendant_bits, max_phases=max_phases)
        graph = verify_graph(table, reference, max_states=max_states, deadline=deadline,
                             expected_sha256=digest)
        # No cache or result field retains the reference. Release it before
        # native execution and before compiling the following program.
        del reference
        gc.collect()
        _before_deadline(deadline)
        record = {'appendants': list(words), 'period': len(words),
                  'finite_control_states': states, 'start': start, 'intervals': intervals,
                  'referenced_metadata_records': metadata, 'lookup_depth_bound': depth, **graph}
        if len(words) > 1:
            run = run_one(program, table, compile_reader(program), '11', target_horizon=2,
                          max_steps=max_steps, max_ticks=max_ticks, max_nodes=max_nodes,
                          deadline=deadline)
            _before_deadline(deadline)
            if run != expected['runs'][0]:
                raise AssertionError(f'period-{len(words)} seed-11 run differs from archived output')
            record['seed11_run'] = run
        records.append(record)
        del table
        gc.collect()
    _before_deadline(deadline)
    runs = [record['seed11_run'] for record in records if 'seed11_run' in record]
    return {
        'schema': 's-only-succinct-periodic-v1',
        'scope': 'exact graphs for periods 1/3/4/5; seed 11 through horizon 2 for periods 3/4/5',
        'sources': {'archive': ARCHIVE_PATH, 'archive_sha256': checksum,
                    'archive_source_commit': SOURCE_COMMIT,
                    'succinct_compiler': 's_only/succinct_periodic.py',
                    'materialized_compiler': 's_only/program_selector_parts/compiler.py',
                    'graph_checker': 'tools/succinct_selector_report.py:verify_graph',
                    'native_checker': 'tools/program_selector_report.py:run_one'},
        'runtime': 'unchanged root_selector.step/erase; fresh fixed control and root per invocation',
        'comparison_method': 'serial exact graphs; one materialized reference at a time, released before native run',
        'memory_caveat': 'The verifier materializes references and does not demonstrate low peak process RSS.',
        'metadata_count_definition': 'referenced record slots, counted separately per embed; not bytes or integer bit lengths',
        'cross_fragment_interning': False,
        'graph_digest_format': 'control:observation-index:command:next-state followed by LF; None is literal',
        'observations_per_state': 6,
        'external_bounds': {'comparison_states': max_states, 'phases': max_phases,
                            'total_appendant_bits': max_appendant_bits, 'metadata_records': max_metadata_records,
                            'soft_compile_seconds': max_compile_seconds, 'soft_wall_seconds': max_seconds,
                            'native_contractions_per_run': max_steps,
                            'selection_microticks_per_invocation': max_ticks,
                            'implied_selection_microticks_per_run': max_steps * max_ticks,
                            'expanded_nodes': max_nodes},
        'external_process_envelope': {'hard_timeout_seconds': 1200, 'address_space_limit_kib': 2097152,
                                      'enforcement': 'external launcher only; not enforced by Python report',
                                      'reproduction_command': HARD_LIMIT_COMMAND},
        'graph_count': len(records),
        'entries_checked': sum(record['entries_checked'] for record in records),
        'statuses_checked': sum(record['statuses_checked'] for record in records),
        'run_count': len(runs),
        'native_contractions_checked': sum(run['native_contractions'] for run in runs),
        'selection_microticks_checked': sum(run['selection_microticks'] for run in runs),
        'structural_samples_checked': sum(run['samples_checked'] for run in runs),
        'checkpoints_checked': sum(len(run['checkpoints']) for run in runs),
        'full_archived_seed11_runs_match': True,
        'programs': records,
        'elapsed_seconds': round(time.monotonic() - started, 6),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    for flag, default in (('max-states', 3000000), ('max-phases', 5), ('max-appendant-bits', 8),
                          ('max-metadata-records', 250000), ('max-steps', 120),
                          ('max-microticks', 200000), ('max-nodes', 2000000)):
        parser.add_argument('--' + flag, type=int, default=default)
    parser.add_argument('--max-compile-seconds', type=float, default=15)
    parser.add_argument('--max-seconds', type=float, default=1000)
    parser.add_argument('--deterministic', action='store_true', help='omit measured elapsed duration')
    args = parser.parse_args()
    try:
        result = report(max_states=args.max_states, max_phases=args.max_phases,
                        max_appendant_bits=args.max_appendant_bits,
                        max_metadata_records=args.max_metadata_records,
                        max_compile_seconds=args.max_compile_seconds, max_steps=args.max_steps,
                        max_ticks=args.max_microticks, max_nodes=args.max_nodes, max_seconds=args.max_seconds)
    except (ValueError, CompilationLimit, ExperimentLimit, NativeLimit, AssertionError) as error:
        parser.error(str(error))
    if args.deterministic:
        result.pop('elapsed_seconds', None)
    content = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(content)
    print(content, end='')


if __name__ == '__main__':
    main()
