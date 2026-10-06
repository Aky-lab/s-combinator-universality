"""Bounded positive-period controller compilation and native S checkpoints."""
import argparse
import json
from pathlib import Path
import time

from s_only.cts import Program
from s_only.cts_reader import compile_reader
from s_only.periodic_selector import CompilationLimit, selector_table
from tools.program_selector_report import (
    ExperimentLimit, SOURCE_COMMIT, _graph_digest, _positive, _time_limit, run_one,
)


PROGRAMS = (('01',), ('01', '', '01'), ('10', '1', '', '10'),
            ('01', '', '1', '01', '001'))
SEEDS = ('11', '1', '')


def report(*, max_states=3_000_000, max_steps=180, max_ticks=2_000_000,
           max_nodes=5_000_000, max_seconds=600):
    for value, name in ((max_states, 'max_states'), (max_steps, 'max_steps'),
                        (max_ticks, 'max_ticks'), (max_nodes, 'max_nodes')):
        _positive(value, name)
    _time_limit(max_seconds)
    started = time.monotonic()
    deadline = started + max_seconds
    records = []
    for appendants in PROGRAMS:
        if time.monotonic() >= deadline:
            raise ExperimentLimit('external soft wall-clock bound reached')
        program = Program(appendants)
        # This cache is compile-time storage, unrelated to runtime selection.
        selector_table.cache_clear()
        attempts = []
        caps = ((min(2_000_000, max_states), max_states)
                if len(appendants) == 5 else (max_states,))
        table = None
        for cap in dict.fromkeys(caps):
            if time.monotonic() >= deadline:
                raise ExperimentLimit('external soft wall-clock bound reached')
            try:
                table = selector_table(program, max_states=cap,
                                       max_appendant_bits=128, max_phases=16)
            except CompilationLimit as error:
                attempts.append({'state_cap': cap, 'status': 'construction_limit',
                                 'reason': str(error)})
            else:
                attempts.append({'state_cap': cap, 'status': 'compiled'})
                break
        if table is None:
            raise CompilationLimit(f'program {appendants!r} exhausted the configured construction caps')
        reader = compile_reader(program)
        records.append({'appendants': list(appendants), 'period': len(appendants),
                        'compilation_attempts': attempts,
                        'finite_control_states': len(table.states),
                        'control_table_sha256': _graph_digest(table),
                        'runs': [run_one(program, table, reader, seed,
                                         target_horizon=2, max_steps=max_steps,
                                         max_ticks=max_ticks, max_nodes=max_nodes,
                                         deadline=deadline) for seed in SEEDS]})
        del table
        selector_table.cache_clear()
    runs = [run for record in records for run in record['runs']]
    return {'schema': 's-only-positive-period-programs-v1',
            'source_commit': SOURCE_COMMIT,
            'scope': 'periods 1, 3, 4 and 5; three seeds and two checked horizons each',
            'source_semantics': 'ordinary CTS until empty; empty-word phase advance thereafter',
            'runtime_observation': 'finite control, node kind and incoming side',
            'external_bounds': {'control_states': max_states, 'total_appendant_bits': 128,
                                'phases': 16, 'native_contractions_per_run': max_steps,
                                'selection_microticks_per_invocation': max_ticks,
                                'expanded_nodes': max_nodes, 'soft_wall_seconds': max_seconds},
            'elapsed_seconds': round(time.monotonic() - started, 6),
            'run_count': len(runs),
            'native_contractions_checked': sum(run['native_contractions'] for run in runs),
            'structural_samples_checked': sum(run['samples_checked'] for run in runs),
            'accepted_samples': sum(len(run['checkpoints']) for run in runs),
            'programs': records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--max-states', type=int, default=3_000_000)
    parser.add_argument('--max-steps', type=int, default=180)
    parser.add_argument('--max-microticks', type=int, default=2_000_000)
    parser.add_argument('--max-nodes', type=int, default=5_000_000)
    parser.add_argument('--max-seconds', type=float, default=600)
    parser.add_argument('--deterministic', action='store_true')
    args = parser.parse_args()
    try:
        result = report(max_states=args.max_states, max_steps=args.max_steps,
                        max_ticks=args.max_microticks, max_nodes=args.max_nodes,
                        max_seconds=args.max_seconds)
    except (ValueError, ExperimentLimit) as error:
        parser.error(str(error))
    if args.deterministic:
        result.pop('elapsed_seconds')
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')


if __name__ == '__main__':
    main()
