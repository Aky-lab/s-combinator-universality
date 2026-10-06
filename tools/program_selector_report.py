"""Reproduce two-phase CTS checkpoints selected by program-static S controllers.

Every counter, digest, source transition and structural readout is external
instrumentation. The controller receives only its finite table and current
tree. Empty source words use the explicitly named totalized readout convention.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import time

from s_only.cts import Configuration as SourceState, Program, step as source_step
from s_only.cts_reader import compile_reader
from s_only.encoding import encode, prefix_sha256
from s_only.probes import Configuration, Cursor
from s_only.program_selector import selector_table
from s_only.reduction import root_arguments
from s_only.root_selector import erase, step
from s_only.terms import nodes


PROGRAMS = (('1', ''), ('0', '10'), ('10', '1'), ('', ''), ('01', '001'))
SEEDS = ('101', '11', '1', '')
SOURCE_COMMIT = '85a867988442fc423279341200f81634a1e65582'


class ExperimentLimit(RuntimeError):
    """A driver resource limit was reached; no success report is emitted."""


def _positive(value, name):
    if type(value) is not int or value < 1:
        raise ValueError(f'{name} must be a positive integer')


def _time_limit(value):
    if type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
        raise ValueError('max_seconds must be finite and positive')


def totalized_source_step(program, source):
    """Ordinary CTS on nonempty queues; advance phase alone on empty queues."""
    if source.word:
        return source_step(program, source)
    return SourceState('', (source.phase + 1) % len(program.appendants))


def _select(table, term, max_ticks, deadline):
    state = Configuration(table.start, Cursor.at(term))
    ticks = 0
    while table.status(state.control) is None:
        if ticks >= max_ticks:
            raise ExperimentLimit('external selection microtick bound reached')
        if ticks % 1024 == 0 and time.monotonic() >= deadline:
            raise ExperimentLimit('external soft wall-clock bound reached')
        state = step(table, state)
        ticks += 1
    if table.status(state.control) != 'Rdx':
        raise AssertionError('encoded trajectory reached an unexpected normal form')
    return state, ticks


def _graph_digest(table):
    digest = hashlib.sha256()
    for control, row in enumerate(table.states):
        for observation, entry in enumerate(row):
            digest.update(f'{control}:{observation}:{entry.command}:{entry.next_state}\n'.encode())
    return digest.hexdigest()


def run_one(program, table, reader, seed, *, target_horizon, max_steps,
            max_ticks, max_nodes, deadline):
    """Stop on the requested checked horizon, with no source feedback to selection."""
    for value, name in ((target_horizon, 'target_horizon'), (max_steps, 'max_steps'),
                        (max_ticks, 'max_ticks'), (max_nodes, 'max_nodes')):
        _positive(value, name)
    expected = [SourceState(seed)]
    for _ in range(target_horizon):
        expected.append(totalized_source_step(program, expected[-1]))
    term = encode(program, seed)
    accepted, selections = [], []
    peak_nodes = nodes(term)
    total_ticks = max_seen_ticks = 0
    last_horizon = -1
    for native_steps in range(max_steps + 1):
        if nodes(term) > max_nodes:
            raise ExperimentLimit('external expanded-node bound reached')
        if time.monotonic() >= deadline:
            raise ExperimentLimit('external soft wall-clock bound reached')
        checkpoint = reader.decode(term)
        if checkpoint is not None:
            horizon = checkpoint['horizon']
            if not 0 <= horizon <= target_horizon:
                raise AssertionError('unexpected checkpoint horizon')
            source = expected[horizon]
            if checkpoint != {'horizon': horizon, 'phase': source.phase, 'data': source.word}:
                raise AssertionError(f'checkpoint/source mismatch: {checkpoint!r}')
            if horizon < last_horizon or horizon > last_horizon + 1:
                raise AssertionError('checkpoint sequence skipped or reversed a horizon')
            last_horizon = horizon
            accepted.append(dict(checkpoint, native_contractions=native_steps,
                                 expanded_nodes=nodes(term),
                                 prefix_sha256=prefix_sha256(term, max_nodes=max_nodes)))
            if horizon == target_horizon:
                return {'seed': seed, 'checkpoints': accepted,
                        'native_contractions': native_steps,
                        'samples_checked': native_steps + 1,
                        'noncheckpoint_samples': native_steps + 1 - len(accepted),
                        'selected_addresses': selections,
                        'selection_microticks': total_ticks,
                        'max_selection_microticks': max_seen_ticks,
                        'peak_expanded_nodes': peak_nodes}
        if native_steps == max_steps:
            raise ExperimentLimit('external native-contraction bound reached')
        selected, ticks = _select(table, term, max_ticks, deadline)
        arguments = root_arguments(selected.cursor.focus)
        if arguments is None:
            raise AssertionError('selected occurrence is not an S redex')
        # Both sides contain three application nodes; only S is replaced by z.
        next_nodes = nodes(term) + nodes(arguments[2]) - 1
        if next_nodes > max_nodes:
            raise ExperimentLimit('next contraction exceeds expanded-node bound')
        # The path is recorded only after the controller has selected it.
        selections.append(''.join(map(str, selected.cursor.path)))
        terminal = step(table, selected)
        if table.status(terminal.control) != 'contracted' or step(table, terminal) is not terminal:
            raise AssertionError('one-contraction absorbing terminal violated')
        term = erase(terminal.cursor)
        if nodes(term) != next_nodes:
            raise AssertionError('single-contraction size identity failed')
        total_ticks += ticks
        max_seen_ticks = max(max_seen_ticks, ticks)
        peak_nodes = max(peak_nodes, next_nodes)
    raise AssertionError('unreachable driver exit')


def report(*, max_states=1_000_000, max_steps=150, max_ticks=2_000_000,
           max_nodes=5_000_000, max_seconds=300):
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
        table = selector_table(program, max_states=max_states, max_appendant_bits=128)
        reader = compile_reader(program)
        records.append({'appendants': list(appendants),
                        'finite_control_states': len(table.states),
                        'control_table_sha256': _graph_digest(table),
                        'runs': [run_one(program, table, reader, seed,
                                         target_horizon=2, max_steps=max_steps,
                                         max_ticks=max_ticks, max_nodes=max_nodes,
                                         deadline=deadline) for seed in SEEDS]})
    runs = [run for record in records for run in record['runs']]
    return {'schema': 's-only-two-phase-programs-v1', 'source_commit': SOURCE_COMMIT,
            'scope': 'five program-static two-phase controllers; four seeds and two horizons each',
            'source_semantics': 'ordinary CTS until empty; empty-word phase advance thereafter',
            'runtime_observation': 'finite control, node kind and incoming side',
            'external_bounds': {'control_states': max_states,
                                'total_appendant_bits': 128,
                                'native_contractions_per_run': max_steps,
                                'selection_microticks_per_invocation': max_ticks,
                                'expanded_nodes': max_nodes,
                                'soft_wall_seconds': max_seconds},
            'elapsed_seconds': round(time.monotonic() - started, 6),
            'run_count': len(runs),
            'native_contractions_checked': sum(run['native_contractions'] for run in runs),
            'structural_samples_checked': sum(run['samples_checked'] for run in runs),
            'accepted_samples': sum(len(run['checkpoints']) for run in runs),
            'programs': records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--max-states', type=int, default=1_000_000)
    parser.add_argument('--max-steps', type=int, default=150)
    parser.add_argument('--max-microticks', type=int, default=2_000_000)
    parser.add_argument('--max-nodes', type=int, default=5_000_000)
    parser.add_argument('--max-seconds', type=float, default=300)
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
    content = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(content)
    print(content, end='')


if __name__ == '__main__':
    main()
