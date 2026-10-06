"""Bounded, reproducible root-reset selector replication and measurements.

The schedule is an external expected-output oracle only. Selection receives
just the current bare tree and the already compiled fixed controller.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import time

from s_only.probes import Configuration, Cursor
from s_only.queue_fixture import encode
from s_only.reduction import at, root_arguments, select_path as preorder
from s_only.root_selector import erase, selector_table, step
from s_only.terms import App, S, nodes, prefix

ROOT = Path(__file__).resolve().parents[1]
SOURCE_COMMIT = '85a867988442fc423279341200f81634a1e65582'


def bounded_selection(table, term, max_ticks, deadline):
    """Instrumentation only; none of these variables enters the machine."""
    configuration = Configuration(table.start, Cursor.at(term))
    ticks = 0
    limit = min(max_ticks, table.linear_coefficient * (nodes(term) + 1))
    while table.status(configuration.control) is None:
        if ticks >= limit:
            raise RuntimeError(f'external selector microtick limit exceeded: {limit}')
        if ticks % 1024 == 0 and time.monotonic() >= deadline:
            raise RuntimeError('external wall-clock limit exceeded')
        configuration = step(table, configuration)
        ticks += 1
    return configuration, ticks


def _small_terms(max_leaves):
    by_size = {1: [S]}
    for size in range(2, max_leaves + 1):
        by_size[size] = [App(left, right) for cut in range(1, size)
                         for left in by_size[cut] for right in by_size[size - cut]]
    return [term for size in by_size for term in by_size[size]]


def report(max_ticks=2_000_000, max_seconds=120, malformed_leaves=8):
    if type(max_ticks) is not int or max_ticks < 1:
        raise ValueError('max_ticks must be a positive integer')
    if type(max_seconds) not in (int, float) or not math.isfinite(max_seconds) or max_seconds <= 0:
        raise ValueError('max_seconds must be finite and positive')
    if type(malformed_leaves) is not int or malformed_leaves < 1:
        raise ValueError('malformed_leaves must be a positive integer')
    started = time.monotonic()
    deadline = started + max_seconds
    table = selector_table()
    compile_seconds = time.monotonic() - started
    graph_digest = hashlib.sha256()
    for control, row in enumerate(table.states):
        for observation, entry in enumerate(row):
            graph_digest.update(f'{control}:{observation}:{entry.command}:{entry.next_state}\n'.encode())
    data = json.loads((ROOT / 'fixtures/queue_101_path.json').read_text())
    term = encode()
    if prefix(term) != data['initial_prefix']:
        raise AssertionError('fixture initial term differs')
    selections = []
    for index, expected in enumerate(data['steps'], 1):
        configuration, ticks = bounded_selection(table, term, max_ticks, deadline)
        status = table.status(configuration.control)
        address = ''.join(map(str, configuration.cursor.path))
        if status != 'Rdx' or address != expected['path']:
            raise AssertionError(f'first mismatch at contraction {index}: {status} {address!r}, '
                                 f'expected {expected["path"]!r}')
        after = step(table, configuration)
        if table.status(after.control) != 'contracted' or step(table, after) is not after:
            raise AssertionError('one-contraction absorbing terminal violated')
        term = erase(after.cursor)
        digest = hashlib.sha256(prefix(term).encode('ascii')).hexdigest()
        if nodes(term) != expected['nodes'] or digest != expected['after_sha256']:
            raise AssertionError(f'output mismatch at contraction {index}')
        selections.append({'contraction': index, 'address': address,
                           'selection_microticks': ticks, 'native_contractions': 1,
                           'after_nodes': nodes(term), 'after_sha256': digest})
    malformed_count = normal_count = 0
    malformed_ticks = 0
    for candidate in _small_terms(malformed_leaves):
        configuration, ticks = bounded_selection(table, candidate, max_ticks, deadline)
        path = configuration.cursor.path if table.status(configuration.control) == 'Rdx' else None
        expected = preorder(candidate)
        if (path is None) != (expected is None):
            raise AssertionError('normality disagreement on small tree')
        if path is not None and root_arguments(at(candidate, path)) is None:
            raise AssertionError('illegal selection on small tree')
        malformed_count += 1
        normal_count += path is None
        malformed_ticks = max(malformed_ticks, ticks)
    tiny = []
    for word in ((), (0,), (1,), (0, 0), (0, 1), (1, 0), (1, 1)):
        candidate = encode(word)
        paths, ticks_high = [], 0
        for index in range(28):
            configuration, ticks = bounded_selection(table, candidate, max_ticks, deadline)
            if table.status(configuration.control) != 'Rdx':
                raise AssertionError('unexpected tiny-seed normality')
            paths.append(''.join(map(str, configuration.cursor.path)))
            candidate = erase(step(table, configuration).cursor)
            ticks_high = max(ticks_high, ticks)
        if paths[:4] != ['0', '0', '01', '']:
            raise AssertionError('tiny initial CLOCK discrepancy')
        tiny.append({'input': ''.join(map(str, word)), 'native_contractions': 28,
                     'max_selection_microticks': ticks_high, 'after_nodes': nodes(candidate),
                     'after_sha256': hashlib.sha256(prefix(candidate).encode('ascii')).hexdigest(),
                     'selected_addresses': paths})
    return {
        'schema': 's-only-root-selector-v1', 'source_commit': SOURCE_COMMIT,
        'scope': 'fixed two-phase fixture; independent finite selector, no general universality claim',
        'finite_control_states': len(table.states), 'observations_per_state': 6,
        'primitive_commands': ['stay', 'L', 'R', 'U', 'Rdx'],
        'control_table_sha256': graph_digest.hexdigest(),
        'linear_configuration_bound_coefficient': table.linear_coefficient,
        'linear_bound_premise': 'Deterministic read-only prefix terminates; finite-configuration counting alone does not prove totality',
        'external_max_selection_microticks': max_ticks, 'external_max_seconds': max_seconds,
        'compile_seconds': round(compile_seconds, 6),
        'elapsed_seconds': round(time.monotonic() - started, 6),
        'native_contractions_checked': len(selections),
        'max_selection_microticks': max(row['selection_microticks'] for row in selections),
        'total_selection_microticks': sum(row['selection_microticks'] for row in selections),
        'fixture_selections': selections,
        'exhaustive_malformed': {'max_leaves': malformed_leaves, 'trees': malformed_count,
                                 'normal_trees': normal_count, 'reducible_trees': malformed_count - normal_count,
                                 'max_selection_microticks': malformed_ticks},
        'tiny_initial_runs': tiny,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--max-microticks', type=int, default=2_000_000)
    parser.add_argument('--max-seconds', type=float, default=120)
    parser.add_argument('--deterministic', action='store_true',
                        help='omit wall-clock durations from the recorded output')
    args = parser.parse_args()
    if args.max_microticks < 1 or not math.isfinite(args.max_seconds) or args.max_seconds <= 0:
        parser.error('bounds must be positive')
    result = report(args.max_microticks, args.max_seconds)
    if args.deterministic:
        result.pop('compile_seconds', None)
        result.pop('elapsed_seconds', None)
    content = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(content)
    print(content, end='')


if __name__ == '__main__':
    main()
