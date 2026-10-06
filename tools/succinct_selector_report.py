"""Reproduce the exact legacy graph and its 85-step succinct-controller run.

This external checker deliberately retains one materialized reference table.
It is not a low-peak-RSS experiment. Reference and succinct executions are
serial; neither runtime receives archived or reference choices. All budgets,
addresses, traces, hashes and comparisons remain outside root_selector.step.

For a hard process envelope, launch from the repository root with:
  timeout 180s sh -c 'ulimit -v 1048576; exec python -m tools.succinct_selector_report --deterministic --output results/succinct_selector.json'
The Python time limits are cooperative, not preemptive.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import time

from s_only.cts import Program
from s_only.encoding import encode, prefix_sha256
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.program_selector import selector_table
from s_only.program_selector_parts.compiler import CompilationLimit
from s_only.reduction import at, root_arguments
from s_only.root_selector import erase, step
from s_only.succinct_selector import compile_table
from s_only.terms import App, nodes, prefix

ROOT = Path(__file__).resolve().parents[1]
GRAPH_SHA256 = 'bb4c1f981a8dba4fb14d7f93f55d6f6927c460ebc8263037643903ddec291924'
HARD_LIMIT_COMMAND = (
    "timeout 180s sh -c 'ulimit -v 1048576; exec python -m "
    "tools.succinct_selector_report --deterministic --output results/succinct_selector.json'")


class ExperimentLimit(RuntimeError):
    """An external budget was exhausted; no successful report is emitted."""


def _positive(value, name):
    if type(value) is not int or value < 1:
        raise ValueError(f'{name} must be a positive integer')


def _seconds(value, name):
    if (type(value) is not int and type(value) is not float) or not math.isfinite(value) or value <= 0:
        raise ValueError(f'{name} must be finite and positive')


def _before_deadline(deadline):
    if time.monotonic() >= deadline:
        raise ExperimentLimit('external soft wall-clock bound reached')


def verify_graph(table, reference, *, max_states, deadline, expected_sha256=GRAPH_SHA256):
    """Enumerate a capped graph through lookup; only reference has .states."""
    _positive(max_states, 'max_states')
    _positive(table.state_count, 'state_count')
    if table.state_count > max_states or len(reference.states) > max_states:
        raise ExperimentLimit('external graph comparison state bound reached')
    if table.state_count != len(reference.states) or table.start != reference.start:
        raise AssertionError('graph state count or initial control mismatch')
    digest = hashlib.sha256()
    statuses = {'read_only': 0, 'normal': 0, 'contracted': 0, 'Rdx': 0}
    for control in range(table.state_count):
        if control % 1024 == 0:
            _before_deadline(deadline)
        status = table.status(control)
        if status != reference.status(control):
            raise AssertionError(f'graph status mismatch at control {control}')
        statuses['read_only' if status is None else status] += 1
        for observation, tags in enumerate(OBSERVATIONS):
            entry = table.transition(control, *tags)
            if entry != reference.transition(control, *tags):
                raise AssertionError(f'graph entry mismatch at control {control}, observation {observation}')
            digest.update(f'{control}:{observation}:{entry.command}:{entry.next_state}\n'.encode('ascii'))
    _before_deadline(deadline)
    actual = digest.hexdigest()
    if actual != expected_sha256:
        raise AssertionError('graph digest differs from the archived text-row digest')
    return {'control_table_sha256': actual,
            'entries_checked': table.state_count * len(OBSERVATIONS),
            'statuses_checked': table.state_count, 'status_counts': statuses}


def bounded_selection(table, term, *, max_ticks, max_total_ticks, used_ticks, deadline):
    """Reset each invocation and stop before Rdx; trace is external only.

    Inclusive tick caps allow reaching Rdx on the final permitted tick. The
    trace hashes every read-only configuration, including the selected one,
    as control:node-kind:incoming-side:binary-occurrence-address followed by LF.
    """
    _positive(max_ticks, 'max_ticks')
    _positive(max_total_ticks, 'max_total_ticks')
    if type(used_ticks) is not int or not 0 <= used_ticks <= max_total_ticks:
        raise ValueError('used_ticks must be an integer within the cumulative budget')
    state = Configuration(table.start, Cursor.at(term))
    ticks = 0
    digest = hashlib.sha256()
    while True:
        if ticks % 1024 == 0:
            _before_deadline(deadline)
        address = ''.join(map(str, state.cursor.path))
        digest.update(f'{state.control}:{state.cursor.kind}:{state.cursor.incoming}:{address}\n'.encode('ascii'))
        status = table.status(state.control)
        if status is not None:
            _before_deadline(deadline)
            if status != 'Rdx':
                raise AssertionError('encoded trajectory reached an unexpected terminal')
            if state.cursor.root is not term or at(term, state.cursor.path) is not state.cursor.focus:
                raise AssertionError('selection changed the current bare tree')
            return state, ticks, digest.hexdigest()
        if ticks >= max_ticks:
            raise ExperimentLimit('external per-selection microtick bound reached')
        if used_ticks + ticks >= max_total_ticks:
            raise ExperimentLimit('external cumulative microtick bound reached')
        state = step(table, state)
        ticks += 1


def contract_once(table, selected, term, *, max_nodes, deadline):
    """Check growth before Rdx and verify the exact single-occurrence rewrite."""
    _positive(max_nodes, 'max_nodes')
    _before_deadline(deadline)
    if table.status(selected.control) != 'Rdx' or selected.cursor.root is not term:
        raise AssertionError('contraction requires a selected occurrence in the current tree')
    arguments = root_arguments(selected.cursor.focus)
    if arguments is None:
        raise AssertionError('selected occurrence is not an S redex')
    x, y, z = arguments
    next_nodes = nodes(term) + nodes(z) - 1
    if nodes(term) > max_nodes or next_nodes > max_nodes:
        raise ExperimentLimit('next contraction exceeds expanded-node bound')
    terminal = step(table, selected)
    replacement = terminal.cursor.focus
    if (table.status(terminal.control) != 'contracted' or
            terminal.cursor.parents is not selected.cursor.parents or
            type(replacement) is not App or type(replacement.left) is not App or
            type(replacement.right) is not App or replacement.left.left is not x or
            replacement.left.right is not z or replacement.right.left is not y or
            replacement.right.right is not z):
        raise AssertionError('exact single-contraction replacement or context violated')
    if step(table, terminal) is not terminal:
        raise AssertionError('one-contraction terminal is not immediately absorbing')
    result = erase(terminal.cursor)
    if nodes(result) != next_nodes:
        raise AssertionError('single-contraction size identity failed')
    _before_deadline(deadline)
    return result


def replay(table, fixture, archived_selections, *, max_steps, max_ticks,
           max_total_ticks, max_nodes, deadline):
    """Run independently; consult expected choices only after selection."""
    for name, value in (('max_steps', max_steps), ('max_ticks', max_ticks),
                        ('max_total_ticks', max_total_ticks), ('max_nodes', max_nodes)):
        _positive(value, name)
    if len(fixture['steps']) != len(archived_selections):
        raise AssertionError('fixture and archived selection lengths disagree')
    term = encode(Program(('1', '')), '101')
    if nodes(term) > max_nodes:
        raise ExperimentLimit('initial tree exceeds expanded-node bound')
    if prefix(term) != fixture['initial_prefix']:
        raise AssertionError('fixture initial term differs')
    records = []
    total_ticks = 0
    peak_nodes = nodes(term)
    for index, expected in enumerate(fixture['steps'], 1):
        if index > max_steps:
            raise ExperimentLimit('external native-contraction bound reached')
        selected, ticks, trace = bounded_selection(
            table, term, max_ticks=max_ticks, max_total_ticks=max_total_ticks,
            used_ticks=total_ticks, deadline=deadline)
        address = ''.join(map(str, selected.cursor.path))
        if address != expected['path']:
            raise AssertionError(f'selected address differs at contraction {index}')
        term = contract_once(table, selected, term, max_nodes=max_nodes, deadline=deadline)
        digest = prefix_sha256(term, max_nodes=max_nodes)
        if nodes(term) != expected['nodes'] or digest != expected['after_sha256']:
            raise AssertionError(f'fixture output differs at contraction {index}')
        record = {'contraction': index, 'address': address,
                  'selection_microticks': ticks, 'native_contractions': 1,
                  'after_nodes': nodes(term), 'after_sha256': digest}
        if record != archived_selections[index - 1]:
            raise AssertionError(f'archived selection differs at contraction {index}')
        record['selection_trace_sha256'] = trace
        records.append(record)
        total_ticks += ticks
        peak_nodes = max(peak_nodes, nodes(term))
    _before_deadline(deadline)
    return {'native_contractions_checked': len(records),
            'total_selection_microticks': total_ticks,
            'max_selection_microticks': max((row['selection_microticks'] for row in records), default=0),
            'peak_expanded_nodes': peak_nodes, 'fixture_selections': records}


def report(*, max_states=300_000, max_appendant_bits=8, max_metadata_records=100_000,
           max_compile_seconds=10, max_steps=85, max_ticks=100_000,
           max_total_ticks=2_000_000, max_nodes=400_000, max_seconds=120):
    for name, value in (('max_states', max_states), ('max_metadata_records', max_metadata_records),
                        ('max_steps', max_steps), ('max_ticks', max_ticks),
                        ('max_total_ticks', max_total_ticks), ('max_nodes', max_nodes)):
        _positive(value, name)
    if type(max_appendant_bits) is not int or not 0 <= max_appendant_bits <= 8:
        raise ValueError('max_appendant_bits must be an integer from 0 through 8')
    _seconds(max_compile_seconds, 'max_compile_seconds')
    _seconds(max_seconds, 'max_seconds')
    started = time.monotonic()
    deadline = started + max_seconds
    fixture_bytes = (ROOT / 'fixtures/queue_101_path.json').read_bytes()
    fixture = json.loads(fixture_bytes)
    archive = json.loads((ROOT / 'results/root_selector.json').read_text())
    if (fixture.get('schema') != 's-only-path-v1' or len(fixture['steps']) != 85 or
            archive['native_contractions_checked'] != 85 or
            len(archive['fixture_selections']) != 85 or
            archive['control_table_sha256'] != GRAPH_SHA256):
        raise AssertionError('unexpected fixture or archived reference metadata')
    program = Program(('1', ''))
    compile_started = time.monotonic()
    table = compile_table(program, max_appendant_bits=max_appendant_bits,
                          max_metadata_records=max_metadata_records,
                          max_compile_seconds=max_compile_seconds)
    compile_seconds = time.monotonic() - compile_started
    _before_deadline(deadline)
    # Exactly one deliberately materialized reference; no succinct .states or
    # materialize() adapter is used anywhere in this report.
    reference = selector_table(program, max_states=max_states,
                               max_appendant_bits=max_appendant_bits)
    graph = verify_graph(table, reference, max_states=max_states, deadline=deadline)
    if (table.state_count, table.start, len(table.blocks), table.metadata_records) != (257299, 227379, 370, 33040):
        raise AssertionError('legacy controller representation counts changed')
    limits = dict(max_steps=max_steps, max_ticks=max_ticks, max_total_ticks=max_total_ticks,
                  max_nodes=max_nodes, deadline=deadline)
    reference_run = replay(reference, fixture, archive['fixture_selections'], **limits)
    succinct_run = replay(table, fixture, archive['fixture_selections'], **limits)
    if succinct_run != reference_run:
        raise AssertionError('serial reference and succinct traces disagree')
    if (succinct_run['total_selection_microticks'] != archive['total_selection_microticks'] or
            succinct_run['max_selection_microticks'] != archive['max_selection_microticks']):
        raise AssertionError('archived aggregate microticks disagree')
    return {
        'schema': 's-only-succinct-selector-v1', 'appendants': ['1', ''], 'seed': '101',
        'scope': 'exact legacy graph and archived 85-contraction trajectory',
        'runtime': 'unchanged root_selector.step/erase; fresh fixed control and root per invocation',
        'comparison_method': 'one materialized program_selector reference plus one succinct table; serial runs',
        'memory_caveat': 'This checker retains a materialized reference and does not demonstrate low peak RSS.',
        'metadata_count_definition': 'referenced record slots, counted separately per embed; not bytes or integer bit lengths',
        'finite_control_states': table.state_count, 'start': table.start,
        'intervals': len(table.blocks), 'referenced_metadata_records': table.metadata_records,
        'observations_per_state': len(OBSERVATIONS), **graph,
        'graph_digest_format': 'control:observation-index:command:next-state followed by LF; None is literal',
        'trace_digest_format': 'control:node-kind:incoming-side:binary-address followed by LF; includes initial and selected configurations',
        'fixture_sha256': hashlib.sha256(fixture_bytes).hexdigest(),
        'external_bounds': {'comparison_states': max_states, 'total_appendant_bits': max_appendant_bits,
                            'metadata_records': max_metadata_records, 'soft_compile_seconds': max_compile_seconds,
                            'native_contractions_per_run': max_steps, 'selection_microticks_per_invocation': max_ticks,
                            'selection_microticks_per_run': max_total_ticks, 'expanded_nodes': max_nodes,
                            'soft_wall_seconds': max_seconds},
        'external_process_envelope': {'hard_timeout_seconds': 180, 'address_space_limit_kib': 1048576,
                                      'enforcement': 'external launcher, not the Python report',
                                      'reproduction_command': HARD_LIMIT_COMMAND},
        'compile_seconds': round(compile_seconds, 6),
        'elapsed_seconds': round(time.monotonic() - started, 6),
        'serial_runs_checked': 2,
        'native_contractions_checked_across_both_runs': 2 * succinct_run['native_contractions_checked'],
        'selection_microticks_checked_across_both_runs': 2 * succinct_run['total_selection_microticks'],
        'reference_and_succinct_trace_digests_match': True,
        **succinct_run,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--max-states', type=int, default=300_000)
    parser.add_argument('--max-appendant-bits', type=int, default=8)
    parser.add_argument('--max-metadata-records', type=int, default=100_000)
    parser.add_argument('--max-compile-seconds', type=float, default=10)
    parser.add_argument('--max-steps', type=int, default=85)
    parser.add_argument('--max-microticks', type=int, default=100_000)
    parser.add_argument('--max-total-microticks', type=int, default=2_000_000)
    parser.add_argument('--max-nodes', type=int, default=400_000)
    parser.add_argument('--max-seconds', type=float, default=120)
    parser.add_argument('--deterministic', action='store_true', help='omit measured elapsed durations only')
    args = parser.parse_args()
    try:
        result = report(max_states=args.max_states, max_appendant_bits=args.max_appendant_bits,
                        max_metadata_records=args.max_metadata_records, max_compile_seconds=args.max_compile_seconds,
                        max_steps=args.max_steps, max_ticks=args.max_microticks,
                        max_total_ticks=args.max_total_microticks, max_nodes=args.max_nodes,
                        max_seconds=args.max_seconds)
    except (ValueError, CompilationLimit, ExperimentLimit) as error:
        parser.error(str(error))
    if args.deterministic:
        result.pop('compile_seconds', None)
        result.pop('elapsed_seconds', None)
    content = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(content)
    print(content, end='')


if __name__ == '__main__':
    main()
