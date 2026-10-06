"""Reproduce bounded, prospective fresh-marker events on native S trajectories.

Run with an outer process guard, for example:
    timeout 600s python -m tools.marker_observer_report --deterministic

All counters, exact-tree audits, paths, digests, checkpoint decoding and source
comparison are external instrumentation. Neither finite machine receives them.
The observer has no Euler fallback; the native reduction selector retains it.
"""
import argparse
import json
from pathlib import Path
import time

from s_only.cts import Configuration as SourceState, Program
from s_only.cts_reader import compile_reader
from s_only.encoding import encode, prefix_sha256
from s_only.marker_observer import observer_table, step as observer_step
from s_only.probes import Configuration, Cursor
from s_only.program_selector import selector_table
from s_only.reduction import contract_at, root_arguments
from s_only.root_selector import erase, step
from s_only.terms import App, S, nodes, prefix
from tools.program_selector_report import (
    ExperimentLimit, SOURCE_COMMIT, _graph_digest, _positive, _time_limit,
    totalized_source_step,
)


APPENDANTS = ('1', '')
SEEDS = ('101', '1', '0', '')


def _check_deadline(deadline):
    if time.monotonic() >= deadline:
        raise ExperimentLimit('external soft wall-clock bound reached')


def _observe(table, term, max_ticks, deadline):
    """Fresh read-only runtime; inclusive tick cap belongs to this driver."""
    _positive(max_ticks, 'max_ticks')
    _check_deadline(deadline)
    state = Configuration(table.start, Cursor.at(term))
    ticks = 0
    while table.answer(state.control) is None:
        if ticks >= max_ticks:
            raise ExperimentLimit('external observer microtick bound reached')
        if ticks % 1024 == 0:
            _check_deadline(deadline)
        state = observer_step(table, state)
        ticks += 1
    _check_deadline(deadline)
    if observer_step(table, state) is not state:
        raise AssertionError('observer terminal is not read-only absorbing')
    return state, ticks


def _select(table, term, max_ticks, deadline):
    """Stop before Rdx, so the driver can reject growth before contraction."""
    _positive(max_ticks, 'max_ticks')
    _check_deadline(deadline)
    state = Configuration(table.start, Cursor.at(term))
    ticks = 0
    while table.status(state.control) is None:
        if ticks >= max_ticks:
            raise ExperimentLimit('external selection microtick bound reached')
        if ticks % 1024 == 0:
            _check_deadline(deadline)
        state = step(table, state)
        ticks += 1
    _check_deadline(deadline)
    if table.status(state.control) != 'Rdx':
        raise AssertionError('encoded trajectory reached an unexpected normal form')
    return state, ticks


def _unchanged(term, state, before):
    """Audit exact tokens and every occurrence frame, not just a root hash."""
    current = term
    for frame in state.cursor.parents:
        if frame.parent is not current:
            raise AssertionError('read-only cursor changed its ambient context')
        current = current.left if frame.side == 'L' else current.right
    if state.cursor.focus is not current or prefix(term) != before:
        raise AssertionError('read-only traversal changed its ambient tree')


def _marker_payload(term):
    """Independent literal shape: App(((S S) ((S S) S)), opaque payload)."""
    def b(node):
        return (isinstance(node, App) and isinstance(node.left, type(S))
                and isinstance(node.right, type(S)))
    if not isinstance(term, App) or not isinstance(term.left, App):
        return None
    code = term.left
    if (b(code.left) and isinstance(code.right, App)
            and b(code.right.left) and isinstance(code.right.right, type(S))):
        return term.right
    return None


def _contract(table, selected, term, *, max_nodes):
    """One native Rdx tick, with pre-growth and exact reference-rewrite audits."""
    arguments = root_arguments(selected.cursor.focus)
    if arguments is None:
        raise AssertionError('selected occurrence is not an S redex')
    next_nodes = nodes(term) + nodes(arguments[2]) - 1
    if next_nodes > max_nodes:
        raise ExperimentLimit('next contraction exceeds expanded-node bound')
    terminal = step(table, selected)
    if table.status(terminal.control) != 'contracted' or step(table, terminal) is not terminal:
        raise AssertionError('one-contraction absorbing terminal violated')
    result = erase(terminal.cursor)
    if nodes(result) != next_nodes:
        raise AssertionError('single-contraction size identity failed')
    # This reference never chooses the path or supplies the next runtime tree.
    reference = contract_at(term, selected.cursor.path)
    if prefix(result) != prefix(reference):
        raise AssertionError('result differs from exactly one reference S contraction')
    return result, terminal


def run_one(program, observer, selector, reader, seed, *, max_steps,
            max_ticks, max_nodes, deadline):
    """Observe samples 0..max_steps and perform exactly max_steps contractions."""
    for value, name in ((max_steps, 'max_steps'), (max_ticks, 'max_ticks'),
                        (max_nodes, 'max_nodes')):
        _positive(value, name)
    _check_deadline(deadline)
    term = encode(program, seed)
    samples, markers, checkpoints, selections = [], [], [], []
    expected = [SourceState(seed)]
    last_horizon = -1
    total_observer_ticks = total_selection_ticks = 0
    peak_nodes = nodes(term)
    for sample in range(max_steps + 1):
        if nodes(term) > max_nodes:
            raise ExperimentLimit('external expanded-node bound reached')
        _check_deadline(deadline)
        before = prefix(term)
        observed, observer_ticks = _observe(observer, term, max_ticks, deadline)
        _unchanged(term, observed, before)
        answer = observer.answer(observed.control)
        if type(answer) is not bool:
            raise AssertionError('observer did not return a Boolean')
        path = ''.join(map(str, observed.cursor.path))
        samples.append({'sample': sample, 'answer': answer,
                        'observer_cursor_path': path, 'observer_microticks': observer_ticks,
                        'expanded_nodes': nodes(term)})
        total_observer_ticks += observer_ticks
        marker = None
        if answer:
            payload = _marker_payload(observed.cursor.focus)
            if payload is None:
                raise AssertionError('true answer lacks the independent literal marker shape')
            marker = {'sample': sample, 'selected_cursor_path': path,
                      'occurrence_shape': 'HALT payload = ((S S) ((S S) S)) payload',
                      'payload_is_opaque': True, 'expanded_nodes': nodes(observed.cursor.focus),
                      'occurrence_prefix_sha256': prefix_sha256(observed.cursor.focus, max_nodes=max_nodes),
                      'payload_prefix_sha256': prefix_sha256(payload, max_nodes=max_nodes),
                      'contracted_in_this_run': sample < max_steps}
            markers.append(marker)
        # This structural grammar and source comparison are not observer inputs.
        checkpoint = reader.decode(term)
        if checkpoint is not None:
            horizon = checkpoint['horizon']
            if horizon != last_horizon + 1:
                raise AssertionError('checkpoint horizon skipped or repeated')
            while len(expected) <= horizon:
                expected.append(totalized_source_step(program, expected[-1]))
            source = expected[horizon]
            if checkpoint != {'horizon': horizon, 'phase': source.phase, 'data': source.word}:
                raise AssertionError('independent checkpoint/source mismatch')
            checkpoints.append(dict(checkpoint, sample=sample, expanded_nodes=nodes(term),
                                    prefix_sha256=prefix_sha256(term, max_nodes=max_nodes)))
            last_horizon = horizon
        if sample == max_steps:
            break
        selected, selection_ticks = _select(selector, term, max_ticks, deadline)
        _unchanged(term, selected, before)
        selected_path = ''.join(map(str, selected.cursor.path))
        if answer and selected.cursor.path != observed.cursor.path:
            raise AssertionError('marker cursor disagrees with native selected occurrence')
        selections.append({'sample': sample, 'selected_cursor_path': selected_path,
                           'selection_microticks': selection_ticks})
        total_selection_ticks += selection_ticks
        result, terminal = _contract(selector, selected, term, max_nodes=max_nodes)
        if marker is not None:
            if _marker_payload(terminal.cursor.focus) is not None:
                raise AssertionError('marker contraction retained the fresh field')
            # Check the literal marked result S payload (HALT_TAG payload),
            # including the two occurrences of the original opaque payload.
            field = terminal.cursor.focus
            if not (isinstance(field, App) and isinstance(field.left, App)
                    and field.left.left is S and field.left.right is payload
                    and isinstance(field.right, App) and field.right.right is payload
                    and field.right.left is observed.cursor.focus.left.right):
                raise AssertionError('marker contraction did not produce the marked field')
            marker['after_shape'] = 'S payload (HALT_TAG payload)'
            marker['after_occurrence_prefix_sha256'] = prefix_sha256(field, max_nodes=max_nodes)
            marker['native_selection_agrees'] = True
        term = result
        peak_nodes = max(peak_nodes, nodes(term))
    _check_deadline(deadline)
    return {'seed': seed, 'native_contractions': max_steps, 'samples_checked': len(samples),
            'true_samples': [entry['sample'] for entry in markers],
            'false_samples': len(samples) - len(markers),
            'observer_microticks': total_observer_ticks,
            'max_observer_microticks': max(entry['observer_microticks'] for entry in samples),
            'selection_microticks': total_selection_ticks,
            'max_selection_microticks': max(entry['selection_microticks'] for entry in selections),
            'native_primitive_microticks': total_selection_ticks + max_steps,
            'peak_expanded_nodes': peak_nodes,
            'exact_read_only_sample_checks': len(samples),
            'observer_absorbing_terminal_checks': len(samples),
            'exact_one_contraction_checks': len(selections),
            'native_absorbing_terminal_checks': len(selections),
            'checkpoints': checkpoints, 'markers': markers,
            'samples': samples, 'native_selections': selections}


def report(*, max_states=1_000_000, max_steps=100, max_ticks=2_000_000,
           max_nodes=5_000_000, max_seconds=300):
    for value, name in ((max_states, 'max_states'), (max_steps, 'max_steps'),
                        (max_ticks, 'max_ticks'), (max_nodes, 'max_nodes')):
        _positive(value, name)
    _time_limit(max_seconds)
    started = time.monotonic()
    deadline = started + max_seconds
    program = Program(APPENDANTS)
    observer = observer_table(program, max_states=max_states, max_appendant_bits=128,
                              max_phases=16)
    _check_deadline(deadline)
    selector = selector_table(program, max_states=max_states, max_appendant_bits=128)
    _check_deadline(deadline)
    reader = compile_reader(program)
    graphs = {
        'observer': {'finite_control_states': len(observer.states),
                     'control_table_sha256': _graph_digest(observer),
                     'start_control': observer.start, 'euler_fallback': False},
        'native_selector': {'finite_control_states': len(selector.states),
                            'control_table_sha256': _graph_digest(selector),
                            'start_control': selector.start, 'euler_fallback': True},
    }
    runs = [run_one(program, observer, selector, reader, seed, max_steps=max_steps,
                    max_ticks=max_ticks, max_nodes=max_nodes, deadline=deadline)
            for seed in SEEDS]
    result = {
        'schema': 's-only-finite-marker-observer-v1', 'source_commit': SOURCE_COMMIT,
        'appendants': list(APPENDANTS),
        'scope': 'four native trajectories; a fresh observer invocation at every current-tree sample',
        'event': 'successful priority selection at a literal fresh HALT payload redex before contraction',
        'sample_convention': 'sample n is the tree after n native contractions; true concerns the next selected occurrence',
        'source_semantics': 'ordinary CTS until empty; empty-word phase advance thereafter for structural checkpoint comparison only',
        'runtime_inputs': 'precompiled finite table and current S tree only; fresh control and root cursor per invocation',
        'external_instrumentation': 'bounds, counters, paths, exact tokens, hashes, structural reader and source comparison never enter either machine',
        'event_scope': 'A current-tree selection predicate, with marker and checkpoint times recorded separately.',
        'external_bounds': {'control_states_per_graph': max_states, 'total_appendant_bits': 128,
                            'phases': 16, 'native_contractions_per_run': max_steps,
                            'observer_microticks_per_invocation': max_ticks,
                            'selection_microticks_per_invocation': max_ticks,
                            'contraction_microticks_per_native_step': 1,
                            'expanded_nodes': max_nodes, 'soft_wall_seconds': max_seconds},
        'hard_process_guard': 'caller-enforced; reproduction uses timeout 600s and ulimit -v 2097152',
        'graphs': graphs, 'run_count': len(runs),
        'native_contractions_checked': sum(run['native_contractions'] for run in runs),
        'samples_checked': sum(run['samples_checked'] for run in runs),
        'true_samples': sum(len(run['true_samples']) for run in runs),
        'checkpoints_checked': sum(len(run['checkpoints']) for run in runs),
        'observer_microticks': sum(run['observer_microticks'] for run in runs),
        'selection_microticks': sum(run['selection_microticks'] for run in runs),
        'runs': runs,
        'elapsed_seconds': round(time.monotonic() - started, 6),
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--max-states', type=int, default=1_000_000)
    parser.add_argument('--max-steps', type=int, default=100)
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
