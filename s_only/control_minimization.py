"""Exact, offline Mealy minimization of immutable selector control graphs.

All six local observations and every primitive output are retained.  In
particular, ``stay`` is not an epsilon edge.  The quotient remains an ordinary
SelectorTable; its interpreter needs neither this compiler nor the state map.
"""
from __future__ import annotations

from array import array
from collections import deque
from dataclasses import dataclass

from .root_selector import SelectorTable
from .selector_parts.graph import Command


@dataclass(frozen=True, slots=True)
class MinimizationResult:
    """A runtime table plus a compile-time, independently checkable witness."""

    table: SelectorTable
    state_map: tuple[int, ...]


def minimize(table: SelectorTable, *, max_states: int | None = None) -> MinimizationResult:
    """Return the coarsest exact-output bisimulation quotient of all states.

    Unreachable states are included: the witness relates every old control,
    not just those visited in a sample execution.  ``max_states`` limits the
    input graph size before allocating refinement indexes.  Time/memory caps
    for construction and execution belong to the external caller.

    This is smaller-half Hopcroft refinement, with six inverse-edge lists
    and an in-place contiguous partition.  For fixed alphabet size its work
    is O(N log N), and auxiliary storage is O(N); see the accompanying proof.
    """
    if not isinstance(table, SelectorTable):
        raise TypeError('table must be a SelectorTable')
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError('max_states must be a positive integer or None')
    count = len(table.states)
    if max_states is not None and count > max_states:
        raise ValueError(f'input controller exceeds {max_states} states')
    # Signed indices permit -1 as a linked-list sentinel.  Reject instead of
    # silently overflowing the actual platform array representation.
    if count > (1 << (8 * array('i').itemsize - 1)) - 1:
        raise ValueError('controller exceeds the index representation')

    signatures = {}
    for state, row in enumerate(table.states):
        signatures.setdefault(tuple(entry.command for entry in row), []).append(state)
    order = array('i')
    positions = array('i', [0]) * count
    block_of = array('i', [0]) * count
    starts, ends = [], []
    for block, members in enumerate(signatures.values()):
        starts.append(len(order))
        for state in members:
            positions[state] = len(order)
            block_of[state] = block
            order.append(state)
        ends.append(len(order))
    del signatures

    # For each observation a and target t, heads[a][t] begins a linked list
    # of its source states; links[a][source] advances that list.  Absorbing
    # terminal outputs are totalized with self-edges solely for refinement.
    heads = [array('i', [-1]) * count for _ in range(6)]
    links = [array('i', [-1]) * count for _ in range(6)]
    for source, row in enumerate(table.states):
        for observation, entry in enumerate(row):
            target = source if entry.next_state is None else entry.next_state
            links[observation][source] = heads[observation][target]
            heads[observation][target] = source

    work = deque(range(6 * len(starts)))
    marked = [0] * len(starts)
    while work:
        item = work.popleft()
        splitter, observation = divmod(item, 6)
        # Moving predecessors inside their blocks can move splitter members.
        # Snapshot its members before any such swaps occur.
        targets = order[starts[splitter]:ends[splitter]]
        touched = []
        head, link = heads[observation], links[observation]
        for target in targets:
            source = head[target]
            while source != -1:
                block = block_of[source]
                if ends[block] - starts[block] > 1:
                    if not marked[block]:
                        touched.append(block)
                    marked[block] += 1
                    destination = ends[block] - marked[block]
                    position = positions[source]
                    displaced = order[destination]
                    order[destination], order[position] = source, displaced
                    positions[source], positions[displaced] = destination, position
                source = link[source]
        for block in touched:
            selected = marked[block]
            marked[block] = 0
            first, last = starts[block], ends[block]
            size = last - first
            if selected == size:
                continue
            boundary = last - selected
            new_block = len(starts)
            # Keep the larger part under the old id.  Each new id therefore
            # holds at most half its old block; only these members relabel.
            if selected <= size // 2:
                starts.append(boundary)
                ends.append(last)
                ends[block] = boundary
            else:
                starts.append(first)
                ends.append(boundary)
                starts[block] = boundary
            marked.append(0)
            for position in range(starts[new_block], ends[new_block]):
                block_of[order[position]] = new_block
            # If an old block was queued, its retained id still represents
            # the larger half and the new half is now also queued.  If not,
            # the smaller half alone suffices (complement argument).
            work.extend(range(6 * new_block, 6 * new_block + 6))

    # Canonical numbering by first old state keeps results deterministic even
    # if internal partition ordering changes.  No reachability pruning occurs.
    canonical, representatives, mapping = {}, [], []
    for state, block in enumerate(block_of):
        if block not in canonical:
            canonical[block] = len(representatives)
            representatives.append(state)
        mapping.append(canonical[block])
    state_map = tuple(mapping)
    rows = tuple(tuple(Command(entry.command,
                               None if entry.next_state is None else state_map[entry.next_state])
                       for entry in table.states[representative])
                 for representative in representatives)
    quotient = SelectorTable(rows, state_map[table.start])
    return MinimizationResult(quotient, state_map)


def verify_quotient(original: SelectorTable, result: MinimizationResult) -> None:
    """Check the complete finite homomorphism witness without refining it.

    Raises ValueError for an invalid witness.  A successful check proves exact
    trace preservation; it does not independently certify quotient minimality.
    """
    if not isinstance(original, SelectorTable) or not isinstance(result, MinimizationResult):
        raise TypeError('expected a SelectorTable and MinimizationResult')
    quotient, mapping = result.table, result.state_map
    if not isinstance(quotient, SelectorTable):
        raise ValueError('invalid quotient table')
    if type(mapping) is not tuple or len(mapping) != len(original.states):
        raise ValueError('one immutable mapped control is required per source state')
    if any(type(state) is not int or not 0 <= state < len(quotient.states) for state in mapping):
        raise ValueError('invalid mapped control')
    if len(set(mapping)) != len(quotient.states):
        raise ValueError('quotient contains an unmapped state')
    if quotient.start != mapping[original.start]:
        raise ValueError('initial control is not preserved')
    for state, row in enumerate(original.states):
        for old, new in zip(row, quotient.states[mapping[state]]):
            if old.command != new.command:
                raise ValueError('primitive output is not preserved')
            expected = None if old.next_state is None else mapping[old.next_state]
            if new.next_state != expected:
                raise ValueError('successor control is not preserved')


def graph_digest(table: SelectorTable) -> str:
    """Stable SHA-256 over documented command bytes and unsigned 64-bit ids."""
    from hashlib import sha256
    from struct import pack
    digest = sha256(b'selector-table-v1\0')
    digest.update(pack('>QQ', len(table.states), table.start))
    commands = {name: code for code, name in enumerate(
        ('normal', 'contracted', 'stay', 'L', 'R', 'U', 'Rdx'))}
    for row in table.states:
        for entry in row:
            digest.update(pack('>BQ', commands[entry.command],
                               (1 << 64) - 1 if entry.next_state is None else entry.next_state))
    return digest.hexdigest()


def quotient_report(original: SelectorTable, *, max_states: int | None = None) -> dict:
    """Build and verify a quotient, returning reproducible counts and digests."""
    from hashlib import sha256
    from struct import pack
    result = minimize(original, max_states=max_states)
    verify_quotient(original, result)
    witness = sha256(b'selector-state-map-v1\0')
    witness.update(pack('>Q', len(result.state_map)))
    for state in result.state_map:
        witness.update(pack('>Q', state))
    return {
        'schema': 'selector-exact-mealy-quotient-v1',
        'original_states': len(original.states),
        'quotient_states': len(result.table.states),
        'removed_states': len(original.states) - len(result.table.states),
        'original_graph_sha256': graph_digest(original),
        'quotient_graph_sha256': graph_digest(result.table),
        'state_map_sha256': witness.hexdigest(),
        'verified_observation_entries': 6 * len(original.states),
        'all_states_witness_verified': True,
    }


def _main():
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--program', nargs=2, metavar=('APPENDANT_0', 'APPENDANT_1'),
                        help='compile this two-phase program instead of the legacy table')
    parser.add_argument('--max-states', type=int, default=1_000_000)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.max_states <= 0:
        parser.error('--max-states must be a positive integer')
    if args.program is None:
        from .root_selector import selector_table
        original = selector_table()
        program = None
    else:
        from .cts import Program
        from .program_selector import selector_table
        program = tuple(args.program)
        original = selector_table(Program(program), max_states=args.max_states)
    report = quotient_report(original, max_states=args.max_states)
    report['compiler'] = 'root_selector' if program is None else 'program_selector'
    report['appendants'] = program
    output = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        print(output, end='')
    else:
        args.output.write_text(output, encoding='utf-8')


if __name__ == '__main__':
    _main()
