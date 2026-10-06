"""Exact succinct code for the prioritized table in ``probes.compile_rows``.

Only fixed immutable pattern code and positive-width row intervals are kept.
The existing ``probes.step``/``execute`` runtime is unchanged.  See
``docs/succinct-rows.md`` for the same-index proof and code-only lookup bounds.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .probes import Address, Incoming, Instruction, NodeKind, Pattern
from .succinct_probes import SuccinctProbeTable, compile_pattern


@dataclass(frozen=True, slots=True)
class _PatternCode:
    probe: SuccinctProbeTable
    failure_ticks: int | None


@dataclass(frozen=True, slots=True)
class _RowBlock:
    # Half-open, positive-width intervals in original reverse-row emission order.
    origin: int
    stop: int
    pattern: int
    address: Address
    no: int


def _failure_ticks(probe: SuccinctProbeTable) -> int | None:
    """Compile-time graph profile, measured before the failure continuation."""
    failures: list[int | None] = []
    for node in probe.nodes:
        if node.kind == "_":
            failures.append(None)
        elif node.kind == "S":
            failures.append(1)
        else:
            bound = 1  # The pair's initial node-kind test can fail.
            left, right = failures[node.left], failures[node.right]
            if left is not None:
                bound = max(bound, 3 + left)
            if right is not None:
                bound = max(bound, 5 + probe.nodes[node.left].ticks + right)
            failures.append(bound)
    return failures[probe.root]


def _validate_selection(probe: SuccinctProbeTable, address: Address) -> None:
    if type(address) is not tuple or any(
        type(direction) is not int or direction not in (0, 1) for direction in address
    ):
        raise ValueError("an address is an immutable tuple of 0/1 directions")
    descriptor = probe.root
    for direction in address:
        node = probe.nodes[descriptor]
        if node.kind != "pair":
            raise ValueError("row address must be guaranteed by its pattern")
        descriptor = node.left if direction == 0 else node.right


def _row_bound(code: _PatternCode, address_length: int, remaining: int) -> int:
    success = code.probe.tick_bound + address_length
    return success if code.failure_ticks is None else max(
        success, code.failure_ticks + remaining
    )


@dataclass(frozen=True, slots=True)
class SuccinctRowsTable:
    """Exactly the original row table, including every unreachable control.

    ``patterns`` contains immutable standalone code objects.  ``blocks`` records
    their distinct occurrence intervals; sharing code never merges controls.
    Zero-width wildcard rows are represented by continuation/start resets to 1.
    """

    patterns: tuple[_PatternCode, ...]
    blocks: tuple[_RowBlock, ...]
    start: int
    ticks: int

    def __post_init__(self):
        if type(self.patterns) is not tuple or type(self.blocks) is not tuple:
            raise ValueError("patterns and blocks must be immutable tuples")
        for code in self.patterns:
            if type(code) is not _PatternCode or type(code.probe) is not SuccinctProbeTable:
                raise ValueError("patterns must contain exact immutable pattern code")
            # Validate all plain descriptor fields even for unused pattern code.
            SuccinctProbeTable.__post_init__(code.probe)
            failure = code.failure_ticks
            if failure is not None and (type(failure) is not int or failure < 0):
                raise ValueError("failure profiles must be plain nonnegative integers or None")
            if failure != _failure_ticks(code.probe):
                raise ValueError("failure profile disagrees with the pattern code")
        if type(self.start) is not int:
            raise ValueError("start must be a plain integer")
        if type(self.ticks) is not int or self.ticks < 0:
            raise ValueError("ticks must be a plain nonnegative integer")

        origin, previous_entry, bound = 2, 0, 0
        for block in self.blocks:
            if type(block) is not _RowBlock:
                raise ValueError("blocks must be exact immutable row blocks")
            if any(type(value) is not int or value < 0
                   for value in (block.origin, block.stop, block.pattern, block.no)):
                raise ValueError("block indices must be plain nonnegative integers")
            if block.pattern >= len(self.patterns):
                raise ValueError("unknown row pattern code")
            code = self.patterns[block.pattern]
            _validate_selection(code.probe, block.address)
            width = len(block.address) + code.probe.state_count - 2
            if width == 0 or block.origin != origin or block.stop != origin + width:
                raise ValueError("blocks must partition the nonterminal controls without gaps")
            if block.no not in (1, previous_entry):
                raise ValueError("row failure must continue to the previous row or a wildcard")
            # A skipped zero-state wildcard cuts off the previous suffix.
            bound = _row_bound(code, len(block.address), 0 if block.no == 1 else bound)
            previous_entry, origin = block.stop - 1, block.stop
        if self.start not in (1, previous_entry):
            raise ValueError("start must be the final row entry or a wildcard")
        expected_ticks = bound if self.start >= 2 else 0
        if self.ticks != expected_ticks:
            raise ValueError("tick bound disagrees with the row graph")

    @property
    def state_count(self) -> int:
        return self.blocks[-1].stop if self.blocks else 2

    @property
    def tick_bound(self) -> int:
        """Exact longest control-graph path, not necessarily a realizable trace."""
        return self.ticks

    @property
    def block_lookup_bound(self) -> int:
        """Maximum binary-search iterations for the fixed block list."""
        return len(self.blocks).bit_length()

    @property
    def pattern_lookup_depth_bound(self) -> int:
        return max((code.probe.lookup_depth_bound for code in self.patterns), default=0)

    @property
    def lookup_depth_bound(self) -> int:
        """Bound on block-search plus selected-pattern decoder iterations."""
        return self.block_lookup_bound + self.pattern_lookup_depth_bound

    def _validate_control(self, control: int) -> None:
        if type(control) is not int or not 0 <= control < self.state_count:
            raise ValueError("unknown finite control")

    def answer(self, control: int) -> bool | None:
        self._validate_control(control)
        return bool(control) if control < 2 else None

    def transition(self, control: int, kind: NodeKind, incoming: Incoming) -> Instruction:
        """Decode only from immutable code, a control, and one of six observations."""
        self._validate_control(control)
        if (type(kind) is not str or kind not in ("S", "application")
                or type(incoming) is not str or incoming not in ("root", "L", "R")):
            raise ValueError("unknown local observation")
        if control < 2:
            return Instruction("true" if control else "false")

        low, high = 0, len(self.blocks)
        while low < high:
            middle = (low + high) // 2
            block = self.blocks[middle]
            if control < block.origin:
                high = middle
            elif control >= block.stop:
                low = middle + 1
            else:
                break
        # Constructor validation proves the positive intervals partition [2,N).
        address_length = len(block.address)
        pattern_origin = block.origin + address_length
        if control < pattern_origin:
            offset = control - block.origin
            direction = block.address[address_length - offset - 1]
            return Instruction("L" if direction == 0 else "R",
                               1 if offset == 0 else control - 1)

        probe = self.patterns[block.pattern].probe
        instruction = probe.transition(control - pattern_origin + 2, kind, incoming)
        target = instruction.next_state
        if target == 0:
            target = block.no
        elif target == 1:
            target = pattern_origin - 1 if address_length else 1
        else:
            target += pattern_origin - 2
        return Instruction(instruction.command, target)


def compile_rows(rows: Iterable[tuple[Pattern, Address]]) -> SuccinctRowsTable:
    """Compile original row indices without unfolding shared pattern occurrences.

    Identity caches exist only here.  The prepared source keeps root objects
    alive while their identities are keys; no input tuple is hashed or compared.
    Equal but separately allocated pattern roots need not share code.
    """
    prepared = tuple(rows)
    patterns: list[_PatternCode] = []
    compiled: list[tuple[int, Address]] = []
    identities: dict[int, int] = {}
    for row in prepared:
        if type(row) is not tuple or len(row) != 2:
            raise ValueError("each row must be a (pattern, address) pair")
        pattern, address = row
        identity = id(pattern)
        if identity not in identities:
            probe = compile_pattern(pattern)
            identities[identity] = len(patterns)
            patterns.append(_PatternCode(probe, _failure_ticks(probe)))
        index = identities[identity]
        _validate_selection(patterns[index].probe, address)
        compiled.append((index, address))

    blocks: list[_RowBlock] = []
    origin, remaining, bound = 2, 0, 0
    for index, address in reversed(compiled):
        code = patterns[index]
        width = len(address) + code.probe.state_count - 2
        if width == 0:
            remaining, bound = 1, 0
            continue
        stop = origin + width
        blocks.append(_RowBlock(origin, stop, index, address, remaining))
        remaining = stop - 1
        bound = _row_bound(code, len(address), bound)
        origin = stop
    return SuccinctRowsTable(tuple(patterns), tuple(blocks), remaining, bound)
