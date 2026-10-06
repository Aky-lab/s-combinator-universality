"""Exact succinct inverse-row probes and finite looping spine walkers.

Immutable code decodes the original control indices without materializing the
forward validation table or inverse matcher occurrences. Execution uses the
unchanged ``walkers.step`` / ``walkers.execute`` occurrence-zipper runtime.
See ``docs/succinct-walkers.md`` for the indexing and resource proofs.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .probes import Address, Incoming, Instruction, NodeKind, Pattern
from .succinct_probes import SuccinctProbeTable, compile_pattern
from .succinct_rows import (
    SuccinctRowsTable, _PatternCode, _failure_ticks, _validate_selection,
    compile_rows,
)


@dataclass(frozen=True, slots=True)
class _InverseRowBlock:
    # Original reverse-row emission order; every scoped strict row has width > 0.
    origin: int
    stop: int
    pattern: int
    address: Address
    no: int


def _inverse_bound(code: _PatternCode, depth: int, remaining: int) -> int:
    """Exact control-graph DP, not a claim of simultaneous input attainment."""
    success = 2 * depth + code.probe.tick_bound
    # An incoming-side miss after j upward moves costs 2*j+1+j,
    # maximized at j=depth-1. A matcher miss restores all depth edges.
    failure = 3 * depth - 2
    if code.failure_ticks is not None:
        failure = max(failure, 3 * depth + code.failure_ticks)
    return max(success, failure + remaining)


@dataclass(frozen=True, slots=True)
class SuccinctInverseRowsTable:
    """Exactly ``walkers.compile_inverse_rows``, including unused controls.

    Pattern code can be shared, while every row's unfolded matcher retains its
    own state interval and continuation targets. No invocation changes code.
    """

    patterns: tuple[_PatternCode, ...]
    blocks: tuple[_InverseRowBlock, ...]
    start: int
    ticks: int

    def __post_init__(self):
        if type(self.patterns) is not tuple or type(self.blocks) is not tuple:
            raise ValueError("patterns and blocks must be immutable tuples")
        for code in self.patterns:
            if type(code) is not _PatternCode or type(code.probe) is not SuccinctProbeTable:
                raise ValueError("patterns must contain exact immutable pattern code")
            # Also validate unused metadata and reject plain-type lookalikes.
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

        origin, remaining, bound = 2, 0, 0
        for block in self.blocks:
            if type(block) is not _InverseRowBlock:
                raise ValueError("blocks must be exact immutable inverse row blocks")
            if any(type(value) is not int or value < 0
                   for value in (block.origin, block.stop, block.pattern, block.no)):
                raise ValueError("block indices must be plain nonnegative integers")
            if block.pattern >= len(self.patterns):
                raise ValueError("unknown row pattern code")
            code = self.patterns[block.pattern]
            _validate_selection(code.probe, block.address)
            depth = len(block.address)
            if not depth:
                raise ValueError("spine feedback requires nonempty child addresses")
            width = code.probe.state_count - 2 + 3 * depth
            if block.origin != origin or block.stop != origin + width:
                raise ValueError("blocks must partition the nonterminal controls without gaps")
            if block.no != remaining:
                raise ValueError("inverse failure must continue to the previous row")
            bound = _inverse_bound(code, depth, bound)
            remaining, origin = block.stop - 1, block.stop
        if self.start != remaining:
            raise ValueError("start must be the final row entry or false for no rows")
        if self.ticks != bound:
            raise ValueError("tick bound disagrees with the inverse row graph")

    @property
    def state_count(self) -> int:
        return self.blocks[-1].stop if self.blocks else 2

    @property
    def tick_bound(self) -> int:
        """Exact longest path in the original probe's six-observation graph."""
        return self.ticks

    @property
    def block_lookup_bound(self) -> int:
        return len(self.blocks).bit_length()

    @property
    def pattern_lookup_depth_bound(self) -> int:
        return max((code.probe.lookup_depth_bound for code in self.patterns), default=0)

    @property
    def lookup_depth_bound(self) -> int:
        """Static bound on block-search plus matcher-decoder loop iterations."""
        return self.block_lookup_bound + self.pattern_lookup_depth_bound

    def _validate_control(self, control: int) -> None:
        if type(control) is not int or not 0 <= control < self.state_count:
            raise ValueError("unknown finite control")

    def answer(self, control: int) -> bool | None:
        self._validate_control(control)
        return bool(control) if control < 2 else None

    def transition(self, control: int, kind: NodeKind, incoming: Incoming) -> Instruction:
        """Decode from fixed code, one control, and one of six observations."""
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
        # Validated intervals cover exactly [2, state_count).
        depth = len(block.address)
        pattern_origin = block.origin + depth
        pattern_stop = block.stop - 2 * depth
        if control < pattern_origin:
            offset = control - block.origin
            direction = block.address[depth - offset - 1]
            return Instruction("L" if direction == 0 else "R",
                               block.no if offset == 0 else control - 1)
        if control < pattern_stop:
            probe = self.patterns[block.pattern].probe
            instruction = probe.transition(control - pattern_origin + 2, kind, incoming)
            target = instruction.next_state
            if target == 0:
                target = pattern_origin - 1
            elif target != 1:
                target += pattern_origin - 2
            return Instruction(instruction.command, target)

        index, is_test = divmod(control - pattern_stop, 2)
        if not is_test:
            # Scoped nonempty addresses force a pair root, hence W > 0.
            return Instruction("U", control - 1)
        side = "L" if block.address[index] == 0 else "R"
        restored_edges = depth - index - 1
        failure = block.no if restored_edges == 0 else block.origin + restored_edges - 1
        return Instruction("stay", control - 1 if incoming == side else failure)


@dataclass(frozen=True, slots=True)
class SuccinctWalkerTable:
    """Close the unique success state 1 of an immutable row probe to its start.

    The fixed wrapper changes just six entries. It adds neither runtime state
    nor a new execution loop, and its pass bound cuts that feedback edge.
    """

    probe: SuccinctRowsTable | SuccinctInverseRowsTable

    def __post_init__(self):
        if type(self.probe) is not SuccinctRowsTable and type(self.probe) is not SuccinctInverseRowsTable:
            raise ValueError("a walker needs exact immutable row probe code")
        type(self.probe).__post_init__(self.probe)
        if self.start == self.feedback:
            raise ValueError("entry cannot be an empty feedback loop")

    @property
    def state_count(self) -> int:
        return self.probe.state_count

    @property
    def start(self) -> int:
        return self.probe.start

    @property
    def feedback(self) -> int:
        return 1

    @property
    def pass_bound(self) -> int:
        return self.probe.tick_bound

    @property
    def coefficient(self) -> int:
        return self.pass_bound + 1

    @property
    def lookup_depth_bound(self) -> int:
        return self.probe.lookup_depth_bound

    def answer(self, control: int) -> bool | None:
        answer = self.probe.answer(control)
        return None if control == self.feedback else answer

    def transition(self, control: int, kind: NodeKind, incoming: Incoming) -> Instruction:
        instruction = self.probe.transition(control, kind, incoming)
        return Instruction("stay", self.start) if control == self.feedback else instruction


def compile_inverse_rows(rows: Iterable[tuple[Pattern, Address]], *, _factory=None) -> SuccinctInverseRowsTable:
    """Recognize prioritized ancestor candidates with exact failure restoration.

    This duplicates the forward compiler's syntax and scope checks using DAG
    code only. No forward transition table, source tree, or expanded pattern is
    built. Compilation-only identity maps do not survive in the result.
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
            probe = compile_pattern(pattern, _factory=_factory)
            identities[identity] = len(patterns)
            patterns.append(_PatternCode(probe, _failure_ticks(probe)))
        index = identities[identity]
        _validate_selection(patterns[index].probe, address)
        compiled.append((index, address))
    if any(not address for _, address in compiled):
        raise ValueError("spine feedback requires nonempty child addresses")

    blocks: list[_InverseRowBlock] = []
    origin, remaining, bound = 2, 0, 0
    for index, address in reversed(compiled):
        code = patterns[index]
        stop = origin + code.probe.state_count - 2 + 3 * len(address)
        blocks.append(_InverseRowBlock(origin, stop, index, address, remaining))
        remaining = stop - 1
        bound = _inverse_bound(code, len(address), bound)
        origin = stop
    return SuccinctInverseRowsTable(tuple(patterns), tuple(blocks), remaining, bound)


def compile_descent(rows: Iterable[tuple[Pattern, Address]], *, _factory=None) -> SuccinctWalkerTable:
    """Repeat prioritized strict-child selection, exactly as the original table."""
    prepared = tuple(rows)
    forward = compile_rows(prepared, _factory=_factory)
    if any(not address for _, address in prepared):
        raise ValueError("spine feedback requires nonempty child addresses")
    return SuccinctWalkerTable(forward)


def compile_ascent(rows: Iterable[tuple[Pattern, Address]], *, _factory=None) -> SuccinctWalkerTable:
    """Repeat ancestor recognition; reconstruction still needs coherence premises."""
    return SuccinctWalkerTable(compile_inverse_rows(rows, _factory=_factory))
