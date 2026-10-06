"""Exact interval-coded prototype of a small fixed-program selector graph.

Compilation reuses the original graph constructors and their emission order.
Runtime decodes a primitive row from immutable code and six observations; it
never consults a source tree, compiler, saved cursor, or mutable lookup cache.
See ``docs/succinct-selector.md`` for the precise scope and cost model.
"""
from __future__ import annotations

from dataclasses import dataclass
import math
import time

from .cts import Program
from .probes import OBSERVATIONS
from .root_selector import SelectorTable, _euler
from .selector_parts.graph import Command, GraphBuilder
from .program_selector_parts.compiler import CompilationLimit
from .succinct_probes import SuccinctProbeTable, compile_pattern
from .succinct_rows import SuccinctRowsTable, compile_rows
from .succinct_walkers import (
    SuccinctInverseRowsTable, SuccinctWalkerTable, compile_inverse_rows,
    compile_descent, compile_ascent,
)

_FRAGMENT_TYPES = (SuccinctProbeTable, SuccinctRowsTable,
                   SuccinctInverseRowsTable, SuccinctWalkerTable)


@dataclass(frozen=True, slots=True)
class _DirectRow:
    origin: int
    row: tuple[Command, ...]

    @property
    def stop(self):
        return self.origin + 1


@dataclass(frozen=True, slots=True)
class _Fragment:
    origin: int
    table: SuccinctProbeTable | SuccinctRowsTable | SuccinctInverseRowsTable | SuccinctWalkerTable
    yes: int
    no: int

    @property
    def dropped(self):
        return 1 if type(self.table) is SuccinctWalkerTable else 2

    @property
    def stop(self):
        return self.origin + self.table.state_count - self.dropped

    def rebase(self, old):
        if old == 0:
            return self.no
        if old == 1 and self.dropped == 2:
            return self.yes
        return self.origin + old - self.dropped


def _fragment_records(table):
    """Referenced record slots, counting duplicated code separately per embed.

    Each table header, pattern-code record, descriptor, row block and address
    direction is one slot. This is a reproducible representation count, not a
    claim about Python bytes or integer bit lengths.
    """
    if type(table) is SuccinctWalkerTable:
        return 1 + _fragment_records(table.probe)
    if type(table) is SuccinctProbeTable:
        return 1 + len(table.nodes)
    return (1 + sum(1 + _fragment_records(code.probe) for code in table.patterns)
            + sum(1 + len(block.address) for block in table.blocks))


def _validate_fragment(table):
    if not any(type(table) is accepted for accepted in _FRAGMENT_TYPES):
        raise ValueError('an exact immutable succinct fragment is required')
    type(table).__post_init__(table)


@dataclass(frozen=True, slots=True)
class SuccinctSelectorTable:
    """The exact original finite graph, represented by contiguous intervals.

    There is intentionally no ``states`` collection. ``state_count`` can be
    larger than ``sys.maxsize``. Use explicit capped ``materialize`` only for
    small external comparisons. The original root_selector runtime accepts
    this table's start/status/transition methods without any runtime changes.
    """

    blocks: tuple[_DirectRow | _Fragment, ...]
    start: int

    def __post_init__(self):
        if type(self.blocks) is not tuple or not self.blocks:
            raise ValueError('nonempty immutable interval code required')
        origin = 0
        for block in self.blocks:
            if type(block) is not _DirectRow and type(block) is not _Fragment:
                raise ValueError('unknown interval record')
            if type(block.origin) is not int or block.origin != origin:
                raise ValueError('intervals must cover all controls without gaps')
            if type(block) is _Fragment:
                _validate_fragment(block.table)
            if block.stop <= origin:
                raise ValueError('empty fragments must not allocate an interval')
            origin = block.stop
        if type(self.start) is not int or not 0 <= self.start < origin:
            raise ValueError('invalid initial control')
        # Reject malformed data globally before equality or Rdx-target checks
        # can inspect a later row. No user-defined comparison is admissible.
        for block in self.blocks:
            if type(block) is _Fragment:
                self._validate_target(block.yes)
                self._validate_target(block.no)
                continue
            if type(block.row) is not tuple or len(block.row) != 6:
                raise ValueError('six immutable observation entries required')
            for entry in block.row:
                if type(entry) is not Command or type(entry.command) is not str:
                    raise ValueError('exact instructions and plain primitive strings required')
                if entry.next_state is not None and type(entry.next_state) is not int:
                    raise ValueError('instruction targets must be plain integers or None')
        for block in self.blocks:
            if type(block) is _Fragment:
                self._validate_target(block.yes)
                self._validate_target(block.no)
                continue
            row = block.row
            if type(row) is not tuple or len(row) != 6:
                raise ValueError('six immutable observation entries required')
            for entry in row:
                if type(entry) is not Command or type(entry.command) is not str:
                    raise ValueError('exact instructions and plain primitive strings required')
                if entry.command in ('normal', 'contracted'):
                    if entry.next_state is not None or any(other != entry for other in row):
                        raise ValueError('terminal must be uniform and absorbing')
                elif entry.command in ('stay', 'L', 'R', 'U', 'Rdx'):
                    self._validate_target(entry.next_state)
                    if entry.command == 'Rdx':
                        if any(other != entry for other in row):
                            raise ValueError('contraction site must be observation-independent')
                        target = self._block(entry.next_state)
                        if (type(target) is not _DirectRow or
                                type(target.row) is not tuple or not target.row or
                                type(target.row[0]) is not Command or
                                target.row[0].command != 'contracted'):
                            raise ValueError('a contraction must end the invocation')
                else:
                    raise ValueError('invalid primitive')

    @property
    def state_count(self):
        return self.blocks[-1].stop

    @property
    def linear_coefficient(self):
        """The original finite-configuration bound, conditional on termination."""
        return self.state_count + 1

    @property
    def metadata_records(self):
        return sum(7 if type(block) is _DirectRow else
                   1 + _fragment_records(block.table) for block in self.blocks)

    @property
    def lookup_depth_bound(self):
        return len(self.blocks).bit_length() + max(
            (block.table.lookup_depth_bound for block in self.blocks
             if type(block) is _Fragment), default=0)

    def _validate_target(self, control):
        if type(control) is not int or not 0 <= control < self.state_count:
            raise ValueError('unknown finite control')

    def _block(self, control):
        low, high = 0, len(self.blocks)
        while low < high:
            middle = (low + high) // 2
            block = self.blocks[middle]
            if control < block.origin:
                high = middle
            elif control >= block.stop:
                low = middle + 1
            else:
                return block
        raise ValueError('unknown finite control')

    def status(self, control):
        self._validate_target(control)
        block = self._block(control)
        if type(block) is _DirectRow:
            command = block.row[0].command
            return command if command in ('normal', 'contracted', 'Rdx') else None
        return None

    def transition(self, control, kind, incoming):
        """Read only finite control, six observations, and fixed immutable code."""
        self._validate_target(control)
        if (type(kind) is not str or kind not in ('S', 'application') or
                type(incoming) is not str or incoming not in ('root', 'L', 'R')):
            raise ValueError('unknown local observation')
        block = self._block(control)
        if type(block) is _DirectRow:
            return block.row[OBSERVATIONS.index((kind, incoming))]
        old = control - block.origin + block.dropped
        entry = block.table.transition(old, kind, incoming)
        return Command(entry.command, block.rebase(entry.next_state))

    def materialize(self, *, max_states):
        """Explicit external comparison adapter; never invoked by the runtime."""
        if type(max_states) is not int or max_states < 1:
            raise ValueError('max_states must be a positive integer')
        if self.state_count > max_states:
            raise CompilationLimit(f'materialization exceeds {max_states} states')
        states = tuple(tuple(self.transition(q, *obs) for obs in OBSERVATIONS)
                       for q in range(self.state_count))
        return SelectorTable(states, self.start)


class _Reservations:
    """Compile-only indexed assignment, deliberately neither iterable nor sized."""
    def __init__(self, builder):
        self._builder = builder

    def __getitem__(self, control):
        if type(control) is not int or control not in self._builder._direct:
            raise ValueError('not a directly reserved control')
        return self._builder._direct[control]

    def __setitem__(self, control, row):
        if self[control] is not None:
            raise ValueError('reserved control already filled')
        self._builder._direct[control] = row

    def __iter__(self):
        raise TypeError('reservations are compile-only indexed assignments')


def _positive_int(value, name):
    if type(value) is not int or value < 1:
        raise ValueError(f'{name} must be a positive integer')


class SuccinctGraphBuilder(GraphBuilder):
    """Compile-only GraphBuilder facade with fixed metadata and soft time caps.

    Never retains a pattern, compiler, clock, reservation dictionary or source
    Program in the finished immutable table. Existing helper functions may use
    reserve/jump and states[index] assignment without virtual-list allocation.
    """
    def __init__(self, *, max_metadata_records=100_000, max_compile_seconds=10):
        _positive_int(max_metadata_records, 'max_metadata_records')
        if type(max_compile_seconds) is not int and type(max_compile_seconds) is not float:
            raise ValueError('max_compile_seconds must be finite and positive')
        try:
            seconds = float(max_compile_seconds)
        except OverflowError as exc:
            raise ValueError('max_compile_seconds must fit a finite clock value') from exc
        if not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('max_compile_seconds must be finite and positive')
        self._limit = max_metadata_records
        self._deadline = time.monotonic() + seconds
        if not math.isfinite(self._deadline):
            raise ValueError('max_compile_seconds must produce a finite deadline')
        self._records = 0
        self._count = 0
        self._pieces = []
        self._direct = {}
        self.states = _Reservations(self)

    @property
    def state_count(self):
        return self._count

    def _check(self, additional=0):
        if self._records + additional > self._limit:
            raise CompilationLimit(f'controller exceeds {self._limit} metadata records')
        if time.monotonic() >= self._deadline:
            raise CompilationLimit('controller exceeds the soft compilation time budget')

    def reserve(self):
        self._check(7)
        state = self._count
        self._count += 1
        self._records += 7
        self._direct[state] = None
        self._pieces.append(state)
        return state

    def embed(self, table, yes, no):
        self._check()
        _validate_fragment(table)
        block = _Fragment(self._count, table, yes, no)
        width = block.stop - block.origin
        if width:
            cost = 1 + _fragment_records(table)
            self._check(cost)
            self._pieces.append(block)
            self._records += cost
            self._count += width
        return block.rebase(table.start)

    def match(self, pattern, yes, no):
        self._check()
        return self.embed(compile_pattern(pattern), yes, no)

    def rows(self, rows, yes, no):
        self._check()
        return self.embed(compile_rows(rows), yes, no)

    def inverse_rows(self, rows, yes, no):
        self._check()
        return self.embed(compile_inverse_rows(rows), yes, no)

    def descent(self, rows, done):
        self._check()
        return self.embed(compile_descent(rows), done, done)

    def ascent(self, rows, done):
        self._check()
        return self.embed(compile_ascent(rows), done, done)

    def finish(self, start):
        self._check()
        if any(row is None for row in self._direct.values()):
            raise ValueError('unresolved finite control')
        blocks = tuple(_DirectRow(piece, self._direct[piece])
                       if type(piece) is int else piece for piece in self._pieces)
        result = SuccinctSelectorTable(blocks, start)
        self._check()
        return result


def compile_table(program, *, max_appendant_bits=8,
                  max_metadata_records=100_000, max_compile_seconds=10):
    """Prototype limited to periods 1/2 and at most eight appendant bits.

    Metadata and cooperative wall-time caps are mandatory. They bound retained
    representation slots and detect slow compilation between fragments, but do
    not preempt a compiler call or bound transient allocation within that call.
    Repeated PatternFamily construction is intentionally unchanged.
    """
    if type(program) is not Program:
        raise TypeError('program must be an exact s_only.cts.Program')
    if len(program.appendants) not in (1, 2):
        raise CompilationLimit('succinct prototype supports only periods 1 and 2')
    if (type(max_appendant_bits) is not int or
            not 0 <= max_appendant_bits <= 8):
        raise ValueError('max_appendant_bits must be an integer from 0 through 8')
    if any(type(word) is not str for word in program.appendants):
        raise ValueError('appendants must be plain binary strings')
    if sum(map(len, program.appendants)) > max_appendant_bits:
        raise CompilationLimit(f'program exceeds {max_appendant_bits} total appendant bits')
    return _assemble_program(program, max_metadata_records=max_metadata_records,
                             max_compile_seconds=max_compile_seconds)


def _assemble_program(program, *, max_metadata_records, max_compile_seconds):
    """Shared original-order composition, after an entry point checks its scope.

    This compile-only helper deliberately does not relax either public API's
    syntax caps or retain the source program in the finished interval code.
    """
    from .program_selector_parts.patterns import PatternFamily
    from .program_selector_parts.active import compile_active
    from .program_selector_parts.priority import compile_fresh, compile_marked
    builder = SuccinctGraphBuilder(max_metadata_records=max_metadata_records,
                                   max_compile_seconds=max_compile_seconds)
    normal = builder.uniform('normal')
    contracted = builder.uniform('contracted')
    selected = builder.uniform('Rdx', contracted)
    fallback = builder.root(_euler(builder, selected, normal))
    p = PatternFamily(program, required_period=None)
    active = compile_active(builder, p, selected, fallback)
    marked = compile_marked(builder, p, selected, builder.root(active))
    fresh = compile_fresh(builder, p, selected, builder.root(marked))
    return builder.finish(fresh)
