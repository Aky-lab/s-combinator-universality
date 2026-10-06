"""Bounded construction-time sharing of exact immutable selector code.

This opt-in prototype has the same five-phase/eight-bit scope as
``succinct_periodic``. It shares equal descriptor and probe values during
compilation, not finite controls or runtime computations. See
``docs/pooled-selector.md`` for validation, budgets and measurement caveats.
"""
from __future__ import annotations

from dataclasses import dataclass
import time

from .cts import Program
from .program_selector_parts.compiler import CompilationLimit
from .succinct_probes import _Descriptor, SuccinctProbeTable, compile_pattern
from .succinct_rows import compile_rows
from .succinct_walkers import compile_inverse_rows, compile_descent, compile_ascent
from .succinct_selector import (
    SuccinctGraphBuilder, SuccinctSelectorTable, _assemble_program, _positive_int,
)


@dataclass(frozen=True, slots=True)
class PoolStatistics:
    """Compile-only counts, not retained bytes or a peak-memory estimate.

    Requests count validated candidate objects, including discarded equal
    candidates. Entries count all values retained by the pool at completion,
    including values absent from the finished controller. Pools never evict,
    so retained entries also give their maximum entry count.
    """

    descriptor_requests: int
    probe_requests: int
    descriptor_entries: int
    probe_entries: int

    @property
    def descriptor_hits(self):
        return self.descriptor_requests - self.descriptor_entries

    @property
    def probe_hits(self):
        return self.probe_requests - self.probe_entries

    @property
    def peak_pool_entries(self):
        return self.descriptor_entries + self.probe_entries


def _validate_descriptor(value):
    """Reject lookalikes before hashing or equality can invoke user code.

    Child-relative count recurrences are checked by SuccinctProbeTable before
    a complete probe becomes a key. This preliminary check proves every field
    in a descriptor key is an exact primitive with safe equality and hashing.
    """
    if type(value) is not _Descriptor:
        raise ValueError('the pool accepts only exact immutable descriptors')
    if type(value.kind) is not str or value.kind not in ('_', 'S', 'pair'):
        raise ValueError('unknown descriptor kind')
    if any(type(count) is not int or count < 0
           for count in (value.width, value.ticks, value.height)):
        raise ValueError('descriptor counts must be nonnegative plain integers')
    if value.kind == 'pair':
        if any(type(child) is not int or child < 0 for child in (value.left, value.right)):
            raise ValueError('pair indices must be nonnegative plain integers')
    else:
        if value.left is not None or value.right is not None:
            raise ValueError('leaves cannot have child descriptors')
        width = int(value.kind == 'S')
        if (value.width, value.ticks, value.height) != (width, width, 1):
            raise ValueError('invalid leaf counts')


class _CodePool:
    """Private, per-compilation factory; never reachable from emitted code."""

    def __init__(self, *, max_pool_records=100_000, deadline=None):
        _positive_int(max_pool_records, 'max_pool_records')
        self._limit = max_pool_records
        self._deadline = deadline
        self._descriptors = {}
        self._probes = {}
        self._descriptor_requests = 0
        self._probe_requests = 0

    def _check(self, additional=0):
        if len(self._descriptors) + len(self._probes) + additional > self._limit:
            raise CompilationLimit(f'code pool exceeds {self._limit} retained entries')
        if self._deadline is not None and time.monotonic() >= self._deadline:
            raise CompilationLimit('controller exceeds the soft compilation time budget')

    def descriptor(self, value):
        _validate_descriptor(value)
        self._check()
        self._descriptor_requests += 1
        retained = self._descriptors.get(value)
        if retained is None:
            self._check(1)
            self._descriptors[value] = value
            retained = value
        return retained

    def probe(self, value):
        if type(value) is not SuccinctProbeTable:
            raise ValueError('the pool accepts only exact immutable probe tables')
        # Validation precedes keys, including exact plain indices and counts.
        SuccinctProbeTable.__post_init__(value)
        self._check()
        self._probe_requests += 1
        retained = self._probes.get(value)
        if retained is None:
            self._check(1)
            self._probes[value] = value
            retained = value
        return retained

    def statistics(self):
        return PoolStatistics(self._descriptor_requests, self._probe_requests,
                              len(self._descriptors), len(self._probes))


class PooledGraphBuilder(SuccinctGraphBuilder):
    """Opt-in compile-only facade with per-build descriptor/probe interning.

    All state reservations, fragment embedding, validators and metadata-slot
    accounting are inherited unchanged. Pool entries have a separate mandatory
    cap; equal values save physical objects but never reduce referenced slots.
    """

    def __init__(self, *, max_metadata_records=250_000, max_compile_seconds=10,
                 max_pool_records=100_000):
        _positive_int(max_pool_records, 'max_pool_records')
        super().__init__(max_metadata_records=max_metadata_records,
                         max_compile_seconds=max_compile_seconds)
        self._pool = _CodePool(max_pool_records=max_pool_records, deadline=self._deadline)

    @property
    def pool_statistics(self):
        return self._pool.statistics()

    def match(self, pattern, yes, no):
        self._check()
        return self.embed(compile_pattern(pattern, _factory=self._pool), yes, no)

    def rows(self, rows, yes, no):
        self._check()
        return self.embed(compile_rows(rows, _factory=self._pool), yes, no)

    def inverse_rows(self, rows, yes, no):
        self._check()
        return self.embed(compile_inverse_rows(rows, _factory=self._pool), yes, no)

    def descent(self, rows, done):
        self._check()
        return self.embed(compile_descent(rows, _factory=self._pool), done, done)

    def ascent(self, rows, done):
        self._check()
        return self.embed(compile_ascent(rows, _factory=self._pool), done, done)


def _validate_program(program, max_phases, max_appendant_bits):
    # Deliberately retain the conservative succinct_periodic syntax ceiling.
    if type(program) is not Program:
        raise TypeError('program must be an exact s_only.cts.Program')
    if type(program.appendants) is not tuple or not program.appendants:
        raise ValueError('appendants must be a nonempty plain tuple')
    if type(max_phases) is not int or not 1 <= max_phases <= 5:
        raise ValueError('max_phases must be an integer from 1 through 5')
    if len(program.appendants) > max_phases:
        raise CompilationLimit(f'program exceeds {max_phases} phases')
    if type(max_appendant_bits) is not int or not 0 <= max_appendant_bits <= 8:
        raise ValueError('max_appendant_bits must be an integer from 0 through 8')
    if any(type(word) is not str for word in program.appendants):
        raise ValueError('appendants must be plain binary strings')
    if sum(map(len, program.appendants)) > max_appendant_bits:
        raise CompilationLimit(f'program exceeds {max_appendant_bits} total appendant bits')
    if any(set(word) - {'0', '1'} for word in program.appendants):
        raise ValueError('appendants must be plain binary strings')


def compile_with_statistics(program, *, max_phases=5, max_appendant_bits=8,
                            max_metadata_records=250_000, max_compile_seconds=10,
                            max_pool_records=100_000) -> tuple[SuccinctSelectorTable, PoolStatistics]:
    """Return exact code and a separate immutable compile-time count snapshot.

    Pool dictionaries, source patterns and builders are not returned. Soft
    deadlines and count caps do not bound process bytes or preempt a fragment;
    use external timeout/address-space limits for resource experiments.
    """
    _validate_program(program, max_phases, max_appendant_bits)
    builder = PooledGraphBuilder(max_metadata_records=max_metadata_records,
                                 max_compile_seconds=max_compile_seconds,
                                 max_pool_records=max_pool_records)
    table = _assemble_program(program, max_metadata_records=max_metadata_records,
                              max_compile_seconds=max_compile_seconds, _builder=builder)
    return table, builder.pool_statistics


def compile_table(program, *, max_phases=5, max_appendant_bits=8,
                  max_metadata_records=250_000, max_compile_seconds=10,
                  max_pool_records=100_000) -> SuccinctSelectorTable:
    """Compile the same indexed graph as succinct_periodic with local sharing."""
    table, _ = compile_with_statistics(
        program, max_phases=max_phases, max_appendant_bits=max_appendant_bits,
        max_metadata_records=max_metadata_records, max_compile_seconds=max_compile_seconds,
        max_pool_records=max_pool_records)
    return table
