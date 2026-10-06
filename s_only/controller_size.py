"""Exact allocation/start preflight, with no probe or controller tables.

This is a count-only compiler facade for fixed valid programs, not an executable
controller or a transition-semantics proof. Existing shape factories still
construct finite patterns. Unlike compilation_cost, this is not a source-only
arithmetic formula. Run large cases inside a hard process/memory envelope.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
import math
import time

from .cts import Program
from .program_selector_parts.compiler import CompilationLimit
from .selector_parts.graph import GraphBuilder


@dataclass(frozen=True, slots=True)
class StageSize:
    name: str
    first_state: int
    state_count: int
    start: int


@dataclass(frozen=True, slots=True)
class FragmentSize:
    kind: str
    calls: int
    state_count: int


@dataclass(frozen=True, slots=True)
class ControllerSize:
    state_count: int
    start: int
    direct_states: int
    fragments: tuple[FragmentSize, ...]
    stages: tuple[StageSize, ...]
    pattern_work: int
    pattern_nodes: int


class _Reservations:
    """Sparse fill flags only; assigned transition rows are immediately dropped."""
    def __init__(self, builder):
        self.builder = builder

    def __getitem__(self, state):
        if type(state) is not int or state not in self.builder._direct:
            raise ValueError('not a directly reserved control')
        return True if self.builder._direct[state] else None

    def __setitem__(self, state, row):
        if self[state] is not None:
            raise ValueError('reserved control already filled')
        if type(row) is not tuple or len(row) != 6:
            raise ValueError('six observation entries required')
        self.builder._direct[state] = True

    def __iter__(self):
        raise TypeError('reservations are not a virtual collection')


def _positive(value, name):
    if type(value) is not int or value < 1:
        raise ValueError(f'{name} must be a positive integer')


class CountingGraphBuilder(GraphBuilder):
    """Count GraphBuilder operations, preserving their exact emission indices.

    The facade retains sparse direct-control fill flags, integer totals and
    optional stage summaries, never transition rows or virtual-state arrays.
    ``embed`` is deliberately unsupported: call the five shape-based methods.
    Work/time budgets are cooperative; external hard bounds are still needed
    for factory construction before a method receives a pattern family.
    """
    def __init__(self, *, max_pattern_work=100_000_000, max_compile_seconds=120):
        _positive(max_pattern_work, 'max_pattern_work')
        if type(max_compile_seconds) is not int and type(max_compile_seconds) is not float:
            raise ValueError('max_compile_seconds must be finite and positive')
        try:
            seconds = float(max_compile_seconds)
        except OverflowError as exc:
            raise ValueError('max_compile_seconds must fit a finite clock value') from exc
        if not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('max_compile_seconds must be finite and positive')
        self._deadline = time.monotonic() + seconds
        if not math.isfinite(self._deadline):
            raise ValueError('max_compile_seconds must produce a finite deadline')
        self._limit = max_pattern_work
        self._count = self.pattern_work = self.pattern_nodes = 0
        self._direct = {}
        self._fragments = {name: [0, 0] for name in
                           ('match', 'rows', 'inverse_rows', 'descent', 'ascent')}
        self._stages = []
        self.states = _Reservations(self)

    @property
    def state_count(self):
        return self._count

    def _check(self):
        if time.monotonic() >= self._deadline:
            raise CompilationLimit('count preflight exceeds its soft time budget')

    def _work(self):
        # One unit per traversal-stack pop, row, or checked address direction.
        self.pattern_work += 1
        if self.pattern_work > self._limit:
            raise CompilationLimit(f'count preflight exceeds {self._limit} pattern-work units')
        if self.pattern_work % 1024 == 0:
            self._check()

    def reserve(self):
        self._check()
        state = self._count
        self._count += 1
        self._direct[state] = False
        return state

    def embed(self, table, yes, no):
        raise TypeError('count preflight consumes patterns, not compiled tables')

    def _width(self, pattern, widths):
        """Iterative DAG DP; caller keeps every keyed pattern root alive.

        Widths use identity integer keys, never tuple hashes/equality. A cache
        is local to one match or one prepared row family, so id reuse cannot
        confuse distinct patterns. The occurrence width still adds both child
        widths, even when the two child objects are identical.
        """
        pending = [(pattern, False)]
        while pending:
            self._work()
            node, visited = pending.pop()
            identity = id(node)
            if identity in widths:
                continue
            if type(node) is str:
                if node not in ('_', 'S'):
                    raise ValueError("a pattern is '_', 'S', or a pair of patterns")
                widths[identity] = int(node == 'S')
            elif type(node) is not tuple or len(node) != 2:
                raise ValueError("a pattern is '_', 'S', or a pair of patterns")
            elif visited:
                widths[identity] = 6 + widths[id(node[0])] + widths[id(node[1])]
            else:
                pending.extend(((node, True), (node[1], False), (node[0], False)))
                continue
            self.pattern_nodes += 1
        return widths[id(pattern)]

    def _allocate(self, kind, width):
        origin = self._count
        self._count += width
        self._fragments[kind][0] += 1
        self._fragments[kind][1] += width
        self._check()
        return origin

    def match(self, pattern, yes, no):
        self._check()
        width = self._width(pattern, {})
        origin = self._allocate('match', width)
        return origin + width - 1 if width else yes

    def _rows(self, rows, yes, no, *, inverse, closed):
        self._check()
        prepared = tuple(rows)
        widths = {}
        width, start = 0, 0  # Standalone terminals are false=0, true=1.
        for row in reversed(prepared):
            self._work()
            if type(row) is not tuple or len(row) != 2:
                raise ValueError('each row must be a (pattern, address) pair')
            pattern, address = row
            matcher = self._width(pattern, widths)
            if type(address) is not tuple:
                raise ValueError('an address is an immutable tuple of 0/1 directions')
            node = pattern
            for direction in address:
                self._work()
                if type(direction) is not int or direction not in (0, 1):
                    raise ValueError('an address is an immutable tuple of 0/1 directions')
                if type(node) is not tuple:
                    raise ValueError('row address must be guaranteed by its pattern')
                node = node[direction]
            if (closed or inverse) and not address:
                raise ValueError('spine feedback requires nonempty child addresses')
            row_width = matcher + (3 if inverse else 1) * len(address)
            width += row_width
            # Even after earlier controls were emitted, a zero-width wildcard
            # resets the entry to true. Unreachable controls remain counted.
            start = width + 1 if row_width else 1
        kind = ('ascent' if inverse else 'descent') if closed else (
            'inverse_rows' if inverse else 'rows')
        dropped = 1 if closed else 2
        origin = self._allocate(kind, width + 2 - dropped)
        if start == 0:
            return no
        if start == 1 and not closed:
            return yes
        return origin + start - dropped

    def rows(self, rows, yes, no):
        return self._rows(rows, yes, no, inverse=False, closed=False)

    def inverse_rows(self, rows, yes, no):
        return self._rows(rows, yes, no, inverse=True, closed=False)

    def descent(self, rows, done):
        return self._rows(rows, done, done, inverse=False, closed=True)

    def ascent(self, rows, done):
        return self._rows(rows, done, done, inverse=True, closed=True)

    def stage(self, name, function):
        origin = self._count
        start = function()
        self._stages.append(StageSize(name, origin, self._count - origin, start))
        self._check()
        return start

    def finish(self, start):
        self._check()
        if not all(self._direct.values()):
            raise ValueError('unresolved finite control')
        if type(start) is not int or not 0 <= start < self._count:
            raise ValueError('invalid initial control')
        return ControllerSize(self._count, start, len(self._direct), tuple(
            FragmentSize(kind, *stats) for kind, stats in self._fragments.items()),
            tuple(self._stages), self.pattern_work, self.pattern_nodes)


def controller_size(program, *, max_phases=64, max_appendant_bits=1024,
                    max_pattern_work=100_000_000, max_compile_seconds=120):
    """Count the original complete, unquotiented graph for one fixed program.

    Uses the current shape factories, but independently derives all fragment
    widths and starts. Assembly order matches succinct_selector._assemble_program.
    No input term, source execution, probe compiler or controller table is used.
    Syntax/work/time caps are mandatory. A raised limit is not an exact result.
    """
    if type(program) is not Program:
        raise TypeError('program must be an exact s_only.cts.Program')
    _positive(max_phases, 'max_phases')
    if type(max_appendant_bits) is not int or max_appendant_bits < 0:
        raise ValueError('max_appendant_bits must be a nonnegative integer')
    if type(program.appendants) is not tuple or not program.appendants:
        raise ValueError('appendants must be a nonempty plain tuple')
    if len(program.appendants) > max_phases:
        raise CompilationLimit(f'program exceeds {max_phases} phases')
    if any(type(word) is not str or set(word) - {'0', '1'} for word in program.appendants):
        raise ValueError('appendants must be plain binary strings')
    if sum(map(len, program.appendants)) > max_appendant_bits:
        raise CompilationLimit(f'program exceeds {max_appendant_bits} total appendant bits')
    from .root_selector import _euler
    from .program_selector_parts.patterns import PatternFamily
    from .program_selector_parts.active import compile_active
    from .program_selector_parts.priority import compile_fresh, compile_marked
    builder = CountingGraphBuilder(max_pattern_work=max_pattern_work,
                                   max_compile_seconds=max_compile_seconds)
    normal = builder.stage('normal', lambda: builder.uniform('normal'))
    contracted = builder.stage('contracted', lambda: builder.uniform('contracted'))
    selected = builder.stage('selected', lambda: builder.uniform('Rdx', contracted))
    fallback = builder.stage('fallback', lambda: builder.root(_euler(builder, selected, normal)))
    p = PatternFamily(program, required_period=None)
    builder._check()
    active = builder.stage('active', lambda: compile_active(builder, p, selected, fallback))
    root_active = builder.stage('root_active', lambda: builder.root(active))
    marked = builder.stage('marked', lambda: compile_marked(builder, p, selected, root_active))
    root_marked = builder.stage('root_marked', lambda: builder.root(marked))
    fresh = builder.stage('fresh', lambda: compile_fresh(builder, p, selected, root_marked))
    return builder.finish(fresh)


def main(argv=None):
    """Print a reproducible UT19 preflight; use an external hard resource cap."""
    import argparse
    import json
    from .ut19 import compile_cts
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ut19', action='store_true', required=True)
    parser.add_argument('--max-pattern-work', type=int, default=100_000_000)
    parser.add_argument('--max-compile-seconds', type=float, default=120)
    arguments = parser.parse_args(argv)
    program = compile_cts()
    try:
        result = controller_size(program, max_pattern_work=arguments.max_pattern_work,
                                 max_compile_seconds=arguments.max_compile_seconds)
    except (CompilationLimit, MemoryError, RecursionError) as error:
        print(json.dumps({'complete': False, 'reason': type(error).__name__ + ': ' + str(error)},
                         indent=2, sort_keys=True))
        return 1
    print(json.dumps({'schema': 's-only-controller-size-v1', 'complete': True,
                      'phase_count': len(program.appendants),
                      'total_appendant_bits': sum(map(len, program.appendants)),
                      **asdict(result)}, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
