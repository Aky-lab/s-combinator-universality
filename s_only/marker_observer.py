"""Finite, read-only priority-selected fresh halt-field observation.

Static compilation sees the fixed positive-period program, never an input.
Execution uses an explicit immutable graph and one fresh occurrence zipper.
There is deliberately no Euler fallback, contraction, or checkpoint decoder.
See docs/marker-observer.md for the exact event and unmechanized proof scope.
"""
from __future__ import annotations

from dataclasses import dataclass

from .probes import OBSERVATIONS, Configuration, Cursor, ProbeResult
from .selector_parts.graph import Command


@dataclass(frozen=True, slots=True)
class ObserverTable:
    """A finite six-observation graph with uniform Boolean terminal states.

    Cycles are allowed, so validation establishes the finite read-only interface,
    not termination for arbitrary hand-built tables. Termination of compiled
    workers is a separate compositional argument; runtime retains no counter.
    """

    states: tuple[tuple[Command, ...], ...]
    start: int

    def __post_init__(self):
        if type(self.states) is not tuple or not self.states:
            raise ValueError('nonempty immutable states required')
        if type(self.start) is not int or not 0 <= self.start < len(self.states):
            raise ValueError('invalid initial control')
        for row in self.states:
            if type(row) is not tuple or len(row) != len(OBSERVATIONS):
                raise ValueError('six immutable observation entries required')
            for entry in row:
                if type(entry) is not Command:
                    raise ValueError('invalid instruction')
                if type(entry.command) is not str:
                    raise ValueError('read-only command must be a plain string')
                if entry.command in ('true', 'false'):
                    if any(other != entry for other in row) or entry.next_state is not None:
                        raise ValueError('terminal must be uniform and absorbing')
                elif entry.command in ('stay', 'L', 'R', 'U'):
                    if type(entry.next_state) is not int or not 0 <= entry.next_state < len(self.states):
                        raise ValueError('invalid finite target')
                else:
                    raise ValueError('invalid read-only primitive')

    def transition(self, control, kind, incoming):
        if type(control) is not int or not 0 <= control < len(self.states):
            raise ValueError('unknown finite control')
        try:
            observation = OBSERVATIONS.index((kind, incoming))
        except ValueError as error:
            raise ValueError('unknown local observation') from error
        return self.states[control][observation]

    def answer(self, control):
        command = self.transition(control, 'S', 'root').command
        return True if command == 'true' else False if command == 'false' else None

    @property
    def linear_coefficient(self):
        """Finite-configuration bound, conditional on invocation termination.

        On an N-occurrence immutable tree, a terminating deterministic run
        cannot repeat any of its N*|Q| control/cursor configurations.
        """
        return len(self.states)


def observer_table(program, *, max_states=None, max_appendant_bits=128,
                   max_phases=16):
    """Compile priority selection followed by a restoring literal shape test.

    The caller compiles once, before supplying any input tree. Syntax and
    graph caps cover construction only. They do not appear in the runtime
    table. None disables the corresponding cap. Host recursion exhaustion
    is reported as CompilationLimit, rather than yielding a partial table.
    """
    from .cts import Program
    from .program_selector_parts.compiler import CompilationLimit, _BoundedBuilder

    if not isinstance(program, Program):
        raise TypeError('program must be s_only.cts.Program')
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError('max_states must be a positive integer or None')
    if max_appendant_bits is not None and (type(max_appendant_bits) is not int or max_appendant_bits < 0):
        raise ValueError('max_appendant_bits must be a nonnegative integer or None')
    if max_phases is not None and (type(max_phases) is not int or max_phases < 1):
        raise ValueError('max_phases must be a positive integer or None')
    if max_phases is not None and len(program.appendants) > max_phases:
        raise CompilationLimit(f'program exceeds {max_phases} phases')
    if max_appendant_bits is not None and sum(map(len, program.appendants)) > max_appendant_bits:
        raise CompilationLimit(f'program exceeds {max_appendant_bits} total appendant bits')
    from .program_selector_parts.patterns import PatternFamily, HALT, H
    from .program_selector_parts.active import compile_active
    from .program_selector_parts.priority import compile_fresh, compile_marked

    builder = _BoundedBuilder(max_states)
    try:
        no = builder.uniform('false')
        yes = builder.uniform('true')
        # Selected COMMIT is Local.LLL = HALT payload, not the Local root.
        # Successes from *all* priority passes undergo this exact local test.
        selected = builder.match((HALT, H), yes, no)
        p = PatternFamily(program, required_period=None)
        active = compile_active(builder, p, selected, no)
        marked = compile_marked(builder, p, selected, builder.root(active))
        fresh = compile_fresh(builder, p, selected, builder.root(marked))
    except RecursionError as error:
        raise CompilationLimit('host recursion limit in the marker probe compiler') from error
    return ObserverTable(builder.finish(), fresh)


def step(table: ObserverTable, configuration: Configuration) -> Configuration:
    """One read-only primitive tick, observing only node kind and side."""
    cursor = configuration.cursor
    instruction = table.transition(configuration.control, cursor.kind, cursor.incoming)
    if instruction.command in ('true', 'false'):
        return configuration
    if instruction.command == 'stay':
        return Configuration(instruction.next_state, cursor)
    return Configuration(instruction.next_state, cursor.move(instruction.command))


def execute(term, table: ObserverTable) -> ProbeResult:
    """Start at root every time; never compile or retain prior invocation data."""
    if not isinstance(table, ObserverTable):
        raise TypeError('an explicitly precompiled ObserverTable is required')
    configuration = Configuration(table.start, Cursor.at(term))
    while table.answer(configuration.control) is None:
        configuration = step(table, configuration)
    return ProbeResult(table.answer(configuration.control), configuration.cursor)


def accepts(term, table: ObserverTable) -> bool:
    """Whether priority selection chooses a literal fresh halt-field redex."""
    return execute(term, table).answer
