"""Input-independent primitive controllers for fixed two-phase binary CTSs.

Compile a program once, then use the shared primitive interpreter on any
current bare S tree. Compilation consumes no initial word or runtime term.
Only the immutable six-observation graph survives into execution.
"""
from __future__ import annotations

from functools import lru_cache

from .cts import Program
from .root_selector import SelectorTable, _euler, erase, step
from . import root_selector as runtime
from .selector_parts.graph import GraphBuilder


class CompilationLimit(ValueError):
    """An explicit construction budget or host compiler resource was exhausted."""


class _BoundedBuilder(GraphBuilder):
    def __init__(self, max_states):
        super().__init__()
        self.max_states = max_states

    def reserve(self):
        if self.max_states is not None and len(self.states) >= self.max_states:
            raise CompilationLimit(f'controller exceeds {self.max_states} states')
        return super().reserve()


@lru_cache(maxsize=1, typed=True)
def selector_table(program: Program, *, max_states: int | None = None,
                   max_appendant_bits: int | None = 128) -> SelectorTable:
    """Compile a fixed program; an optional construction bound is not runtime state.

    Exactly two phases are supported. Finite binary appendants, including two
    empty appendants, determine the static row families. The default syntax
    budget is 128 total appendant bits; None disables that budget. Host memory
    and shared probe-compiler recursion remain resource constraints.
    The cache is bounded and keyed only by compile-time program and budgets.
    """
    if not isinstance(program, Program):
        raise TypeError('program must be s_only.cts.Program')
    if len(program.appendants) != 2:
        raise ValueError('this compiler supports exactly two CTS phases')
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError('max_states must be a positive integer or None')
    if max_appendant_bits is not None and (type(max_appendant_bits) is not int or max_appendant_bits < 0):
        raise ValueError('max_appendant_bits must be a nonnegative integer or None')
    if max_appendant_bits is not None and sum(map(len, program.appendants)) > max_appendant_bits:
        raise CompilationLimit(f'program exceeds {max_appendant_bits} total appendant bits')
    from .program_selector_parts.patterns import PatternFamily
    from .program_selector_parts.active import compile_active
    from .program_selector_parts.priority import compile_fresh, compile_marked
    builder = _BoundedBuilder(max_states)
    normal = builder.uniform('normal')
    contracted = builder.uniform('contracted')
    selected = builder.uniform('Rdx', contracted)
    fallback = builder.root(_euler(builder, selected, normal))
    # A tiny state cap can reject before expanding any program patterns.
    p = PatternFamily(program)
    try:
        active = compile_active(builder, p, selected, fallback)
        marked = compile_marked(builder, p, selected, builder.root(active))
        fresh = compile_fresh(builder, p, selected, builder.root(marked))
    except RecursionError as error:
        raise CompilationLimit('host recursion limit in the shared compile-time probe compiler') from error
    return SelectorTable(builder.finish(), fresh)


def _require_table(table):
    if not isinstance(table, SelectorTable):
        raise TypeError('an explicitly compiled SelectorTable is required')
    return table


def select_cursor(term, table: SelectorTable):
    """Start at root and select read-only, using only an already compiled table."""
    return runtime.select_cursor(term, _require_table(table))


def select_path(term, table: SelectorTable):
    """Externally inspect the selected occurrence address."""
    return runtime.select_path(term, _require_table(table))


def execute(term, table: SelectorTable):
    """Reset at root and execute one native contraction or certify normality."""
    return runtime.execute(term, _require_table(table))


def reduce_once(term, table: SelectorTable):
    return runtime.reduce_once(term, _require_table(table))
