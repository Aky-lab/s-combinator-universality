"""Input-independent primitive controllers for fixed two-phase binary CTSs.

Compile a program once, then use the shared primitive interpreter on any
current bare S tree. Compilation consumes no initial word or runtime term.
Only the immutable six-observation graph survives into execution.
"""
from __future__ import annotations

from functools import lru_cache

from .cts import Program
from .root_selector import SelectorTable, erase, step
from . import root_selector as runtime
from .program_selector_parts.compiler import CompilationLimit, compile_table


@lru_cache(maxsize=1, typed=True)
def selector_table(program: Program, *, max_states: int | None = None,
                   max_appendant_bits: int | None = 128) -> SelectorTable:
    """Compile exactly two phases, preserving the original program-static API.

    Finite binary appendants, including two empty appendants, determine the
    static row families. The default syntax budget is 128 total appendant
    bits; None disables that budget. Host memory and shared probe-compiler
    recursion remain resource constraints. The typed cache holds one table.
    """
    return compile_table(program, required_period=2, max_states=max_states,
                         max_appendant_bits=max_appendant_bits)


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
