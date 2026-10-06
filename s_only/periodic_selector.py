"""Program-static root-reset S controllers for positive-period binary CTSs.

Compilation sees only the fixed program and budgets. Execution requires an
explicit immutable six-observation SelectorTable and resets at the root for
each single native S contraction. No program object survives in that table.
"""
from functools import lru_cache

from .cts import Program
from .program_selector import (execute, reduce_once, select_cursor, select_path)
from .program_selector_parts.compiler import CompilationLimit, compile_table
from .root_selector import SelectorTable, erase, step


@lru_cache(maxsize=1, typed=True)
def selector_table(program: Program, *, max_states: int | None = None,
                   max_appendant_bits: int | None = 128,
                   max_phases: int | None = 16) -> SelectorTable:
    """Compile arbitrary positive periods within explicit construction limits.

    max_appendant_bits counts all emitted bits; max_phases additionally caps
    dispatch syntax even when every appendant is empty. None disables either
    syntax cap. A state cap limits the emitted graph, not temporary compiler
    memory. Host recursion exhaustion raises CompilationLimit. The typed
    cache holds at most one immutable graph, never a runtime source state.
    """
    return compile_table(program, required_period=None, max_states=max_states,
                         max_appendant_bits=max_appendant_bits, max_phases=max_phases)
