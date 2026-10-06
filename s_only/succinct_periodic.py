"""Exact interval-coded controllers for conservatively bounded CTS periods.

This opt-in compiler extends only the admitted fixed-program syntax: periods
one through five, at most eight total appendant bits. It uses the identical
original-order constructors and immutable runtime representation as the
period-one/two ``succinct_selector`` API, whose contract is unchanged.
"""
from .cts import Program
from .program_selector_parts.compiler import CompilationLimit
from .succinct_selector import SuccinctSelectorTable, _assemble_program


def compile_table(program, *, max_phases=5, max_appendant_bits=8,
                  max_metadata_records=250_000, max_compile_seconds=10) -> SuccinctSelectorTable:
    """Compile one fixed program with mandatory syntax/metadata/time budgets.

    ``max_phases`` may lower, but cannot raise, the five-phase ceiling;
    ``max_appendant_bits`` similarly cannot exceed eight. The returned table
    has exactly the materialized compiler's state indices and six primitive
    entries, with no runtime compiler, input/history state, evaluator or cache.

    The time budget is cooperative. Metadata bounds count retained referenced
    slots, not transient allocation or bytes. Use an external hard process
    timeout and address-space limit for experiments; no such enforcement is
    claimed by this library function. Cross-fragment interning is not provided.
    """
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
    return _assemble_program(program, max_metadata_records=max_metadata_records,
                             max_compile_seconds=max_compile_seconds)
