"""Shared, resource-bounded static graph construction; never runtime state."""
from ..cts import Program
from ..root_selector import SelectorTable, _euler
from ..selector_parts.graph import GraphBuilder


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


def compile_table(program, *, required_period, max_states, max_appendant_bits,
                  max_phases=None):
    """Emit the same graph for either a restricted or general-period API."""
    if not isinstance(program, Program):
        raise TypeError('program must be s_only.cts.Program')
    if required_period == 2 and len(program.appendants) != 2:
        raise ValueError('this compiler supports exactly two CTS phases')
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
    from .patterns import PatternFamily
    from .active import compile_active
    from .priority import compile_fresh, compile_marked
    builder = _BoundedBuilder(max_states)
    try:
        normal = builder.uniform('normal')
        contracted = builder.uniform('contracted')
        selected = builder.uniform('Rdx', contracted)
        fallback = builder.root(_euler(builder, selected, normal))
        # Tiny state caps reject before expanding program-dependent patterns.
        p = PatternFamily(program, required_period=required_period)
        active = compile_active(builder, p, selected, fallback)
        marked = compile_marked(builder, p, selected, builder.root(active))
        fresh = compile_fresh(builder, p, selected, builder.root(marked))
    except RecursionError as error:
        raise CompilationLimit('host recursion limit in the shared compile-time probe compiler') from error
    return SelectorTable(builder.finish(), fresh)
