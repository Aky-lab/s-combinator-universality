"""A fixed finite root-reset controller for the two-phase CTS fixture.

All pattern/continuation work is compile time.  Runtime configuration is one
finite control and one occurrence zipper.  No source evaluator, fixture trace,
prior selection, tree serialization, or supplementary stack is consulted.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from .probes import OBSERVATIONS, Configuration, Cursor
from .reduction import root_arguments
from .terms import App, Term
from .selector_parts.graph import Command, GraphBuilder


@dataclass(frozen=True, slots=True)
class SelectorTable:
    states: tuple[tuple[Command, ...], ...]
    start: int

    def __post_init__(self):
        if type(self.states) is not tuple or not self.states:
            raise ValueError('nonempty immutable states required')
        if type(self.start) is not int or not 0 <= self.start < len(self.states):
            raise ValueError('invalid initial control')
        for row in self.states:
            if type(row) is not tuple or len(row) != 6:
                raise ValueError('six immutable observation entries required')
            for entry in row:
                if type(entry) is not Command:
                    raise ValueError('invalid instruction')
                if type(entry.command) is not str:
                    raise ValueError('primitive command must be a plain string')
                if entry.command in ('normal', 'contracted'):
                    if any(other != entry for other in row) or entry.next_state is not None:
                        raise ValueError('terminal must be uniform and absorbing')
                elif entry.command in ('stay', 'L', 'R', 'U', 'Rdx'):
                    if type(entry.next_state) is not int or not 0 <= entry.next_state < len(self.states):
                        raise ValueError('invalid finite target')
                    if entry.command == 'Rdx':
                        if any(other != entry for other in row):
                            raise ValueError('contraction site must be observation-independent')
                        if self.states[entry.next_state][0].command != 'contracted':
                            raise ValueError('a contraction must end the invocation')
                else:
                    raise ValueError('invalid primitive')

    def transition(self, control, kind, incoming):
        """The transition sees exactly finite control, node kind and side."""
        if type(control) is not int or not 0 <= control < len(self.states):
            raise ValueError('unknown finite control')
        try:
            observation = OBSERVATIONS.index((kind, incoming))
        except ValueError as error:
            raise ValueError('unknown local observation') from error
        return self.states[control][observation]

    def status(self, control):
        command = self.states[control][0].command
        return command if command in ('normal', 'contracted', 'Rdx') else None

    @property
    def linear_coefficient(self):
        """Finite-configuration bound for terminating read-only invocations.

        For a fixed N-occurrence tree there are at most N*|Q| distinct
        read-only configurations. A terminating deterministic run cannot
        repeat one. Contraction adds one tick. See the termination argument.
        """
        return len(self.states) + 1


def _euler(builder, selected, normal):
    """Complete preorder scan, using parent-side observations for returns."""
    visit, ascend = builder.reserve(), builder.reserve()
    after_left = builder.move('R', visit)
    builder.states[ascend] = tuple(
        Command('stay', normal) if incoming == 'root' else
        Command('U', after_left if incoming == 'L' else ascend)
        for _, incoming in OBSERVATIONS)
    descend = builder.node_test(ascend, builder.move('L', visit))
    redex = ((('S', '_'), '_'), '_')
    probe = builder.match(redex, selected, descend)
    builder.jump(visit, probe)
    return visit


@lru_cache(maxsize=1)
def selector_table():
    """Compile the same fixed controller independently of every input term."""
    from .selector_parts.active import compile_active
    from .selector_parts.priority import compile_fresh, compile_marked
    builder = GraphBuilder()
    normal = builder.uniform('normal')
    contracted = builder.uniform('contracted')
    selected = builder.uniform('Rdx', contracted)
    fallback = builder.root(_euler(builder, selected, normal))
    active = compile_active(builder, selected, fallback)
    marked = compile_marked(builder, selected, builder.root(active))
    fresh = compile_fresh(builder, selected, builder.root(marked))
    return SelectorTable(builder.finish(), fresh)


def step(table: SelectorTable, configuration: Configuration) -> Configuration:
    """One primitive microtick; only Rdx changes the represented bare term.

    After Rdx the machine is absorbing. Its cursor has the replacement focus
    and the original context; use erase(), not the read-only Cursor.root.
    """
    cursor = configuration.cursor
    instruction = table.transition(configuration.control, cursor.kind, cursor.incoming)
    command = instruction.command
    if command in ('normal', 'contracted'):
        return configuration
    if command == 'stay':
        return Configuration(instruction.next_state, cursor)
    if command == 'Rdx':
        arguments = root_arguments(cursor.focus)
        if arguments is None:
            raise ValueError('unguarded native contraction')
        x, y, z = arguments
        return Configuration(instruction.next_state,
                             Cursor(App(App(x, z), App(y, z)), cursor.parents))
    return Configuration(instruction.next_state, cursor.move(command))


def erase(cursor: Cursor) -> Term:
    """Materialize the represented term, including a terminal replacement.

    This is zipper erasure/result inspection, never a selector observation.
    """
    current = cursor.focus
    for frame in reversed(cursor.parents):
        current = (App(current, frame.parent.right) if frame.side == 'L'
                   else App(frame.parent.left, current))
    return current


def select_cursor(term: Term, table: SelectorTable | None = None) -> Cursor | None:
    """Read-only selection. A fresh root and fixed control are used each time."""
    table = selector_table() if table is None else table
    configuration = Configuration(table.start, Cursor.at(term))
    while table.status(configuration.control) is None:
        configuration = step(table, configuration)
    return configuration.cursor if table.status(configuration.control) == 'Rdx' else None


def select_path(term: Term, table: SelectorTable | None = None):
    """Return an address only as an external observation of the final cursor."""
    cursor = select_cursor(term, table)
    return None if cursor is None else cursor.path


def execute(term: Term, table: SelectorTable | None = None) -> Configuration:
    """Exactly one native contraction, or a normal-form terminal.

    There is no budget or counter in this interpreter; tests bound it from
    outside. Each call discards every prior control/cursor and starts at root.
    """
    table = selector_table() if table is None else table
    configuration = Configuration(table.start, Cursor.at(term))
    while table.status(configuration.control) not in ('normal', 'contracted'):
        configuration = step(table, configuration)
    return configuration


def reduce_once(term: Term, table: SelectorTable | None = None) -> Term | None:
    table = selector_table() if table is None else table
    result = execute(term, table)
    return erase(result.cursor) if table.status(result.control) == 'contracted' else None
