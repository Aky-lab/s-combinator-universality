"""Finite, read-only tables for restoring S-tree pattern tests.

Patterns and continuation recursion exist only while compiling.  Execution
uses one finite control value and one occurrence cursor.  See
``docs/probe-compiler.md`` for the table contract and correctness argument.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Literal, TypeAlias

from .terms import App, S, Term

HOLE = "_"
LITERAL_S = "S"
Pattern: TypeAlias = Literal["_", "S"] | tuple["Pattern", "Pattern"]
NodeKind: TypeAlias = Literal["S", "application"]
Incoming: TypeAlias = Literal["root", "L", "R"]
Command: TypeAlias = Literal["stay", "L", "R", "U", "true", "false"]
Address: TypeAlias = tuple[int, ...]

# A state's six entries use this exact order.  These are the only observations.
OBSERVATIONS = (
    ("S", "root"), ("S", "L"), ("S", "R"),
    ("application", "root"), ("application", "L"), ("application", "R"),
)


@dataclass(frozen=True, slots=True)
class Instruction:
    command: Command
    next_state: int | None = None

    def __post_init__(self):
        if self.command not in ("stay", "L", "R", "U", "true", "false"):
            raise ValueError("unknown read-only command")
        if self.command in ("true", "false"):
            if self.next_state is not None:
                raise ValueError("terminal commands have no next state")
        elif type(self.next_state) is not int or self.next_state < 0:
            raise ValueError("nonterminal commands need a nonnegative state")


ObservationRow: TypeAlias = tuple[Instruction, ...]


@dataclass(frozen=True, slots=True)
class ProbeTable:
    """An immutable acyclic table, with absorbing Boolean terminal states.

    Nonterminal targets must precede their source.  This is the compiler's
    numbering convention and a checkable termination certificate; general
    looping controllers are outside this table type's scope.
    """

    states: tuple[ObservationRow, ...]
    start: int

    def __post_init__(self):
        if type(self.states) is not tuple or not self.states:
            raise ValueError("states must be a nonempty immutable tuple")
        if type(self.start) is not int or not 0 <= self.start < len(self.states):
            raise ValueError("start must name a table state")
        for state, row in enumerate(self.states):
            if type(row) is not tuple or len(row) != len(OBSERVATIONS):
                raise ValueError("each state needs six immutable observation entries")
            if any(type(entry) is not Instruction for entry in row):
                raise ValueError("table entries must be Instructions")
            terminal = row[0].command in ("true", "false")
            for entry in row:
                if terminal:
                    if entry != row[0]:
                        raise ValueError("terminal answers must be observation-independent")
                elif entry.command in ("true", "false"):
                    raise ValueError("a nonterminal state cannot have terminal entries")
                elif entry.next_state >= state:
                    raise ValueError("nonterminal targets must precede their source state")

    def transition(self, control: int, kind: NodeKind, incoming: Incoming) -> Instruction:
        """Look up one instruction using exactly the allowed finite inputs."""
        if type(control) is not int or not 0 <= control < len(self.states):
            raise ValueError("unknown finite control")
        try:
            observation = OBSERVATIONS.index((kind, incoming))
        except ValueError as error:
            raise ValueError("unknown local observation") from error
        return self.states[control][observation]

    def answer(self, control: int) -> bool | None:
        """The fixed answer map: None means the worker is still running."""
        command = self.transition(control, "S", "root").command
        if command == "true":
            return True
        if command == "false":
            return False
        return None

    @property
    def tick_bound(self) -> int:
        """Static longest table path; never a field of runtime control."""
        bounds = []
        for row in self.states:
            if row[0].command in ("true", "false"):
                bounds.append(0)
            else:
                bounds.append(1 + max(bounds[entry.next_state] for entry in row))
        return bounds[self.start]


@dataclass(frozen=True, slots=True)
class _Frame:
    # Keeping an immutable parent avoids rebuilding even a single term node.
    parent: App
    side: Literal["L", "R"]


class InvalidMove(ValueError):
    """A table attempted an absent edge; compiled probes never do this."""


@dataclass(frozen=True, slots=True)
class Cursor:
    """A read-only occurrence zipper; parent frames run root-to-nearest."""

    focus: Term
    parents: tuple[_Frame, ...] = ()

    @classmethod
    def at(cls, term: Term, path: Address = ()) -> Cursor:
        """Prepare an invocation cursor; the path is not retained as a register."""
        if not isinstance(term, (type(S), App)):
            raise TypeError("a cursor needs an S term")
        _validate_address(path)
        cursor = cls(term)
        for direction in path:
            cursor = cursor.move("L" if direction == 0 else "R")
        return cursor

    @property
    def kind(self) -> NodeKind:
        return "application" if isinstance(self.focus, App) else "S"

    @property
    def incoming(self) -> Incoming:
        return self.parents[-1].side if self.parents else "root"

    @property
    def path(self) -> Address:
        """Inspect the output occurrence; the transition function never uses this."""
        return tuple(0 if frame.side == "L" else 1 for frame in self.parents)

    @property
    def root(self) -> Term:
        """Inspect the unchanged ambient term; not a controller observation."""
        return self.parents[0].parent if self.parents else self.focus

    def move(self, command: Literal["L", "R", "U"]) -> Cursor:
        if command == "U":
            if not self.parents:
                raise InvalidMove("cannot move up from the root")
            return Cursor(self.parents[-1].parent, self.parents[:-1])
        if command not in ("L", "R"):
            raise ValueError("cursor movement must be L, R, or U")
        if not isinstance(self.focus, App):
            raise InvalidMove("cannot descend from S")
        child = self.focus.left if command == "L" else self.focus.right
        return Cursor(child, self.parents + (_Frame(self.focus, command),))


@dataclass(frozen=True, slots=True)
class Configuration:
    control: int
    cursor: Cursor


@dataclass(frozen=True, slots=True)
class ProbeResult:
    answer: bool
    cursor: Cursor


def step(table: ProbeTable, configuration: Configuration) -> Configuration:
    """One microtick.  A terminal configuration is absorbing."""
    cursor = configuration.cursor
    instruction = table.transition(configuration.control, cursor.kind, cursor.incoming)
    if instruction.command in ("true", "false"):
        return configuration
    if instruction.command == "stay":
        return Configuration(instruction.next_state, cursor)
    return Configuration(instruction.next_state, cursor.move(instruction.command))


def execute(table: ProbeTable, cursor: Cursor) -> ProbeResult:
    """Run an already compiled probe, without a stack, budget, or pattern data."""
    configuration = Configuration(table.start, cursor)
    while table.answer(configuration.control) is None:
        configuration = step(table, configuration)
    return ProbeResult(table.answer(configuration.control), configuration.cursor)


def _validate_pattern(pattern: Pattern) -> None:
    pending = [pattern]
    while pending:
        node = pending.pop()
        if type(node) is str and node in (HOLE, LITERAL_S):
            continue
        if type(node) is not tuple or len(node) != 2:
            raise ValueError("a pattern is '_', 'S', or a pair of patterns")
        pending.extend(node)


def _validate_address(address: Address) -> None:
    if type(address) is not tuple or any(
        type(direction) is not int or direction not in (0, 1) for direction in address
    ):
        raise ValueError("an address is an immutable tuple of 0/1 directions")


def pattern_budget(pattern: Pattern) -> int:
    """The paper's B: 1 for a hole, 2 for S, and 6 + B(A) + B(B) for AB."""
    _validate_pattern(pattern)
    pending = [pattern]
    bound = 0
    while pending:
        node = pending.pop()
        if node == HOLE:
            bound += 1
        elif node == LITERAL_S:
            bound += 2
        else:
            bound += 6
            pending.extend(node)
    return bound


class _Builder:
    """Compile-time storage only; not retained by the executable table."""

    def __init__(self):
        self.states = []
        self.false = self.uniform(Instruction("false"))
        self.true = self.uniform(Instruction("true"))

    def uniform(self, instruction: Instruction) -> int:
        self.states.append((instruction,) * len(OBSERVATIONS))
        return len(self.states) - 1

    def move(self, command: Literal["L", "R", "U"], target: int) -> int:
        return self.uniform(Instruction(command, target))

    def node_test(self, on_s: int, on_application: int) -> int:
        self.states.append((Instruction("stay", on_s),) * 3
                           + (Instruction("stay", on_application),) * 3)
        return len(self.states) - 1

    def match(self, pattern: Pattern, yes: int, no: int) -> int:
        # Recursion here builds a fixed code graph.  Execution never calls this
        # compiler and has no procedure-return stack.
        if pattern == HOLE:
            return yes
        if pattern == LITERAL_S:
            return self.node_test(yes, no)
        left, right = pattern
        up_yes = self.move("U", yes)
        up_no = self.move("U", no)
        right_test = self.match(right, up_yes, up_no)
        after_left = self.move("U", self.move("R", right_test))
        left_test = self.match(left, after_left, up_no)
        return self.node_test(no, self.move("L", left_test))

    def table(self, start: int) -> ProbeTable:
        return ProbeTable(tuple(self.states), start)


def compile_pattern(pattern: Pattern) -> ProbeTable:
    """Compile a matcher that answers at its exact starting occurrence."""
    _validate_pattern(pattern)
    builder = _Builder()
    return builder.table(builder.match(pattern, builder.true, builder.false))


def compile_rows(rows: Iterable[tuple[Pattern, Address]]) -> ProbeTable:
    """Try finite rows in order and follow the first matching row's address.

    Every proper address prefix must be an application in the pattern.  This
    compile-time scope check guarantees that the selected address exists for
    every matching tree, including malformed carrier trees.  An empty list or
    an all-mismatch run answers false at the exact invocation cursor.
    """
    prepared = tuple(rows)
    for row in prepared:
        if type(row) is not tuple or len(row) != 2:
            raise ValueError("each row must be a (pattern, address) pair")
        pattern, address = row
        _validate_pattern(pattern)
        _validate_address(address)
        node = pattern
        for direction in address:
            if type(node) is not tuple:
                raise ValueError("row address must be guaranteed by its pattern")
            node = node[direction]
    builder = _Builder()
    remaining = builder.false
    for pattern, address in reversed(prepared):
        selected = builder.true
        for direction in reversed(address):
            selected = builder.move("L" if direction == 0 else "R", selected)
        remaining = builder.match(pattern, selected, remaining)
    return builder.table(remaining)
