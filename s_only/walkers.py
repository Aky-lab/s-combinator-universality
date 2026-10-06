"""Finite read-only descent and ancestor-candidate spine walkers.

Compilation closes one acyclic probe fragment's success exit back to its entry.
Only finite control and one occurrence zipper survive at runtime.  See
``docs/spine-walkers.md`` for termination and inverse-admissibility statements.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Literal

from .probes import (
    OBSERVATIONS, Address, Configuration, Cursor, Incoming, Instruction,
    NodeKind, ObservationRow, Pattern, ProbeResult, ProbeTable,
    compile_pattern, compile_rows,
)


@dataclass(frozen=True, slots=True)
class WalkerTable:
    """An immutable finite table with one distinguished feedback state.

    Cutting ``feedback`` leaves a backward-numbered acyclic probe.  Feedback
    performs exactly one stay transition to ``start``.  The structural check
    does not prove cursor progress for hand-written tables: termination is a
    theorem of the two compilers below, from their designated start states.
    """

    states: tuple[ObservationRow, ...]
    start: int
    feedback: int

    def __post_init__(self):
        if type(self.states) is not tuple or not self.states:
            raise ValueError("states must be a nonempty immutable tuple")
        for control in (self.start, self.feedback):
            if type(control) is not int or not 0 <= control < len(self.states):
                raise ValueError("start and feedback must name table states")
        if self.start == self.feedback:
            raise ValueError("entry cannot be an empty feedback loop")
        for state, row in enumerate(self.states):
            if type(row) is not tuple or len(row) != len(OBSERVATIONS):
                raise ValueError("each state needs six immutable observation entries")
            if any(type(entry) is not Instruction for entry in row):
                raise ValueError("table entries must be Instructions")
            if state == self.feedback:
                if any(entry != Instruction("stay", self.start) for entry in row):
                    raise ValueError("feedback must stay and return to start")
                continue
            terminal = row[0].command in ("true", "false")
            for entry in row:
                if terminal:
                    if entry != row[0]:
                        raise ValueError("terminal answers must be observation-independent")
                elif entry.command in ("true", "false"):
                    raise ValueError("a nonterminal state cannot have terminal entries")
                elif entry.next_state >= state:
                    raise ValueError("only the feedback state may have a forward target")

    def transition(self, control: int, kind: NodeKind, incoming: Incoming) -> Instruction:
        """Observe exactly control, local node kind, and incoming side."""
        if type(control) is not int or not 0 <= control < len(self.states):
            raise ValueError("unknown finite control")
        try:
            observation = OBSERVATIONS.index((kind, incoming))
        except ValueError as error:
            raise ValueError("unknown local observation") from error
        return self.states[control][observation]

    def answer(self, control: int) -> bool | None:
        command = self.transition(control, "S", "root").command
        if command == "true":
            return True
        if command == "false":
            return False
        return None

    @property
    def pass_bound(self) -> int:
        """Longest path to feedback or a terminal, computed outside execution."""
        bounds = []
        for state, row in enumerate(self.states):
            if state == self.feedback or row[0].command in ("true", "false"):
                bounds.append(0)
            else:
                bounds.append(1 + max(bounds[entry.next_state] for entry in row))
        return bounds[self.start]

    @property
    def coefficient(self) -> int:
        """Fixed microtick coefficient, including one feedback transition."""
        return self.pass_bound + 1


def step(table: WalkerTable | ProbeTable, configuration: Configuration) -> Configuration:
    """Execute one microtick; terminal states are absorbing."""
    cursor = configuration.cursor
    instruction = table.transition(configuration.control, cursor.kind, cursor.incoming)
    if instruction.command in ("true", "false"):
        return configuration
    if instruction.command == "stay":
        return Configuration(instruction.next_state, cursor)
    return Configuration(instruction.next_state, cursor.move(instruction.command))


def execute(table: WalkerTable | ProbeTable, cursor: Cursor) -> ProbeResult:
    """Run finite control only, with no pattern, address, counter or history."""
    configuration = Configuration(table.start, cursor)
    while table.answer(configuration.control) is None:
        configuration = step(table, configuration)
    return ProbeResult(table.answer(configuration.control), configuration.cursor)


def _prepare(rows: Iterable[tuple[Pattern, Address]]) -> tuple[tuple[tuple[Pattern, Address], ...], ProbeTable]:
    prepared = tuple(rows)
    # Reuse the public forward compiler's pattern/address/scope validation.
    # Requiring scoped addresses for inverse rows is sufficient, though its
    # incoming-side tests would also make unscoped backward paths safe.
    forward = compile_rows(prepared)
    if any(not address for _, address in prepared):
        raise ValueError("spine feedback requires nonempty child addresses")
    return prepared, forward


def _close_feedback(probe: ProbeTable) -> WalkerTable:
    successes = [state for state in range(len(probe.states))
                 if probe.answer(state) is True]
    if len(successes) != 1:
        raise ValueError("a spine fragment needs one success terminal")
    feedback = successes[0]
    states = list(probe.states)
    states[feedback] = (Instruction("stay", probe.start),) * len(OBSERVATIONS)
    return WalkerTable(tuple(states), probe.start, feedback)


def compile_descent(rows: Iterable[tuple[Pattern, Address]]) -> WalkerTable:
    """Repeat first-matching strict-child selection; halt at the first miss.

    At most ``coefficient * nodes(initial_focus)`` microticks are needed.
    The terminal answer is false even when one or more edges were followed.
    """
    _, forward = _prepare(rows)
    return _close_feedback(forward)


class _InverseBuilder:
    """Compile-time graph assembly; nothing here is runtime machine state."""

    def __init__(self):
        self.states = []
        self.false = self.uniform(Instruction("false"))
        self.true = self.uniform(Instruction("true"))

    def uniform(self, instruction: Instruction) -> int:
        self.states.append((instruction,) * len(OBSERVATIONS))
        return len(self.states) - 1

    def move(self, command: Literal["L", "R", "U"], target: int) -> int:
        return self.uniform(Instruction(command, target))

    def incoming_test(self, side: Literal["L", "R"], yes: int, no: int) -> int:
        self.states.append(tuple(Instruction("stay", yes if incoming == side else no)
                                 for _, incoming in OBSERVATIONS))
        return len(self.states) - 1

    def match(self, pattern: Pattern, yes: int, no: int) -> int:
        # Inline the existing restoring matcher, redirecting its Boolean exits.
        # The map is compilation storage, never a runtime call/return stack.
        probe = compile_pattern(pattern)
        mapped = {}
        for state, row in enumerate(probe.states):
            answer = probe.answer(state)
            if answer is not None:
                mapped[state] = yes if answer else no
            else:
                mapped[state] = len(self.states)
                self.states.append(tuple(Instruction(entry.command, mapped[entry.next_state])
                                         for entry in row))
        return mapped[probe.start]

    def inverse(self, pattern: Pattern, address: Address, yes: int, no: int) -> int:
        # For j upward moves, restoration is the j known directions downward.
        # They become finite states, not a dynamically stored return address.
        restore = [no]
        for direction in reversed(address):
            restore.append(self.move("L" if direction == 0 else "R", restore[-1]))
        entry = self.match(pattern, yes, restore[-1])
        # Emit from the outermost candidate back toward the original cursor.
        for index, direction in enumerate(address):
            side = "L" if direction == 0 else "R"
            entry = self.incoming_test(side, self.move("U", entry),
                                       restore[len(address) - index - 1])
        return entry


def compile_inverse_rows(rows: Iterable[tuple[Pattern, Address]]) -> ProbeTable:
    """Try fixed ancestor candidates in row order, restoring every failure.

    A success moves to an ancestor matching the row, with that row's address
    leading back to the invocation occurrence.  It need not be the predecessor
    chosen by prioritized descent: see the admissibility condition in the docs.
    """
    prepared, _ = _prepare(rows)
    builder = _InverseBuilder()
    remaining = builder.false
    for pattern, address in reversed(prepared):
        remaining = builder.inverse(pattern, address, builder.true, remaining)
    return ProbeTable(tuple(builder.states), remaining)


def compile_ascent(rows: Iterable[tuple[Pattern, Address]]) -> WalkerTable:
    """Repeat prioritized ancestor recognition until the first family miss.

    At most ``coefficient * (initial_depth + 1)`` microticks are needed.
    Without an admissibility premise this is not a descent-path reconstruction.
    """
    return _close_feedback(compile_inverse_rows(rows))
