"""Compile-time composition of finite six-observation controller tables.

This module runs before any source tree is supplied.  The emitted graph holds
only finite state indices and primitive commands; no pattern survives in it.
"""
from dataclasses import dataclass

from ..probes import OBSERVATIONS, compile_pattern, compile_rows
from ..walkers import compile_descent, compile_ascent, compile_inverse_rows


@dataclass(frozen=True, slots=True)
class Command:
    command: str
    next_state: int | None = None


class GraphBuilder:
    def __init__(self):
        self.states = []

    def reserve(self):
        self.states.append(None)
        return len(self.states) - 1

    def emit(self, row):
        state = self.reserve()
        self.states[state] = tuple(row)
        return state

    def uniform(self, command, target=None):
        return self.emit((Command(command, target),) * 6)

    def move(self, command, target):
        if command not in ('stay', 'L', 'R', 'U'):
            raise ValueError('not a movement command')
        return self.uniform(command, target)

    def jump(self, state, target):
        if self.states[state] is not None:
            raise ValueError('reserved control already filled')
        self.states[state] = (Command('stay', target),) * 6

    def node_test(self, on_s, on_app):
        return self.emit(tuple(Command('stay', on_s if kind == 'S' else on_app)
                               for kind, _ in OBSERVATIONS))

    def incoming_test(self, side, yes, no):
        if side not in ('root', 'L', 'R'):
            raise ValueError('unknown incoming side')
        return self.emit(tuple(Command('stay', yes if incoming == side else no)
                               for _, incoming in OBSERVATIONS))

    def path(self, address, target):
        for direction in reversed(address):
            if type(direction) is not int or direction not in (0, 1):
                raise ValueError('invalid fixed address')
            target = self.move('L' if direction == 0 else 'R', target)
        return target

    def embed(self, table, yes, no):
        """Inline table controls and redirect both absorbing answers."""
        mapping = {}
        for old in range(len(table.states)):
            answer = table.answer(old)
            mapping[old] = (yes if answer else no) if answer is not None else self.reserve()
        for old, row in enumerate(table.states):
            if table.answer(old) is None:
                self.states[mapping[old]] = tuple(
                    Command(entry.command, mapping[entry.next_state]) for entry in row)
        return mapping[table.start]

    def match(self, pattern, yes, no):
        return self.embed(compile_pattern(pattern), yes, no)

    def rows(self, rows, yes, no):
        return self.embed(compile_rows(rows), yes, no)

    def inverse_rows(self, rows, yes, no):
        return self.embed(compile_inverse_rows(rows), yes, no)

    def descent(self, rows, done):
        return self.embed(compile_descent(rows), done, done)

    def ascent(self, rows, done):
        return self.embed(compile_ascent(rows), done, done)

    def root(self, done):
        loop = self.reserve()
        self.states[loop] = tuple(Command('stay', done) if side == 'root'
                                 else Command('U', loop) for _, side in OBSERVATIONS)
        return loop

    def finish(self):
        if any(row is None for row in self.states):
            raise ValueError('unresolved finite control')
        return tuple(self.states)
