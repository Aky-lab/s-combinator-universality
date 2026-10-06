"""Ordinary binary cyclic-tag-system semantics, with explicit resource bounds.

One bit is deleted per step. Its value controls whether the current appendant
is appended; the program phase advances in either case. There is no special
halt token in this interpreter. An empty queue and a repeated configuration
are distinct observations, and neither establishes a simulated machine halt.
"""
from collections import deque
from dataclasses import dataclass


def _bits(word: str) -> None:
    if not isinstance(word, str) or set(word) - {"0", "1"}:
        raise ValueError("a binary word must be a string containing only 0 and 1")


@dataclass(frozen=True)
class Program:
    appendants: tuple[str, ...]

    def __post_init__(self):
        if not isinstance(self.appendants, tuple) or not self.appendants:
            raise ValueError("appendants must be a nonempty tuple")
        for word in self.appendants:
            _bits(word)


@dataclass(frozen=True)
class Configuration:
    word: str
    phase: int = 0

    def __post_init__(self):
        _bits(self.word)
        if type(self.phase) is not int or self.phase < 0:
            raise ValueError("phase must be a nonnegative integer")


@dataclass(frozen=True)
class Event:
    step: int
    phase: int
    deleted: str
    appended: str
    word_bits: int


class ResourceLimit(RuntimeError):
    """A requested next step exceeds a bound; that step is not executed."""


def step(program: Program, state: Configuration) -> Configuration:
    """Pure, single-step reference interface (raises StopIteration on empty)."""
    if state.phase >= len(program.appendants):
        raise ValueError("phase is outside the program")
    if not state.word:
        raise StopIteration("empty dataword")
    suffix = program.appendants[state.phase] if state.word[0] == "1" else ""
    return Configuration(state.word[1:] + suffix,
                         (state.phase + 1) % len(program.appendants))


class Machine:
    """Deque-backed interpreter. Limits apply over this instance's lifetime."""

    def __init__(self, program: Program, initial: Configuration, *,
                 max_steps: int, max_word_bits: int):
        if type(max_steps) is not int or max_steps < 0:
            raise ValueError("max_steps must be a nonnegative integer")
        if type(max_word_bits) is not int or max_word_bits < 0:
            raise ValueError("max_word_bits must be a nonnegative integer")
        if initial.phase >= len(program.appendants):
            raise ValueError("phase is outside the program")
        if len(initial.word) > max_word_bits:
            raise ResourceLimit("initial word exceeds max_word_bits")
        self.program = program
        self._queue = deque(initial.word)
        self.phase = initial.phase
        self.steps = 0
        self.peak_word_bits = len(initial.word)
        self.max_steps = max_steps
        self.max_word_bits = max_word_bits

    @property
    def word_bits(self) -> int:
        return len(self._queue)

    def snapshot(self) -> Configuration:
        return Configuration("".join(self._queue), self.phase)

    def tick(self) -> Event:
        if not self._queue:
            raise StopIteration("empty dataword")
        if self.steps >= self.max_steps:
            raise ResourceLimit("max_steps reached")
        bit = self._queue[0]
        appended = self.program.appendants[self.phase] if bit == "1" else ""
        size = len(self._queue) - 1 + len(appended)
        if size > self.max_word_bits:
            raise ResourceLimit("next step exceeds max_word_bits")
        phase = self.phase
        self._queue.popleft()
        self._queue.extend(appended)
        self.phase = (phase + 1) % len(self.program.appendants)
        self.steps += 1
        self.peak_word_bits = max(self.peak_word_bits, size)
        return Event(self.steps, phase, bit, appended, size)
