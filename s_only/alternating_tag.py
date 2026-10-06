"""Bounded finite-alphabet alternating tag semantics and one-hot CTS compiler.

A microstep deletes one symbol, appends its production only in TAKE phase,
then toggles phase. Only the empty queue stops. In particular this is NOT
conventional deletion-two tag semantics with a length-less-than-two stop.
See docs/alternating-tag.md for the exact simulation and event offsets.
"""
from collections import deque
from dataclasses import dataclass

from . import cts

TAKE = "take"
SKIP = "skip"
ResourceLimit = cts.ResourceLimit


def _natural(value: int, name: str) -> None:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def _word(word: tuple[int, ...], alphabet_size: int | None = None) -> None:
    if type(word) is not tuple:
        raise ValueError("a source word must be a tuple")
    for symbol in word:
        _natural(symbol, "symbol")
        if alphabet_size is not None and symbol >= alphabet_size:
            raise ValueError("symbol is outside the alphabet")


@dataclass(frozen=True, slots=True)
class Program:
    """An immutable table; its length defines the alphabet 0, ..., m-1."""

    productions: tuple[tuple[int, ...], ...]

    def __post_init__(self):
        if type(self.productions) is not tuple or not self.productions:
            raise ValueError("productions must be a nonempty tuple")
        for word in self.productions:
            _word(word, len(self.productions))

    @property
    def alphabet_size(self) -> int:
        return len(self.productions)


@dataclass(frozen=True, slots=True)
class Configuration:
    queue: tuple[int, ...]
    phase: str = TAKE

    def __post_init__(self):
        _word(self.queue)
        if type(self.phase) is not str or self.phase not in (TAKE, SKIP):
            raise ValueError("phase must be 'take' or 'skip'")


def _program(program: Program) -> None:
    if type(program) is not Program:
        raise ValueError("program must be an alternating-tag Program")


def _state(program: Program, state: Configuration) -> None:
    _program(program)
    if type(state) is not Configuration:
        raise ValueError("state must be an alternating-tag Configuration")
    _word(state.queue, program.alphabet_size)
    if type(state.phase) is not str or state.phase not in (TAKE, SKIP):
        raise ValueError("phase must be 'take' or 'skip'")


def _cts_state(state: cts.Configuration) -> None:
    # CTS Configuration itself permits str subclasses; this boundary does not.
    # Binary content is established by its constructor, without an O(n) scan
    # inside the fixed-program selected-event predicate.
    if type(state) is not cts.Configuration or type(state.word) is not str:
        raise ValueError("state must be an exact CTS Configuration with a plain string word")
    _natural(state.phase, "CTS phase")


def _symbol(program: Program, symbol: int) -> None:
    _program(program)
    _natural(symbol, "selected symbol")
    if symbol >= program.alphabet_size:
        raise ValueError("selected symbol is outside the alphabet")


def step(program: Program, state: Configuration, *,
         max_queue_symbols: int) -> Configuration:
    """Pure bounded reference step; raises StopIteration only on empty input."""
    _natural(max_queue_symbols, "max_queue_symbols")
    _state(program, state)
    if len(state.queue) > max_queue_symbols:
        raise ResourceLimit("initial queue exceeds max_queue_symbols")
    if not state.queue:
        raise StopIteration("empty source queue")
    appended = program.productions[state.queue[0]] if state.phase == TAKE else ()
    if len(state.queue) - 1 + len(appended) > max_queue_symbols:
        raise ResourceLimit("next step exceeds max_queue_symbols")
    return Configuration(state.queue[1:] + appended,
                         SKIP if state.phase == TAKE else TAKE)


@dataclass(frozen=True, slots=True)
class Event:
    """A completed source microstep; step is one-based, phase is the PREphase."""

    step: int
    phase: str
    deleted: int
    appended: tuple[int, ...]
    queue_symbols: int

    def __post_init__(self):
        _natural(self.step, "step")
        if self.step == 0:
            raise ValueError("an event step must be positive")
        if type(self.phase) is not str or self.phase not in (TAKE, SKIP):
            raise ValueError("event phase must be 'take' or 'skip'")
        _natural(self.deleted, "deleted symbol")
        _word(self.appended)
        _natural(self.queue_symbols, "queue_symbols")


class Machine:
    """Deque evaluator; step and queue limits apply over this instance's life.

    Every requested size/step bound is checked before queue or counter mutation.
    Events refer to the table's existing immutable production tuples.
    """

    def __init__(self, program: Program, initial: Configuration, *,
                 max_steps: int, max_queue_symbols: int):
        _natural(max_steps, "max_steps")
        _natural(max_queue_symbols, "max_queue_symbols")
        _state(program, initial)
        if len(initial.queue) > max_queue_symbols:
            raise ResourceLimit("initial queue exceeds max_queue_symbols")
        self.program = program
        self._queue = deque(initial.queue)
        self.phase = initial.phase
        self.steps = 0
        self.peak_queue_symbols = len(initial.queue)
        self.max_steps = max_steps
        self.max_queue_symbols = max_queue_symbols

    @property
    def queue_symbols(self) -> int:
        return len(self._queue)

    def snapshot(self) -> Configuration:
        return Configuration(tuple(self._queue), self.phase)

    def tick(self) -> Event:
        if not self._queue:
            raise StopIteration("empty source queue")
        if self.steps >= self.max_steps:
            raise ResourceLimit("max_steps reached")
        head = self._queue[0]
        appended = self.program.productions[head] if self.phase == TAKE else ()
        size = len(self._queue) - 1 + len(appended)
        if size > self.max_queue_symbols:
            raise ResourceLimit("next step exceeds max_queue_symbols")
        phase = self.phase
        self._queue.popleft()
        self._queue.extend(appended)
        self.phase = SKIP if phase == TAKE else TAKE
        self.steps += 1
        self.peak_queue_symbols = max(self.peak_queue_symbols, size)
        return Event(self.steps, phase, head, appended, size)


def _encode_unchecked(alphabet_size: int, word: tuple[int, ...]) -> str:
    # No m-by-m code table: only requested output blocks are constructed.
    return "".join("0" * symbol + "1" + "0" * (alphabet_size - symbol - 1)
                   for symbol in word)


def encode_word(program: Program, word: tuple[int, ...], *,
                max_word_bits: int) -> str:
    _program(program)
    _natural(max_word_bits, "max_word_bits")
    _word(word, program.alphabet_size)
    if program.alphabet_size * len(word) > max_word_bits:
        raise ResourceLimit("encoded word exceeds max_word_bits")
    return _encode_unchecked(program.alphabet_size, word)


def compile_program(program: Program, *, max_phases: int,
                    max_program_bits: int) -> cts.Program:
    """Produce exactly 2m appendants: encoded productions, then m empty words.

    Both output limits are preflighted before encoding any production.
    max_program_bits counts all appendant bits, not their tuple overhead;
    max_phases independently bounds the latter.
    """
    _program(program)
    _natural(max_phases, "max_phases")
    _natural(max_program_bits, "max_program_bits")
    m = program.alphabet_size
    if 2 * m > max_phases:
        raise ResourceLimit("compiled program exceeds max_phases")
    bits = 0
    for word in program.productions:
        bits += m * len(word)
        if bits > max_program_bits:
            raise ResourceLimit("compiled program exceeds max_program_bits")
    return cts.Program(tuple(_encode_unchecked(m, word) for word in program.productions)
                       + ("",) * m)


def encode_configuration(program: Program, state: Configuration, *,
                         max_word_bits: int) -> cts.Configuration:
    _state(program, state)
    return cts.Configuration(encode_word(program, state.queue,
                                         max_word_bits=max_word_bits),
                             0 if state.phase == TAKE else program.alphabet_size)


def decode_boundary(program: Program, state: cts.Configuration, *,
                    max_word_bits: int, max_queue_symbols: int) -> Configuration:
    """Structural boundary parser; no trace lookup or source evaluation.

    This recognizes the boundary language, not reachability from a given seed.
    """
    _program(program)
    _natural(max_word_bits, "max_word_bits")
    _natural(max_queue_symbols, "max_queue_symbols")
    _cts_state(state)
    m = program.alphabet_size
    if state.phase not in (0, m):
        raise ValueError("not a take/skip boundary phase")
    size = len(state.word)
    if size > max_word_bits or size // m > max_queue_symbols:
        raise ResourceLimit("boundary exceeds parser size bounds")
    if size % m:
        raise ValueError("boundary word is not a whole number of code blocks")
    queue = []
    for start in range(0, size, m):
        if state.word.count("1", start, start + m) != 1:
            raise ValueError("boundary code block is not one-hot")
        queue.append(state.word.index("1", start, start + m) - start)
    return Configuration(tuple(queue), TAKE if state.phase == 0 else SKIP)


def selected_cts_event(program: Program, state: cts.Configuration,
                       selected_symbol: int) -> bool:
    """Fixed-program O(1) predicate of a CTS PREstate: phase h and head 1.

    It is equivalent to source selection on correctly encoded trajectories;
    it does not itself certify that an arbitrary configuration is reachable.
    """
    _symbol(program, selected_symbol)
    _cts_state(state)
    if state.phase >= 2 * program.alphabet_size:
        raise ValueError("phase is outside the compiled program")
    return state.phase == selected_symbol and state.word.startswith("1")


@dataclass(frozen=True, slots=True)
class SelectionPosition:
    source_prestate_step: int
    cts_prestate_step: int
    cts_logged_step: int


def selection_position(program: Program, event: Event,
                       selected_symbol: int) -> SelectionPosition | None:
    """Map a selected source event to its zero-based CTS prestate offset.

    Event numbering must begin at the encoded initial boundary. A skipped
    selected symbol maps to None. The CTS logger labels the deletion k+1.
    """
    _symbol(program, selected_symbol)
    if type(event) is not Event:
        raise ValueError("event must be an alternating-tag Event")
    _symbol(program, event.deleted)
    expected = program.productions[event.deleted] if event.phase == TAKE else ()
    if event.appended != expected:
        raise ValueError("event appendant does not match the program and phase")
    if event.phase != TAKE or event.deleted != selected_symbol:
        return None
    source_prestate = event.step - 1
    prestate = program.alphabet_size * source_prestate + selected_symbol
    return SelectionPosition(source_prestate, prestate, prestate + 1)


@dataclass(frozen=True, slots=True)
class Evaluation:
    final: Configuration
    steps: int
    peak_queue_symbols: int
    stop_reason: str
    selected_count: int
    first_selection: SelectionPosition | None


def evaluate(program: Program, initial: Configuration, *, max_steps: int,
             max_queue_symbols: int, selected_symbol: int | None = None) -> Evaluation:
    """Bounded source execution with O(1) event history, never a halt oracle.

    Return stop_reason 'empty' or 'step_limit'; a queue-size violation raises
    ResourceLimit. selected_count is within this bounded execution only.
    """
    if selected_symbol is not None:
        _symbol(program, selected_symbol)
    machine = Machine(program, initial, max_steps=max_steps,
                      max_queue_symbols=max_queue_symbols)
    count, first = 0, None
    while machine.queue_symbols and machine.steps < max_steps:
        event = machine.tick()
        if selected_symbol is not None:
            position = selection_position(program, event, selected_symbol)
            if position is not None:
                count += 1
                if first is None:
                    first = position
    return Evaluation(machine.snapshot(), machine.steps, machine.peak_queue_symbols,
                      "empty" if machine.queue_symbols == 0 else "step_limit", count, first)


def simulation_bounds(program: Program, *, max_source_steps: int,
                      max_queue_symbols: int) -> tuple[int, int]:
    """Sufficient (CTS steps, peak CTS bits) for bounded source trajectories.

    Covers accepted source microsteps, including their transient bit growth;
    it does not assert that arbitrary source runs respect the source bound.
    """
    _program(program)
    _natural(max_source_steps, "max_source_steps")
    _natural(max_queue_symbols, "max_queue_symbols")
    m = program.alphabet_size
    return (m * max_source_steps,
            m * max_queue_symbols + m - 1 if max_queue_symbols else 0)
