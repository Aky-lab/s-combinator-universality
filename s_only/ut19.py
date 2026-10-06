"""Compact Brainpocalypse II -> UT19 source encoding and bounded semantics.

Independently derived from the CC0 wiki construction. UT19's published labels
are 1..19; the generic tag API uses labels 0..18. The source simulation proof
is in docs/ut19-simulation-invariants.md; the exact one-hot translation is in
docs/alternating-tag.md. Implemented resource bounds are explicit and adjustable.
"""
from dataclasses import dataclass
import re

from . import alternating_tag as tag
from . import cts

ResourceLimit = cts.ResourceLimit

UT19_PRODUCTIONS = (
    (2, 3), (4, 4), (18, 4), (1, 1, 19),
    (7, 9), (8, 9), (10, 10), (11, 10), (18, 10),
    (5, 6), (6, 5, 19), (14, 14, 14, 14), (15,),
    (16, 16), (16, 17), (12, 13), (12, 12, 12, 12), (18,), (),
)
TAG_PROGRAM = tag.Program(tuple(tuple(x - 1 for x in row)
                                for row in UT19_PRODUCTIONS))
HALT_SYMBOL = 18  # Published, one-based label; this is a designated event only.
HALT_INDEX = HALT_SYMBOL - 1


def _natural(value: int, name: str) -> None:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


@dataclass(frozen=True, slots=True)
class Command:
    counter: int
    delta: int

    def __post_init__(self):
        if type(self.counter) is not int or self.counter < 1:
            raise ValueError("counter labels must be positive integers")
        if type(self.delta) is not int or self.delta not in (-1, 1):
            raise ValueError("command delta must be -1 or +1")

    def __str__(self):
        return ("+" if self.delta == 1 else "-") + str(self.counter)


@dataclass(frozen=True, slots=True)
class SourceProgram:
    commands: tuple[Command, ...]

    def __post_init__(self):
        if type(self.commands) is not tuple or not self.commands:
            raise ValueError("commands must be a nonempty tuple")
        if any(type(command) is not Command for command in self.commands):
            raise ValueError("every source command must be a Command")
        count = max(command.counter for command in self.commands)
        # Check before constructing a range/set indexed by a possibly huge label.
        if count > len(self.commands) or len({c.counter for c in self.commands}) != count:
            raise ValueError("source counter labels must be dense from 1")

    @property
    def counter_count(self) -> int:
        return max(command.counter for command in self.commands)

    def __str__(self):
        return " ".join(map(str, self.commands))


def parse_source(text: str, *, max_chars: int = 100_000,
                 max_commands: int = 256, max_counters: int = 256) -> SourceProgram:
    """Bounded strict numeric syntax, e.g. '+1 -2 +1'; no implicit labels."""
    for value, name in ((max_chars, "max_chars"), (max_commands, "max_commands"),
                        (max_counters, "max_counters")):
        _natural(value, name)
    if type(text) is not str:
        raise ValueError("source must be text")
    if len(text) > max_chars:
        raise ResourceLimit("source exceeds max_chars")
    commands = []
    for match in re.finditer(r"\S+", text):
        if len(commands) >= max_commands:
            raise ResourceLimit("source exceeds max_commands")
        token = match.group()
        if re.fullmatch(r"[+-][1-9][0-9]*", token) is None:
            raise ValueError("each command must be a sign and a positive decimal label")
        # Reject oversized decimal labels before constructing the integer.
        digits = token[1:]
        cap = str(max_counters)
        if len(digits) > len(cap) or (len(digits) == len(cap) and digits > cap):
            raise ResourceLimit("source exceeds max_counters")
        commands.append(Command(int(digits), 1 if token[0] == "+" else -1))
    return SourceProgram(tuple(commands))


@dataclass(frozen=True, slots=True)
class SourceConfiguration:
    pc: int
    counters: tuple[int, ...]

    def __post_init__(self):
        _natural(self.pc, "pc")
        if type(self.counters) is not tuple:
            raise ValueError("counters must be an immutable tuple")
        for value in self.counters:
            _natural(value, "counter value")


def initial_source(program: SourceProgram, *, max_counters: int) -> SourceConfiguration:
    if type(program) is not SourceProgram:
        raise ValueError("program must be a SourceProgram")
    _natural(max_counters, "max_counters")
    if program.counter_count > max_counters:
        raise ResourceLimit("source exceeds max_counters")
    return SourceConfiguration(0, (0,) * program.counter_count)


def source_step(program: SourceProgram, state: SourceConfiguration, *,
                max_counters: int, max_counter_value: int) -> SourceConfiguration:
    """One BP2 command. Decrementing zero sets 1 and restarts at pc=0.

    The size and next counter-value limits are checked before copying counters.
    Falling off the program is a halt; calling step there raises StopIteration.
    """
    _natural(max_counters, "max_counters")
    _natural(max_counter_value, "max_counter_value")
    if type(program) is not SourceProgram or type(state) is not SourceConfiguration:
        raise ValueError("expected SourceProgram and SourceConfiguration")
    if len(state.counters) != program.counter_count or state.pc > len(program.commands):
        raise ValueError("source configuration does not match program")
    if len(state.counters) > max_counters or any(x > max_counter_value for x in state.counters):
        raise ResourceLimit("initial source configuration exceeds bounds")
    if state.pc == len(program.commands):
        raise StopIteration("source fell off the end")
    command = program.commands[state.pc]
    old = state.counters[command.counter - 1]
    restart = command.delta == -1 and old == 0
    value = 1 if restart else old + command.delta
    if value > max_counter_value:
        raise ResourceLimit("next source value exceeds max_counter_value")
    counters = list(state.counters)
    counters[command.counter - 1] = value
    return SourceConfiguration(0 if restart else state.pc + 1, tuple(counters))


@dataclass(frozen=True, slots=True)
class EncodingLimits:
    max_commands: int = 256
    max_counters: int = 256
    # Bounds one family of vectors; both desired and initial are retained.
    max_memory_entries: int = 300_000
    max_seed_symbols: int = 1_000_000
    max_seed_bits: int = 19_000_000

    def __post_init__(self):
        for name in self.__dataclass_fields__:
            _natural(getattr(self, name), name)


@dataclass(frozen=True, slots=True)
class MemoryBlock:
    position: int
    desired: tuple[int, ...]
    initial: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class Encoding:
    source: SourceProgram
    expanded_commands: int
    blocks: tuple[MemoryBlock, ...]
    queue: tuple[int, ...]  # Published labels 1..19, no cleanup padding.

    @property
    def seed_symbols(self) -> int:
        return len(self.queue)

    @property
    def seed_bits(self) -> int:
        return 19 * len(self.queue)

    def tag_configuration(self, *, max_queue_symbols: int) -> tag.Configuration:
        _natural(max_queue_symbols, "max_queue_symbols")
        if len(self.queue) > max_queue_symbols:
            raise ResourceLimit("seed exceeds max_queue_symbols")
        return tag.Configuration(tuple(x - 1 for x in self.queue), tag.TAKE)

    def cts_configuration(self, *, max_word_bits: int) -> cts.Configuration:
        _natural(max_word_bits, "max_word_bits")
        if self.seed_bits > max_word_bits:
            raise ResourceLimit("seed exceeds max_word_bits")
        state = self.tag_configuration(max_queue_symbols=self.seed_symbols)
        return tag.encode_configuration(TAG_PROGRAM, state, max_word_bits=max_word_bits)


def running_xor_initial(desired: tuple[int, ...], *, max_entries: int) -> tuple[int, ...]:
    """Subset-XOR transform a_i = XOR_{j: i & j == i} desired_j.

    Uses an in-place butterfly on a bounded copy; the returned tuple is immutable.
    Length must be a positive power of two. The transform is self-inverse over F2.
    """
    _natural(max_entries, "max_entries")
    if type(desired) is not tuple:
        raise ValueError("desired widths must be an immutable tuple")
    length = len(desired)
    if length > max_entries:
        raise ResourceLimit("running-XOR vector exceeds max_entries")
    if not length or length & (length - 1):
        raise ValueError("running-XOR length must be a positive power of two")
    if any(type(x) is not int or x not in (0, 1) for x in desired):
        raise ValueError("running-XOR entries must be integer bits")
    result = list(desired)
    stride = 1
    while stride < length:
        for start in range(0, length, 2 * stride):
            for offset in range(stride):
                result[start + offset] ^= result[start + stride + offset]
        stride *= 2
    return tuple(result)


def _widths(program: SourceProgram, position: int, expanded: int) -> tuple[int, ...]:
    count = program.counter_count
    first, last = int(position == 1), int(position == count + 2)
    result = [last, 0]  # Initialization marker ^.
    for command in program.commands:
        adjacent = int(command.counter in (position - 1, position))
        result.extend((0, adjacent ^ first ^ last) if command.delta == 1
                      else (first | last, adjacent))
    adjacent_halt = int(count + 1 in (position - 1, position))
    result.extend((first | last, adjacent_halt & (1 - last), 0, 0))
    for _ in range(expanded - len(program.commands) - 3):
        result.extend((first | last, 0))
    return tuple(result)


def encode_source(program: SourceProgram, *, limits: EncodingLimits = EncodingLimits()) -> Encoding:
    """Construct the compact no-cleanup-padding seed, with staged preflight.

    Preflight commands, counters, entries per vector family and a size lower bound
    BEFORE allocating vectors. Then compute exact inverter/seed counts and
    check symbol and bit caps BEFORE allocating the seed. No compiler subprocess,
    source execution, unbounded label expansion, or cleanup padding is involved.
    """
    if type(program) is not SourceProgram or type(limits) is not EncodingLimits:
        raise ValueError("expected SourceProgram and EncodingLimits")
    length, count = len(program.commands), program.counter_count
    if length > limits.max_commands or count > limits.max_counters:
        raise ResourceLimit("source exceeds command or counter limit")
    expanded = 1 << (length + 2).bit_length()  # Next power of two >= L+3.
    entries = 2 * expanded * (count + 2)
    if entries > limits.max_memory_entries:
        raise ResourceLimit("encoder exceeds max_memory_entries")
    minimum = 1 + 4 * (count + 1) + 2 * entries
    if minimum > limits.max_seed_symbols or 19 * minimum > limits.max_seed_bits:
        raise ResourceLimit("minimum seed exceeds symbol or bit limit")
    blocks = []
    inverters = 0
    for position in range(1, count + 3):
        desired = _widths(program, position, expanded)
        initial = running_xor_initial(desired, max_entries=2 * expanded)
        inverters += sum(initial)
        blocks.append(MemoryBlock(position, desired, initial))
    exact = minimum + 3 * inverters
    if exact > limits.max_seed_symbols or 19 * exact > limits.max_seed_bits:
        raise ResourceLimit("exact seed exceeds symbol or bit limit")
    queue = _materialize_seed(blocks, count)
    if len(queue) != exact:
        raise AssertionError("seed size accounting disagrees with construction")
    return Encoding(program, expanded, tuple(blocks), queue)


def _materialize_seed(blocks, count):
    """Caller must have checked exact symbol and bit budgets first."""
    queue = [19]
    for block in blocks:
        for bit in block.initial:
            queue.extend((5, 6, 1, 1, 19) if bit else (5, 6))
        if block.position <= count + 1:
            queue.extend((12, 13, 12, 13))
    return tuple(queue)


def compile_cts(*, max_phases: int = 38, max_program_bits: int = 760) -> cts.Program:
    return tag.compile_program(TAG_PROGRAM, max_phases=max_phases,
                               max_program_bits=max_program_bits)


def selected_source_event(state: tag.Configuration) -> bool:
    """PRE-transition take of published symbol 18, not presence anywhere."""
    if type(state) is not tag.Configuration:
        raise ValueError("state must be an alternating-tag Configuration")
    return state.phase == tag.TAKE and bool(state.queue) and state.queue[0] == HALT_INDEX
