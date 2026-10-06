"""Bounded, history-free result readers for the compact UT19 first-event form.

The input is the current alternating-tag or ordinary CTS configuration only.
Acceptance checks Reset-word syntax, not reachability or whether this is the
first event. See docs/ut19-readout.md for the deliberately source-free language.
Published symbols in that document are one-based; tag symbols here are zero-based.
"""
from dataclasses import dataclass
from typing import Iterator

from . import alternating_tag as tag
from . import cts

ResourceLimit = cts.ResourceLimit
_RESET_ALPHABET = (3, 9, 10, 15, 17)


def _natural(value: int, name: str) -> None:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative plain integer")


@dataclass(frozen=True, slots=True)
class ReadoutLimits:
    """Input and output budgets; zero counts as one binary output digit.

    max_word_bits bounds the supplied CTS suffix, excluding the 17 implicit
    zeroes. max_queue_symbols includes its logically restored head symbol.
    max_output_bits bounds sum(max(1, value.bit_length())) across the result.
    """

    max_queue_symbols: int = 1_000_000
    max_word_bits: int = 19_000_000
    max_counters: int = 100_000
    max_output_bits: int = 1_000_000

    def __post_init__(self):
        for name in self.__dataclass_fields__:
            _natural(getattr(self, name), name)


def _limits(limits: ReadoutLimits) -> None:
    if type(limits) is not ReadoutLimits:
        raise ValueError("limits must be an exact ReadoutLimits")
    # Recheck even a frozen instance: do not trust object.__setattr__ misuse.
    for name in ReadoutLimits.__dataclass_fields__:
        _natural(getattr(limits, name), name)


def _tag_symbols(queue: tuple[int, ...]) -> Iterator[int]:
    for symbol in queue:
        if type(symbol) is not int or symbol not in _RESET_ALPHABET:
            raise ValueError("symbol is outside the UT19 Reset alphabet")
        yield symbol


def _cts_symbols(word: str) -> Iterator[int]:
    # The head code is logically 0^17 + '10', so its symbol is already known.
    # All remaining blocks have their ordinary 19-bit alignment. No restored
    # word, decoded queue, code table, or evaluator is constructed.
    yield 17
    for start in range(2, len(word), 19):
        block = word[start:start + 19]
        if block.count("1") != 1 or block.count("0") != 18:
            raise ValueError("CTS suffix contains a malformed one-hot block")
        symbol = block.index("1")
        if symbol not in _RESET_ALPHABET:
            raise ValueError("one-hot symbol is outside the UT19 Reset alphabet")
        yield symbol


class _Cursor:
    __slots__ = ("_symbols", "head")

    def __init__(self, symbols: Iterator[int]):
        self._symbols = symbols
        self.head = next(symbols, None)

    def advance(self) -> None:
        self.head = next(self._symbols, None)

    def expect(self, symbol: int) -> None:
        if self.head != symbol:
            raise ValueError("malformed or truncated UT19 Reset memory")
        self.advance()


def _reset_memory(cursor: _Cursor) -> None:
    """Read one nonempty R = ([18,10] [18,4]?)+ in published labels."""
    cursor.expect(17)
    cursor.expect(9)
    inverter_allowed = True
    while cursor.head == 17:
        cursor.advance()
        if cursor.head == 9:
            inverter_allowed = True
        elif cursor.head == 3 and inverter_allowed:
            inverter_allowed = False
        else:
            raise ValueError("malformed cell or repeated Reset inverter")
        cursor.advance()


def _final_memory(cursor: _Cursor) -> None:
    """Read nonempty T = (([10,10] | [11,10]) [4,4]?)+, then EOF."""
    if cursor.head not in (9, 10):
        raise ValueError("missing final UT19 Reset memory")
    while cursor.head in (9, 10):
        cursor.advance()
        cursor.expect(9)
        if cursor.head == 3:
            cursor.expect(3)
            cursor.expect(3)
    if cursor.head is not None:
        raise ValueError("trailing data after final UT19 Reset memory")


def _read_symbols(symbols: Iterator[int], limits: ReadoutLimits) -> tuple[int, ...]:
    cursor = _Cursor(symbols)
    values = []
    output_bits = 0
    _reset_memory(cursor)
    while cursor.head == 15:
        # Check before retaining a new counter. No fixed source counter count.
        if len(values) >= limits.max_counters:
            raise ResourceLimit("result exceeds max_counters")
        run_length = 0
        while cursor.head == 15:
            run_length += 1
            cursor.advance()
        exponent = run_length.bit_length() - 1
        if (run_length < 4 or run_length & (run_length - 1)
                or exponent % 2):
            raise ValueError("counter run length must be a power of four at least four")
        value = exponent // 2 - 1
        output_bits += max(1, value.bit_length())
        if output_bits > limits.max_output_bits:
            raise ResourceLimit("result exceeds max_output_bits")
        values.append(value)
        _reset_memory(cursor)
    if not values:
        raise ValueError("the compact UT19 output requires at least one counter")
    _final_memory(cursor)
    return tuple(values)


def read_tag_result(state: tag.Configuration, *,
                    limits: ReadoutLimits = ReadoutLimits()) -> tuple[int, ...]:
    """Read a take/head-17 tag state in the documented Reset output language.

    All fields must have their exact plain types. Size is checked before any
    symbol scan. ValueError means invalid input; ResourceLimit means refusal.
    Neither outcome establishes halting or nonhalting of an encoded source.
    """
    _limits(limits)
    if type(state) is not tag.Configuration or type(state.queue) is not tuple:
        raise ValueError("state must be an exact tag Configuration with a plain tuple queue")
    if type(state.phase) is not str or state.phase != tag.TAKE:
        raise ValueError("a UT19 result must be in take phase")
    if len(state.queue) > limits.max_queue_symbols:
        raise ResourceLimit("input exceeds max_queue_symbols")
    if not state.queue or type(state.queue[0]) is not int or state.queue[0] != 17:
        raise ValueError("a UT19 result must have head symbol 17 (published 18)")
    return _read_symbols(_tag_symbols(state.queue), limits)


def read_cts_result(state: cts.Configuration, *,
                    limits: ReadoutLimits = ReadoutLimits()) -> tuple[int, ...]:
    """Read an ordinary 38-phase UT19 CTS event at prephase 17, head bit one.

    Exactly 17 leading zeroes have already been deleted from the first code.
    The remaining head block is '10'; whole 19-bit one-hot blocks follow it.
    Prefix restoration is logical, and both input caps precede the bit scan.
    """
    _limits(limits)
    if type(state) is not cts.Configuration or type(state.word) is not str:
        raise ValueError("state must be an exact CTS Configuration with a plain string word")
    if type(state.phase) is not int or state.phase != 17:
        raise ValueError("a UT19 CTS result must be at phase 17")
    size = len(state.word)
    if size > limits.max_word_bits:
        raise ResourceLimit("input exceeds max_word_bits")
    restored_size = size + 17
    if restored_size > 19 * limits.max_queue_symbols:
        raise ResourceLimit("decoded input exceeds max_queue_symbols")
    if restored_size % 19 or not state.word.startswith("10"):
        raise ValueError("CTS result must be '10' followed by whole 19-bit blocks")
    return _read_symbols(_cts_symbols(state.word), limits)
