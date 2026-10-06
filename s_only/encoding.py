"""Closed-S initial encodings of finite, positive-period ordinary binary CTSs.

Independent implementation of Cinematic Strawberry's mathematical constructors,
Sections 3, 4.2 and Appendix E.1, pinned at 85a867988442fc423279341200f81634a1e65582.
The bottom-up dispatcher layout also follows BalancedActionTree.lean at that
commit. This module constructs syntax only; it supplies no reduction strategy,
checkpoint decoder, source simulation or universality claim.
"""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from typing import Iterator

from .cts import Program
from .terms import App, S, Term, nodes


B = App(S, S)
PI = App(S, B)
C0 = App(PI, B)
_VALUE_ZERO = App(S, C0)
VALUES = (_VALUE_ZERO, App(S, _VALUE_ZERO))
LIVE = (App(B, VALUES[0]), App(B, VALUES[1]))
HALT = App(B, App(B, S))


class EncodingLimit(ValueError):
    """An explicit inspection bound would be exceeded."""


def _word(word: str) -> None:
    if not isinstance(word, str) or any(bit not in "01" for bit in word):
        raise ValueError("a binary word must be a string containing only 0 and 1")


def _program(program: Program) -> None:
    if not isinstance(program, Program):
        raise TypeError("program must be s_only.cts.Program")


def _bound(value: int, name: str, *, positive: bool = False) -> None:
    if type(value) is not int or value < (1 if positive else 0):
        adjective = "positive" if positive else "nonnegative"
        raise ValueError(f"{name} must be a {adjective} integer")


class _Arena:
    """Per-construction interning by child identity, never recursive term hash.

    All cached children stay alive in the cached applications. Identical append
    suffixes and dispatcher subtrees share immutable objects, but cached term
    sizes continue to count every unfolded occurrence.
    """

    def __init__(self):
        self.cache: dict[tuple[int, int], App] = {}
        stack = [B, C0, PI, *VALUES, *LIVE, HALT]
        while stack:
            term = stack.pop()
            if isinstance(term, App):
                key = (id(term.left), id(term.right))
                if key not in self.cache:
                    self.cache[key] = term
                    stack.extend((term.left, term.right))

    def app(self, left: Term, right: Term) -> App:
        key = (id(left), id(right))
        result = self.cache.get(key)
        if result is None:
            result = App(left, right)
            self.cache[key] = result
        return result

    def routine(self, word: str) -> Term:
        out = PI
        for bit in reversed(word):
            # Push_J(N) = S (S N) J; reverse construction emits forward order.
            out = self.app(self.app(S, self.app(S, out)), LIVE[bit == "1"])
        return out


def append_routine(word: str) -> Term:
    """The literal appender for word, terminating at PI; empty returns PI."""
    _word(word)
    return _Arena().routine(word)


def encode_word(word: str) -> Term:
    """Wrap incoming bits outside the preceding word; logical front is inner."""
    _word(word)
    out = S
    for bit in word:
        out = App(LIVE[bit == "1"], out)
    return out


@dataclass(frozen=True, slots=True)
class CompiledProgram:
    """Reusable, input-independent dispatcher and raw phase-major actions.

    action_terms[2*j] is PI and action_terms[2*j+1] appends appendants[j].
    The Python tuple is construction metadata, not extra symbols in the term.
    """

    program: Program
    action_terms: tuple[Term, ...]
    actions: Term
    act: Term

    def encode(self, word: str) -> Term:
        """Encode a phase-zero initial word using this fixed dispatcher."""
        seed = App(S, encode_word(word))
        environment = App(S, App(App(S, self.act), seed))
        return App(App(C0, C0), environment)


def compile_program(program: Program) -> CompiledProgram:
    """Compile a deterministic adjacent-pairing dispatcher, without padding.

    Each round pairs adjacent trees from left to right and carries an unpaired
    final tree unchanged. Labels remain (0,0),(0,1),(1,0),(1,1),... .
    """
    _program(program)
    arena = _Arena()
    routines: dict[str, Term] = {"": PI}
    actions: list[Term] = []
    for word in program.appendants:
        if word not in routines:
            routines[word] = arena.routine(word)
        actions.extend((PI, routines[word]))
    forest: list[Term] = [arena.app(B, action) for action in actions]
    while len(forest) > 1:
        next_round: list[Term] = []
        for index in range(0, len(forest) - 1, 2):
            fork = arena.app(arena.app(S, forest[index]), forest[index + 1])
            next_round.append(arena.app(B, fork))
        if len(forest) % 2:
            next_round.append(forest[-1])
        forest = next_round
    dispatcher = forest[0]
    act = arena.app(arena.app(S, HALT), dispatcher)
    return CompiledProgram(program, tuple(actions), dispatcher, act)


def encode(program: Program, word: str) -> Term:
    """Construct the complete closed initial term (C0 C0) E* at phase zero."""
    _word(word)
    return compile_program(program).encode(word)


@dataclass(frozen=True, slots=True)
class EncodingStats:
    phase_count: int
    source_data_bits: int
    source_data_ones: int
    total_appendant_bits: int
    total_appendant_ones: int
    unique_appendant_count: int
    nonempty_appendant_count: int
    word_nodes: int
    dispatcher_nodes: int
    initial_nodes: int
    initial_s_leaves: int


def encoding_stats(program: Program, word: str) -> EncodingStats:
    """Exact symbolic unfolded sizes; does not allocate any encoded term.

    For p phases, M appendant bits, O appendant ones, n data bits and u data
    ones, initial_nodes = 33 + 32*p + 20*M + 2*O + 16*n + 2*u.
    Identical appendants at different phases contribute once per occurrence.
    """
    _program(program)
    _word(word)
    p, n, u = len(program.appendants), len(word), word.count("1")
    m = sum(map(len, program.appendants))
    o = sum(appendant.count("1") for appendant in program.appendants)
    word_nodes = 1 + 16 * n + 2 * u
    dispatcher_nodes = 32 * p - 7 + 20 * m + 2 * o
    initial_nodes = 39 + dispatcher_nodes + word_nodes
    return EncodingStats(p, n, u, m, o, len(set(program.appendants)),
                         sum(bool(item) for item in program.appendants),
                         word_nodes, dispatcher_nodes, initial_nodes,
                         (initial_nodes + 1) // 2)


def unique_objects(term: Term) -> int:
    """Count reachable object identities, including S, separately from nodes."""
    seen: set[int] = set()
    stack = [term]
    while stack:
        item = stack.pop()
        if id(item) in seen:
            continue
        seen.add(id(item))
        if isinstance(item, App):
            stack.extend((item.left, item.right))
        elif item is not S:
            raise TypeError("expected a closed S term")
    return len(seen)


def iter_prefix_chunks(term: Term, *, max_nodes: int,
                       chunk_size: int = 65_536) -> Iterator[bytes]:
    """Stream complete unfolded A/S preorder bytes under an explicit size cap.

    Memory is O(tree depth + chunk_size), independent of serialized length.
    The bound is checked before emitting the first byte. A shared subtree is
    visited at each occurrence, exactly as in terms.prefix.
    """
    _bound(max_nodes, "max_nodes")
    _bound(chunk_size, "chunk_size", positive=True)
    if term is not S and not isinstance(term, App):
        raise TypeError("expected a closed S term")
    if nodes(term) > max_nodes:
        raise EncodingLimit(f"prefix requires {nodes(term)} nodes; cap is {max_nodes}")
    pending = [term]
    buffer = bytearray()
    while pending:
        item = pending.pop()
        if isinstance(item, App):
            buffer.append(65)  # A
            pending.extend((item.right, item.left))
        else:
            buffer.append(83)  # S
        if len(buffer) == chunk_size:
            yield bytes(buffer)
            buffer.clear()
    if buffer:
        yield bytes(buffer)


def prefix_sha256(term: Term, *, max_nodes: int,
                  chunk_size: int = 65_536) -> str:
    """SHA-256 of complete unfolded A/S preorder, with no full string copy."""
    digest = sha256()
    for chunk in iter_prefix_chunks(term, max_nodes=max_nodes, chunk_size=chunk_size):
        digest.update(chunk)
    return digest.hexdigest()
