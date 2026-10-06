"""Bottom-up recognition of descendant occurrences of a fixed S-tree pattern.

The immutable code is a canonical subpattern DAG; one bounded integer is an
automaton state. ``evaluate`` is a separate, input-bounded DAG evaluator, not
the single-zipper native reduction controller. See docs/pattern-automaton.md.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import isfinite
from time import monotonic

from .probes import HOLE, LITERAL_S, Pattern
from .terms import App, S, Term


class ResourceLimit(RuntimeError):
    """A compilation/evaluation cap expired; this is never a negative answer."""


def _natural(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(name + " must be a nonnegative plain integer")


class _Budget:
    __slots__ = ("start", "seconds")

    def __init__(self, seconds):
        if type(seconds) is not int and type(seconds) is not float:
            raise ValueError("max_seconds must be a finite nonnegative number")
        try:
            valid = isfinite(seconds) and seconds >= 0
        except OverflowError:
            valid = False
        if not valid:
            raise ValueError("max_seconds must be a finite nonnegative number")
        self.start, self.seconds = monotonic(), seconds

    def check(self):
        if monotonic() - self.start >= self.seconds:
            raise ResourceLimit("max_seconds exhausted")


@dataclass(frozen=True, slots=True)
class Descriptor:
    """A leaf, or a pair of smaller canonical descriptor indices."""

    kind: str
    left: int | None = None
    right: int | None = None


@dataclass(frozen=True, slots=True)
class PatternAutomaton:
    """Fixed code for a total deterministic finite bottom-up tree automaton.

    Bits 0..k-1 name root matches; bit k records a match anywhere below.
    All 2**(k+1) bit vectors are legal states, including unreachable vectors.
    No transition table or state-space enumeration is allocated.
    """

    nodes: tuple[Descriptor, ...]
    root: int

    def __post_init__(self):
        if type(self.nodes) is not tuple or not self.nodes:
            raise ValueError("nodes must be a nonempty exact tuple")
        if type(self.root) is not int or self.root != len(self.nodes) - 1:
            raise ValueError("root must be the final descriptor index")
        seen = set()
        for index, node in enumerate(self.nodes):
            if type(node) is not Descriptor:
                raise ValueError("nodes must contain exact Descriptors")
            if type(node.kind) is not str or node.kind not in (HOLE, LITERAL_S, "pair"):
                raise ValueError("unknown descriptor kind")
            if node.kind == "pair":
                if any(type(child) is not int or not 0 <= child < index
                       for child in (node.left, node.right)):
                    raise ValueError("pair children must be preceding plain integer indices")
            elif node.left is not None or node.right is not None:
                raise ValueError("leaf descriptors cannot have children")
            # Every field is now a plain scalar. No user equality/hash is run.
            key = node.kind, node.left, node.right
            if key in seen:
                raise ValueError("duplicate descriptors are not canonical")
            seen.add(key)
        reachable, pending = set(), [self.root]
        while pending:
            index = pending.pop()
            if index in reachable:
                continue
            reachable.add(index)
            node = self.nodes[index]
            if node.kind == "pair":
                pending.extend((node.left, node.right))
        if len(reachable) != len(self.nodes):
            raise ValueError("all descriptors must be subpatterns of the root")

    @property
    def state_bits(self) -> int:
        return len(self.nodes) + 1

    @property
    def state_count_bound(self) -> int:
        """Size of the full bit-vector cover, not a minimal-state claim."""
        return 1 << self.state_bits

    def _validate_state(self, state):
        if (type(state) is not int or state < 0
                or state.bit_length() > self.state_bits):
            raise ValueError("state must be a bounded nonnegative plain integer")

    def accepts(self, state: int) -> bool:
        self._validate_state(state)
        return bool((state >> len(self.nodes)) & 1)

    def matches_root(self, state: int) -> bool:
        self._validate_state(state)
        return bool((state >> self.root) & 1)

    def transition(self, kind: str, left: int | None = None,
                   right: int | None = None) -> int:
        """Use only local node kind and bounded child states, plus fixed code.

        There is no input tree, cursor, source program, history, memo, recursive
        call, external input or resource counter in this transition function.
        """
        if type(kind) is not str or kind not in (LITERAL_S, "application"):
            raise ValueError("node kind must be 'S' or 'application'")
        if kind == LITERAL_S:
            if left is not None or right is not None:
                raise ValueError("S has no child states")
        else:
            self._validate_state(left)
            self._validate_state(right)
        flags = 0
        for index, node in enumerate(self.nodes):
            matches = (node.kind == HOLE or
                       (kind == LITERAL_S and node.kind == LITERAL_S))
            if kind == "application" and node.kind == "pair":
                matches = bool((left >> node.left) & (right >> node.right) & 1)
            if matches:
                flags |= 1 << index
        found = bool((flags >> self.root) & 1)
        if kind == "application":
            found = found or bool(((left | right) >> len(self.nodes)) & 1)
        return flags | (int(found) << len(self.nodes))


def compile_pattern(pattern: Pattern, *, max_descriptors: int = 100_000,
                    max_pattern_nodes: int = 200_000,
                    max_seconds: float = 10.0) -> PatternAutomaton:
    """Compile a finite pattern DAG without unfolding occurrences or hashing it.

    Equal subpatterns receive equal IDs by shallow integer-key interning.
    ``max_pattern_nodes`` counts distinct pair objects plus distinct atom
    kinds; ``max_descriptors`` bounds the canonical output. Time is a checked
    cooperative cap, not a substitute for an OS-level timeout.
    """
    _natural(max_descriptors, "max_descriptors")
    _natural(max_pattern_nodes, "max_pattern_nodes")
    budget = _Budget(max_seconds)
    nodes, interned, atoms, completed, active = [], {}, {}, {}, set()
    pending, visited = [(pattern, False)], 0

    def visit():
        nonlocal visited
        if visited >= max_pattern_nodes:
            raise ResourceLimit("max_pattern_nodes exhausted")
        visited += 1

    def intern(kind, left=None, right=None):
        key = kind, left, right
        index = interned.get(key)
        if index is None:
            if len(nodes) >= max_descriptors:
                raise ResourceLimit("max_descriptors exhausted")
            index = len(nodes)
            interned[key] = index
            nodes.append(Descriptor(kind, left, right))
        return index

    def child_index(child):
        return atoms[child] if type(child) is str else completed[id(child)]

    while pending:
        budget.check()
        node, exiting = pending.pop()
        if type(node) is str:
            if node not in (HOLE, LITERAL_S):
                raise ValueError("a pattern is '_', 'S', or an exact pair tuple")
            if node not in atoms:
                visit()
                atoms[node] = intern(node)
            continue
        if type(node) is not tuple or len(node) != 2:
            raise ValueError("a pattern is '_', 'S', or an exact pair tuple")
        identity = id(node)
        if exiting:
            completed[identity] = intern("pair", child_index(node[0]), child_index(node[1]))
            active.remove(identity)
        elif identity in active:
            raise ValueError("pattern must be acyclic")
        elif identity not in completed:
            visit()
            active.add(identity)
            pending.extend(((node, True), (node[1], False), (node[0], False)))
    budget.check()
    result = PatternAutomaton(tuple(nodes), child_index(pattern))
    budget.check()
    return result


def evaluate(automaton: PatternAutomaton, term: Term, *,
             max_term_nodes: int = 1_000_000,
             max_seconds: float = 10.0) -> int:
    """Evaluate on an exact finite S/App DAG with an input-bounded stack/memo.

    Identity sharing avoids occurrence expansion. Every reachable input node
    is validated, even when an accepting subtree was already found. Neither
    term equality/hash nor the cached occurrence-size field is used. Raises
    on invalid syntax, cycles or cap exhaustion rather than returning False.
    """
    if type(automaton) is not PatternAutomaton:
        raise ValueError("automaton must be an exact PatternAutomaton")
    _natural(max_term_nodes, "max_term_nodes")
    budget = _Budget(max_seconds)
    completed, active, pending = {}, set(), [(term, False)]
    visited = 0
    while pending:
        budget.check()
        node, exiting = pending.pop()
        if type(node) is not type(S) and type(node) is not App:
            raise ValueError("term must contain only exact S/App nodes")
        identity = id(node)
        if identity in completed:
            continue
        if exiting:
            completed[identity] = automaton.transition(
                "application", completed[id(node.left)], completed[id(node.right)])
            active.remove(identity)
        elif identity in active:
            raise ValueError("term must be acyclic")
        else:
            if visited >= max_term_nodes:
                raise ResourceLimit("max_term_nodes exhausted")
            visited += 1
            if type(node) is type(S):
                completed[identity] = automaton.transition(LITERAL_S)
            else:
                active.add(identity)
                pending.extend(((node, True), (node.right, False), (node.left, False)))
    budget.check()
    return completed[id(term)]
