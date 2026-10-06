"""Exact succinct code for the occurrence-indexed restoring probe table.

Unlike :mod:`s_only.probes`, this representation retains immutable pattern DAG
metadata.  Lookup decodes a finite table entry; it never reads an input term.
See ``docs/succinct-probes.md`` for the indexing proof and resource model.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from .probes import HOLE, LITERAL_S, Incoming, Instruction, NodeKind, Pattern


@dataclass(frozen=True, slots=True)
class _Descriptor:
    kind: Literal["_", "S", "pair"]
    left: int | None
    right: int | None
    width: int
    ticks: int
    height: int


def _leaf(kind: str) -> _Descriptor:
    width = int(kind == LITERAL_S)
    return _Descriptor(kind, None, None, width, width, 1)


def _pair(left: int, right: int, nodes: list[_Descriptor]) -> _Descriptor:
    a, b = nodes[left], nodes[right]
    return _Descriptor("pair", left, right, 6 + a.width + b.width,
                       5 + a.ticks + b.ticks, 1 + max(a.height, b.height))


@dataclass(frozen=True, slots=True)
class SuccinctProbeTable:
    """An immutable descriptor of exactly ``2 + W(pattern)`` finite controls.

    ``nodes`` is a child-before-parent DAG.  Its integer counts refer to the
    unfolded occurrence tree, even when two child indices are equal.  It is
    code, shared by every invocation; no invocation changes this object.
    """

    nodes: tuple[_Descriptor, ...]
    root: int

    def __post_init__(self):
        if type(self.nodes) is not tuple or not self.nodes:
            raise ValueError("nodes must be a nonempty immutable tuple")
        if type(self.root) is not int or self.root != len(self.nodes) - 1:
            raise ValueError("root must be the final descriptor")
        for index, node in enumerate(self.nodes):
            if type(node) is not _Descriptor:
                raise ValueError("nodes must be exact immutable descriptors")
            if type(node.kind) is not str or node.kind not in (HOLE, LITERAL_S, "pair"):
                raise ValueError("unknown descriptor kind")
            if any(type(value) is not int or value < 0
                   for value in (node.width, node.ticks, node.height)):
                raise ValueError("descriptor counts must be nonnegative plain integers")
            if node.kind == "pair":
                if any(type(child) is not int or not 0 <= child < index
                       for child in (node.left, node.right)):
                    raise ValueError("children must precede their parent descriptor")
                a, b = self.nodes[node.left], self.nodes[node.right]
                expected = (6 + a.width + b.width, 5 + a.ticks + b.ticks,
                            1 + max(a.height, b.height))
            else:
                if node.left is not None or node.right is not None:
                    raise ValueError("leaves cannot have child descriptors")
                width = int(node.kind == LITERAL_S)
                expected = (width, width, 1)
            if (node.width, node.ticks, node.height) != expected:
                raise ValueError("descriptor counts disagree with their children")

    @property
    def state_count(self) -> int:
        """Virtual table size, not the number of allocated Python rows."""
        return 2 + self.nodes[self.root].width

    @property
    def start(self) -> int:
        # A hole enters its yes continuation without allocating a state.
        return self.state_count - 1

    @property
    def tick_bound(self) -> int:
        """Exact longest path from start, identical to the materialized table."""
        return self.nodes[self.root].ticks

    @property
    def lookup_depth_bound(self) -> int:
        """At most this many decoder-loop iterations occur per transition lookup."""
        return self.nodes[self.root].height

    def _validate_control(self, control: int) -> None:
        if type(control) is not int or not 0 <= control < self.state_count:
            raise ValueError("unknown finite control")

    def answer(self, control: int) -> bool | None:
        self._validate_control(control)
        if control < 2:
            return bool(control)
        return None

    def transition(self, control: int, kind: NodeKind, incoming: Incoming) -> Instruction:
        """Decode one exact materialized entry using only the finite inputs.

        Each descent selects one smaller descriptor and one occurrence interval.
        This bounded calculation uses no term, cursor, history, or hash cache.
        It creates no persistent runtime state or procedure-return stack.
        """
        self._validate_control(control)
        if (type(kind) is not str or kind not in ("S", "application")
                or type(incoming) is not str or incoming not in ("root", "L", "R")):
            raise ValueError("unknown local observation")
        if control < 2:
            return Instruction("true" if control else "false")

        descriptor, origin, yes, no = self.root, 2, 1, 0
        while True:
            node = self.nodes[descriptor]
            if node.kind == LITERAL_S:
                return Instruction("stay", yes if kind == "S" else no)
            # No hole interval contains a control: its width is zero.
            right_origin = origin + 2
            right_width = self.nodes[node.right].width
            right_move = right_origin + right_width
            after_left = right_move + 1
            left_origin = right_move + 2
            left_move = left_origin + self.nodes[node.left].width
            if control == origin:
                return Instruction("U", yes)
            if control == origin + 1:
                return Instruction("U", no)
            if control < right_move:
                descriptor, origin, yes, no = node.right, right_origin, origin, origin + 1
                continue
            if control == right_move:
                right_entry = origin if right_width == 0 else right_move - 1
                return Instruction("R", right_entry)
            if control == after_left:
                return Instruction("U", right_move)
            if control < left_move:
                descriptor, origin, yes, no = node.left, left_origin, after_left, origin + 1
                continue
            if control == left_move:
                left_entry = after_left if self.nodes[node.left].width == 0 else left_move - 1
                return Instruction("L", left_entry)
            return Instruction("stay", no if kind == "S" else left_move)


def compile_pattern(pattern: Pattern) -> SuccinctProbeTable:
    """Validate and count a shared pattern DAG without occurrence expansion.

    Identity maps and the explicit DFS stack exist only during compilation.
    Pattern tuples are never structurally compared or hashed.  Only plain
    strings and exact length-two tuples are accepted, as in the original syntax.
    """
    nodes: list[_Descriptor] = []
    leaves: dict[str, int] = {}
    completed: dict[int, int] = {}
    active: set[int] = set()
    pending = [(pattern, False)]

    def child_index(child: Pattern) -> int:
        if type(child) is str:
            return leaves[child]
        return completed[id(child)]

    while pending:
        node, exiting = pending.pop()
        if type(node) is str:
            if node not in (HOLE, LITERAL_S):
                raise ValueError("a pattern is '_', 'S', or a pair of patterns")
            if node not in leaves:
                leaves[node] = len(nodes)
                nodes.append(_leaf(node))
            continue
        if type(node) is not tuple or len(node) != 2:
            raise ValueError("a pattern is '_', 'S', or a pair of patterns")
        identity = id(node)
        if exiting:
            left, right = child_index(node[0]), child_index(node[1])
            completed[identity] = len(nodes)
            nodes.append(_pair(left, right, nodes))
            active.remove(identity)
        elif identity in active:
            raise ValueError("a pattern DAG must be acyclic")
        elif identity not in completed:
            active.add(identity)
            # Stack order visits left, then right, then the parent.  Emission
            # order is separately decoded and is right-before-left.
            pending.extend(((node, True), (node[1], False), (node[0], False)))

    return SuccinctProbeTable(tuple(nodes), child_index(pattern))
