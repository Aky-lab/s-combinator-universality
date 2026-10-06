"""Immutable closed S terms with occurrence-tree size accounting."""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import TypeAlias


@dataclass(frozen=True, slots=True)
class _S:
    pass


S = _S()


@dataclass(frozen=True, slots=True)
class App:
    left: Term
    right: Term
    _leaves: int = field(init=False, repr=False, compare=False)

    def __post_init__(self):
        if not isinstance(self.left, (_S, App)) or not isinstance(self.right, (_S, App)):
            raise TypeError("application children must be S terms")
        object.__setattr__(self, "_leaves", leaves(self.left) + leaves(self.right))


Term: TypeAlias = _S | App


def leaves(term: Term) -> int:
    return term._leaves if isinstance(term, App) else 1


def nodes(term: Term) -> int:
    return 2 * leaves(term) - 1


def parse(source: str) -> Term:
    """Parse S, juxtaposition and parentheses; application associates left."""
    frames: list[Term | None] = [None]
    for offset, char in enumerate(source):
        if char.isspace():
            continue
        if char == "(":
            frames.append(None)
            continue
        if char == "S":
            term = S
        elif char == ")":
            if len(frames) == 1 or frames[-1] is None:
                raise ValueError(f"unexpected ')' at offset {offset}")
            term = frames.pop()
        else:
            raise ValueError(f"unexpected character {char!r} at offset {offset}")
        frames[-1] = term if frames[-1] is None else App(frames[-1], term)
    if len(frames) != 1 or frames[0] is None:
        raise ValueError("empty expression or unclosed parenthesis")
    return frames[0]


def format_term(term: Term) -> str:
    """Fully parenthesized, unambiguous syntax; iterative on deep trees."""
    output: list[str] = []
    stack: list[Term | str] = [term]
    while stack:
        item = stack.pop()
        if isinstance(item, str):
            output.append(item)
        elif isinstance(item, App):
            stack.extend([")", item.right, " ", item.left, "("])
        else:
            output.append("S")
    return "".join(output)


def prefix(term: Term) -> str:
    """Preorder tokens: S is a leaf, A is binary application."""
    output = []
    stack = [term]
    while stack:
        item = stack.pop()
        if isinstance(item, App):
            output.append("A")
            stack.extend([item.right, item.left])
        else:
            output.append("S")
    return "".join(output)
