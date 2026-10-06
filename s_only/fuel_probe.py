"""Seven fixed fuel endpoint probes for the two-phase queue dispatcher.

The structural rows are from the pinned construction's fuel admission
patterns. Each occurrence of a wildcard is independent. Their guards select
a native redex; the surrounding active-context priority is a separate layer.
"""
from functools import lru_cache

from .probes import HOLE, LITERAL_S, Cursor, compile_rows, execute
from .queue_fixture import ACT, B, C0
from .terms import App


def _apply(*patterns):
    result = patterns[0]
    for pattern in patterns[1:]:
        result = (result, pattern)
    return result


def _literal(term):
    if isinstance(term, App):
        return (_literal(term.left), _literal(term.right))
    return LITERAL_S


def fuel_rows():
    """Return (name, pattern, relative address) in the specified priority order."""
    s, h, b = LITERAL_S, HOLE, _literal(B)
    environment = (s, _apply(s, _literal(ACT), (s, h)))
    e = environment
    return (
        ("call_zero", _apply(_literal(C0), e, h), (0,)),
        ("call_positive", _apply(b, h, e, h), (0,)),
        ("positive_half", _apply(s, e, (h, e), h), ()),
        ("zero_first", _apply(b, e, (b, e), h), (0,)),
        ("zero_second", _apply(s, (b, e), (e, (b, e)), h), ()),
        ("zero_third", _apply(b, e, h, _apply(e, (b, e), h)), (0,)),
        ("zero_fourth", _apply(s, h, (e, h), h), ()),
    )


@lru_cache(maxsize=1)
def fuel_table():
    """Compile before a term is supplied; runtime stores only this finite table."""
    return compile_rows(tuple((pattern, address) for _, pattern, address in fuel_rows()))


def select_fuel(term, origin=()):
    """Select a local fuel endpoint relative to a supplied occurrence."""
    result = execute(fuel_table(), Cursor.at(term, origin))
    return result.cursor.path if result.answer else None
