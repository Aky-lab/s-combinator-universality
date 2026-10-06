"""Compile the program-specific controller's fresh-response and marked-handoff passes.

Independent finite-graph transcription of the mathematical workers in
``RootResetFreshResponsePass.lean`` and ``RootResetMarkedHandoffPass.lean``
and their carrier-probe dependencies, Cinematic Strawberry, pinned upstream
85a867988442fc423279341200f81634a1e65582.  These are *compiler* functions:
they consume only fixed pattern families and integer continuation states.
The resulting machine retains neither these functions nor term decoders,
runtime addresses, a queue simulation, or a saved invocation cursor.

Nonempty, parity, oldest-live and EMPTY-origin probes use inverse carrier
rows to return to their invocation boundary.  Their restoring guarantees
require the source's carrier boundary; ``compile_scoped`` establishes that
boundary for completed responses.  The two root-started priority passes
may move the cursor when declining, so their caller must reset to root
before trying a later priority pass.
"""
from __future__ import annotations

from typing import TYPE_CHECKING, Iterable

from ..probes import HOLE, LITERAL_S, Pattern
from .patterns import PatternFamily

if TYPE_CHECKING:
    from ..selector_parts.graph import GraphBuilder


def _family(builder: GraphBuilder, family: Iterable[Pattern], yes: int,
            no: int) -> int:
    """Ordered finite pattern disjunction, restoring both exits."""
    entry = no
    for pattern in reversed(tuple(family)):
        entry = builder.match(pattern, yes, entry)
    return entry


def compile_pending_parent(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Test the immediate *registered* pending parent and restore origin.

    The incoming-side guard is essential: matching a pending term elsewhere
    in the ambient tree does not admit a carrier invocation.
    """
    inspect = builder.match(p.pending_pattern(),
                            builder.move("R", yes), builder.move("R", no))
    return builder.incoming_test("R", builder.move("U", inspect), no)


def compile_scoped(builder: GraphBuilder, p: PatternFamily, nonpending: int, pending: int,
                   no: int) -> int:
    """Root/left enter nonpending; only a registered right parent admits."""
    inspect = compile_pending_parent(builder, p, pending, no)
    return builder.incoming_test("R", inspect, nonpending)


def compile_nonempty(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Descend Base/Local/tombstone, read live, then inverse-restore.

    The answer is one finite control bit, represented by two disjoint
    return fragments.  Live rows are deliberately excluded from descent.
    """
    rows = p.nonempty_carrier_rows()
    return_yes = builder.ascent(rows, yes)
    return_no = builder.ascent(rows, no)
    read = _family(builder, p.live_patterns(), return_yes, return_no)
    return builder.descent(rows, read)


def compile_parity(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Restore complete carrier descent, toggling at Local/tombstone nodes.

    The source worker starts with true.  The endpoint at the bottom is not
    classified; each successful inverse edge first moves to its parent,
    whose tag toggles the bit.  Live nodes and Base nodes do not toggle it.
    """
    rows = p.complete_carrier_rows()
    tags = (tuple(p.local_patterns("fresh"))
            + tuple(p.local_patterns("marked"))
            + tuple(p.tombstone_patterns()))
    up_false, up_true = builder.reserve(), builder.reserve()
    read_false = _family(builder, tags, up_true, up_false)
    read_true = _family(builder, tags, up_false, up_true)
    builder.jump(up_false, builder.inverse_rows(rows, read_false, no))
    builder.jump(up_true, builder.inverse_rows(rows, read_true, yes))
    return builder.descent(rows, up_true)


def compile_oldest(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Select first live ancestor after complete descent, or restore/miss."""
    rows = p.complete_carrier_rows()
    ascend = builder.reserve()
    read = _family(builder, p.live_patterns(), yes, ascend)
    builder.jump(ascend, builder.inverse_rows(rows, read, no))
    return builder.descent(rows, ascend)


def compile_empty_origin(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """A tombstone means ordinary chronology; marked/no-hit means EMPTY.

    Descent omits marked Local and tombstone edges.  A no-label result is
    tested only after decoded carrier emptiness by the enclosing worker.
    """
    rows = p.empty_origin_rows()
    return_yes = builder.ascent(rows, yes)
    return_no = builder.ascent(rows, no)
    read = _family(builder, p.tombstone_patterns(), return_no, return_yes)
    return builder.descent(rows, read)


def compile_commit(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """At a completed fresh Local, select its LLL halt-code redex."""
    return builder.rows(tuple((pattern, (0, 0, 0))
                              for pattern in p.local_patterns("fresh")),
                        yes, no)


def compile_handoff(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Select a generic S _ _ _ parent, only from its right child.

    This intentionally uses the source's generic handoff pattern, distinct
    from the ACT-specific registered-parent admission guard.
    """
    generic_pending = (((LITERAL_S, HOLE), HOLE), HOLE)
    return builder.inverse_rows(((generic_pending, (1,)),), yes, no)


def compile_completed(builder: GraphBuilder, p: PatternFamily, pending: bool,
                      yes: int, no: int) -> int:
    """Guarded completed-response worker under an established boundary."""
    commit = compile_commit(builder, p, yes, no)
    if pending:
        oldest_or_commit = compile_oldest(builder, p, yes, commit)
        handoff = compile_handoff(builder, p, yes, no)
        body = compile_parity(builder, p, oldest_or_commit, handoff)
    else:
        # A nonpending response with live content is not continuation-ready.
        body = compile_nonempty(builder, p, no, commit)
    return _family(builder, p.local_patterns("fresh"), body, no)


def compile_empty_aware(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Pending completed response with the empty-origin COMMIT override."""
    ordinary = compile_completed(builder, p, True, yes, no)
    commit = compile_commit(builder, p, yes, no)
    empty = compile_empty_origin(builder, p, commit, ordinary)
    body = compile_nonempty(builder, p, ordinary, empty)
    return _family(builder, p.local_patterns("fresh"), body, no)


def compile_scoped_completed(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Unconditional scoped response query; every decline restores origin."""
    nonpending = compile_completed(builder, p, False, yes, no)
    pending = compile_empty_aware(builder, p, yes, no)
    return compile_scoped(builder, p, nonpending, pending, no)


def compile_local_ancestor(builder: GraphBuilder, p: PatternFamily, status: str,
                           yes: int, no: int) -> int:
    """Find nearest completed Local, including the starting occurrence."""
    if status not in ("fresh", "marked"):
        raise ValueError("Local status must be fresh or marked")
    loop = builder.reserve()
    ascend = builder.incoming_test("root", no, builder.move("U", loop))
    test = _family(builder, p.local_patterns(status), yes, ascend)
    builder.jump(loop, test)
    return loop


def compile_pending_ancestor(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Search upward for nearest registered pending parent and select it."""
    loop = builder.reserve()
    ascend = builder.incoming_test("root", no, builder.move("U", loop))
    test = compile_pending_parent(builder, p, builder.move("U", yes), ascend)
    builder.jump(loop, test)
    return loop


def compile_fresh(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Root-started fresh-response priority pass, with no saved selection."""
    # Imported at compilation to allow the frontend's own fresh-admission
    # test to reuse these carrier queries without an import cycle.
    from .active import compile_frontend

    completed = compile_scoped_completed(builder, p, yes, no)
    ancestor = compile_local_ancestor(builder, p, "fresh", completed, no)
    # Both ordinary and FRAME terminals enter exactly the same search.
    return compile_frontend(builder, p, ancestor, ancestor)


def compile_marked(builder: GraphBuilder, p: PatternFamily, yes: int, no: int) -> int:
    """Root-started marked-Local recovery followed by pending handoff."""
    from .active import compile_frontend

    pending = compile_pending_ancestor(builder, p, yes, no)
    ancestor = compile_local_ancestor(builder, p, "marked", pending, no)
    return compile_frontend(builder, p, ancestor, ancestor)
