"""Compile the pinned active-context frontend and endpoint priority pass.

These are graph constructors, never runtime term queries.  The resulting
machine carries only a finite state and an occurrence cursor.  Each apparent
loop below is emitted as finite feedback controls, not Python recursion over
input syntax.  Source: RootResetActiveEndpointProbe and its named dependencies,
upstream commit 85a867988442fc423279341200f81634a1e65582.
"""
from .patterns import PatternFamily


def _family(builder, patterns, yes, no):
    return builder.rows(tuple((pattern, ()) for pattern in patterns), yes, no)


def compile_frame(builder, p: PatternFamily, yes, no):
    """FRAME: pending-R descent, bounded head rows, exact inverse on miss."""
    restore = builder.ascent(p.frame_pending_rows(), no)
    heads = builder.rows(p.frame_head_rows(), yes, restore)
    return builder.descent(p.frame_pending_rows(), heads)


def compile_frontend(builder, p: PatternFamily, yes, no):
    """Marked bypass and FRAME/pending/completed-Local active descent.

    FRAME is checked only at root and after a Local RL entry. Pending R
    entries retain the segment boundary; they do not rerun FRAME. A miss
    yields the active endpoint, which may differ from the invocation cursor.
    """
    from .priority import compile_nonempty
    restart = builder.reserve()
    segment = builder.reserve()
    enter_local = builder.path((1, 0), restart)
    fresh_nonempty = compile_nonempty(builder, p, enter_local, no)
    fresh = _family(builder, p.local_patterns("fresh"), fresh_nonempty, no)
    mixed = _family(builder, p.local_patterns("marked"), enter_local, fresh)
    pending = builder.rows(p.pending_admission_rows(), segment, mixed)
    builder.jump(segment, pending)
    frame = compile_frame(builder, p, yes, segment)
    marked = _family(builder, p.local_patterns("marked"), enter_local, frame)
    builder.jump(restart, marked)
    return restart


def compile_base(builder, p: PatternFamily, yes, no):
    """Scoped Base: even chronology selects oldest live, else handoff."""
    from .priority import compile_scoped, compile_parity, compile_oldest, compile_handoff
    handoff = compile_handoff(builder, p, yes, no)
    oldest = compile_oldest(builder, p, yes, handoff)
    # The shared source query starts at true: true is the even branch.
    parity = compile_parity(builder, p, oldest, handoff)
    base = builder.match(p.base_pattern(), parity, no)
    return compile_scoped(builder, p, base, base, no)


def compile_pending_base(builder, p: PatternFamily, yes, no):
    failed_child = builder.move("U", no)
    base = compile_base(builder, p, yes, failed_child)
    enter = builder.move("R", base)
    return builder.match(p.pending_pattern(p.base_pattern()), enter, no)


def _labelled_query(builder, edges, labels, targets, absent):
    """Static labelled read bracketed by descent and exact inverse ascent."""
    targets = {label: builder.ascent(edges, target) for label, target in targets.items()}
    entry = builder.ascent(edges, absent)
    for label, pattern in reversed(labels):
        entry = builder.match(pattern, targets[label], entry)
    return builder.descent(edges, entry)


def _compile_front_bit(builder, p: PatternFamily, on_zero, on_one):
    query = _labelled_query(builder, p.deleted_bit_rows(),
                           tuple(enumerate(p.tombstone_patterns())),
                           {0: on_zero, 1: on_one}, on_zero)
    return _family(builder, p.local_patterns("marked"), on_zero, query)


def _ups(builder, count, target):
    for _ in range(count):
        target = builder.move("U", target)
    return target


def compile_dispatcher(builder, p: PatternFamily, yes, no):
    """Recover phase and deleted front bit, restore LLLR, select route row."""
    absent = _ups(builder, 4, no)
    targets = {}
    for phase in range(len(p.program.appendants)):
        returns = tuple(_ups(builder, 4,
                            builder.rows(p.dispatcher_rows((phase, bit)), yes, no))
                        for bit in (0, 1))
        targets[phase] = _compile_front_bit(builder, p, *returns)
    phase = _labelled_query(builder, p.cell_rows(), p.phase_labels(), targets, absent)
    return builder.rows(((p.local_pattern("fresh"), (0, 0, 0, 1)),), phase, no)


def compile_endpoint(builder, p: PatternFamily, yes, no):
    from .clock import compile_clock
    clock = compile_clock(builder, yes, no)
    fuel = builder.rows(tuple((pattern, address) for _, pattern, address in p.fuel_rows()), yes, clock)
    action = builder.rows(p.selected_action_rows(), yes, fuel)
    dispatcher = compile_dispatcher(builder, p, yes, action)
    pending_base = compile_pending_base(builder, p, yes, dispatcher)
    return compile_base(builder, p, yes, pending_base)


def compile_active(builder, p: PatternFamily, yes, no):
    """RootResetActiveEndpointProbe.worker for the fixed positive-period program."""
    endpoint = compile_endpoint(builder, p, yes, no)
    return compile_frontend(builder, p, yes, endpoint)
