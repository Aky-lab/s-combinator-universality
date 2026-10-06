"""Static finite patterns for the pinned two-phase RootReset construction.

All functions in this module run during table compilation, before any input
term is supplied.  Wildcards are independent, including duplicated-looking
environment, accumulator, continuation, and audit fields.  The row order and
addresses transcribe the 85a867988442fc423279341200f81634a1e65582 Lean sources.
"""
from ..probes import HOLE as H, LITERAL_S as S
from ..terms import App
from .. import queue_fixture as fixture


def app(*patterns):
    """Compile-time left-associated pattern application."""
    out = patterns[0]
    for pattern in patterns[1:]:
        out = (out, pattern)
    return out


def literal(term):
    """Expand fixed program code only, never an input term."""
    if isinstance(term, App):
        return (literal(term.left), literal(term.right))
    return S


B = literal(fixture.B)
C0 = literal(fixture.C0)
PI = literal(fixture.PI)
ACT = literal(fixture.ACT)
HALT = literal(fixture.HALT)
HALT_TAG = literal(fixture.HALT_TAG)
VALUES = tuple(literal(term) for term in fixture.VALUES)
LIVE = tuple(literal(term) for term in fixture.LIVE)
SHELL_ADDRESS = (0, 0, 1)


def environment_pattern():
    return app(S, app(S, ACT, (S, H)))


def pending_pattern(child=H):
    return app(environment_pattern(), H, child)


def generic_pending_pattern():
    return app(S, H, H, H)


def base_pattern():
    e = environment_pattern()
    return app(H, app(e, (B, e), H), H)


def base_row():
    return base_pattern(), (0, 1, 0, 0, 1, 1, 1)


def chosen_pattern(response):
    return app(S, H, response)


def call_pattern(code):
    return (literal(code), H)


def action_pattern(count):
    out = (PI, H)
    for _ in range(count):
        out = (out, H)
    return out


def local_pattern(status, dispatch=H):
    if status == "fresh":
        halt = (HALT, H)
    elif status == "marked":
        halt = app(S, H, (HALT_TAG, H))
    else:
        raise ValueError("Local status must be fresh or marked")
    return app(halt, dispatch, app(S, H, H), (H, H))


def history_count(label):
    phase, bit = label
    return len(fixture.APPENDANTS[phase]) if bit else 0


def route_response_address(route):
    return tuple(direction for side in route for direction in (1, side)) + (1,)


def dispatch_records():
    """(completed route pattern, route, label), in phase-major row order."""
    def visit(specification):
        _, left, right, label = specification
        if label is not None:
            return ((chosen_pattern(action_pattern(history_count(label))), (), label),)
        left_rows = tuple((chosen_pattern((p, call_pattern(right[0]))), (0,) + r, label)
                          for p, r, label in visit(left))
        right_rows = tuple((chosen_pattern((call_pattern(left[0]), p)), (1,) + r, label)
                           for p, r, label in visit(right))
        return left_rows + right_rows
    return visit(fixture.DISPATCH)


def local_patterns(status):
    return tuple(local_pattern(status, pattern) for pattern, _, _ in dispatch_records())


def local_rows(status):
    return tuple((local_pattern(status, pattern), SHELL_ADDRESS +
                  route_response_address(route) + (0,) * history_count(label) + (1,))
                 for pattern, route, label in dispatch_records())


def live_patterns():
    return tuple((code, H) for code in LIVE)


def live_rows():
    return tuple((pattern, (1,)) for pattern in live_patterns())


def tombstone_patterns():
    return tuple(app(S, H, (value, H)) for value in VALUES)


def tombstone_rows():
    return tuple((pattern, (0, 1)) for pattern in tombstone_patterns())


def nonempty_carrier_rows():
    return (base_row(),) + local_rows("fresh") + local_rows("marked") + tombstone_rows()


def complete_carrier_rows():
    return nonempty_carrier_rows() + live_rows()


def empty_origin_rows():
    return (base_row(),) + local_rows("fresh") + live_rows()


def deleted_bit_rows():
    return (base_row(),) + local_rows("fresh") + local_rows("marked") + live_rows()


def cell_rows():
    return live_rows() + tombstone_rows()


def frame_pending_rows():
    return ((generic_pending_pattern(), (1,)),)


def frame_head_rows():
    first = app(S, app(S, HALT, H), H, H, H)
    second = app(S, HALT, H, H, H, H)
    return ((first, (0,)), (second, (0, 0)))


def pending_admission_rows():
    from ..fuel_probe import fuel_rows
    children = ((pending_pattern(), local_pattern("fresh")) +
                tuple(pattern for pattern, _ in frame_head_rows()) +
                tuple(pattern for _, pattern, _ in fuel_rows()) +
                local_patterns("marked") + local_patterns("fresh"))
    return tuple((pending_pattern(child), (1,)) for child in children)


def phase_labels():
    return ((0, base_pattern()),) + tuple(
        ((label[0] + 1) % len(fixture.APPENDANTS), local_pattern(status, pattern))
        for status in ("fresh", "marked")
        for pattern, _, label in dispatch_records())


def dispatcher_rows(label):
    """Exact Local rows for the fixed phase-major route of ``label``.

    RootResetDispatcherStageRows: initial call, exposed fork, forked
    selected child, then the same two rows under each chosen branch.
    """
    route = label

    def route_rows(specification, remaining):
        _, left, right, leaf_label = specification
        if leaf_label is not None or not remaining:
            return ()
        side, rest = remaining[0], remaining[1:]
        fork = fixture.apply(fixture.S, left[0], right[0])
        head = ((chosen_pattern(call_pattern(fork)), (1,)),
                (chosen_pattern((call_pattern(left[0]), call_pattern(right[0]))),
                 (1, side)))
        child = left if side == 0 else right
        if side == 0:
            nested = tuple((chosen_pattern((p, call_pattern(right[0]))), (1, 0) + a)
                           for p, a in route_rows(child, rest))
        else:
            nested = tuple((chosen_pattern((call_pattern(left[0]), p)), (1, 1) + a)
                           for p, a in route_rows(child, rest))
        return head + nested

    rows = ((call_pattern(fixture.ACTIONS), ()),) + route_rows(fixture.DISPATCH, route)
    return tuple((local_pattern("fresh", pattern), SHELL_ADDRESS + address)
                 for pattern, address in rows)


def _route_pattern(route, response):
    """Wrap a fixed action-response pattern in the chosen dispatcher route."""
    def visit(specification, remaining):
        _, left, right, leaf_label = specification
        if leaf_label is not None:
            return chosen_pattern(response)
        side, rest = remaining[0], remaining[1:]
        if side == 0:
            return chosen_pattern((visit(left, rest), call_pattern(right[0])))
        return chosen_pattern((call_pattern(left[0]), visit(right, rest)))
    return visit(fixture.DISPATCH, route)


def selected_action_rows():
    """The fixture has one nonempty action: phase 0/front 1 emits bit 1."""
    route = (0, 1)
    address = SHELL_ADDRESS + route_response_address(route)
    selected = fixture.apply(fixture.S, fixture.apply(fixture.S, fixture.PI), fixture.LIVE[1])
    initial = _route_pattern(route, call_pattern(selected))
    push = _route_pattern(route, app(S, PI, H, (LIVE[1], H)))
    return ((local_pattern("fresh", initial), address),
            (local_pattern("fresh", push), address))
