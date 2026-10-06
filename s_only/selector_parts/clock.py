"""Compile the finite nested CLOCK probe from the pinned RootReset sources.

Source: cstrawberry/predictive-universe, commit
85a867988442fc423279341200f81634a1e65582, Research/RootResetNestedClockProbe
and its FirstPass, SecondPass, GrowthProbe, CoreProbe, NestedUnaryParity,
NestedUnaryScan and NestedClockPatterns dependencies.  This is an independent
Python transcription of their read-only selection logic, not a Lean proof.

Everything here runs at graph-compilation time.  The parity bit is represented
by two finite controls; no numeral, depth, origin cursor, pattern, or return
stack is retained by the emitted machine.  Stays at component handoffs are
elided, so the source's literal microtick counts are not claimed.
"""
from .patterns import C0, H, S, app


# These are CLOCK wrappers (S field body), not the separate active-context
# pending rows (S field body environment).
PENDING_ROWS = ((app(S, H, H), (1,)),)
SUCCESSOR_ROWS = ((app(S, S, H), (1,)),)
HEAD_PATTERN = app(S, H, H, H)
FIRST_ROWS = ((HEAD_PATTERN, (0, 0, 1)),)


def _up(builder, count, target):
    for _ in range(count):
        target = builder.move("U", target)
    return target


def _compile_unary(builder, initial_bit, finished):
    """Recognize a unary numeral, restore it, and retain its XOR parity.

    ``finished[ready][bit]`` names the four finite continuations.  Each caller
    supplies the exact inverse boundary used in the source: the first pass
    starts at the R child of ``S stage``; the second starts at the R child of
    a saturated redex.  Neither parent is a successor ``S S child``.
    """
    scan = (builder.reserve(), builder.reserve())
    for bit in (0, 1):
        accepted = builder.ascent(SUCCESSOR_ROWS, finished[1][bit])
        rejected = builder.ascent(SUCCESSOR_ROWS, finished[0][bit])
        zero = builder.match(C0, accepted, rejected)
        entry = builder.rows(SUCCESSOR_ROWS, scan[1 - bit], zero)
        builder.jump(scan[bit], entry)
    return scan[int(initial_bit)]


def _compile_core(builder, yes, no):
    """Skip CLOCK wrappers; keep a redex, or undo exactly those wrappers.

    All callers enter at a left child, giving the source's non-right incoming
    boundary.  The inverse wrapper walk consequently cannot escape its entry.
    """
    restore = builder.ascent(PENDING_ROWS, no)
    head = builder.match(HEAD_PATTERN, yes, restore)
    return builder.descent(PENDING_ROWS, head)


def _compile_growth(builder, yes, no):
    # An application contributes one left edge before the bounded core walk.
    core = _compile_core(builder, yes, builder.move("U", no))
    return builder.node_test(no, builder.move("L", core))


def _compile_second(builder, initial_bit, yes, no, growth):
    # On successful parity recognition, restore the numeral, move back to the
    # core endpoint, reverse pending wrappers, then undo the entry left edge.
    # Odd XOR selects the original launch redex; even XOR tries growth.
    final = ((no, no), (growth, yes))
    finished = tuple(
        tuple(builder.move("U", builder.ascent(
            PENDING_ROWS, builder.move("U", final[ready][bit])))
              for bit in (0, 1))
        for ready in (0, 1)
    )
    unary = _compile_unary(builder, initial_bit, finished)
    core = _compile_core(builder, builder.move("R", unary),
                         builder.move("U", no))
    return builder.node_test(no, builder.move("L", core))


def compile_clock(builder, yes, no):
    """Return the nested CLOCK entry control, preserving every miss cursor.

    A saturated root head triggers two restoring numeral-parity passes.  A
    malformed numeral rejects immediately, rather than falling through to
    growth.  A head miss, or two accepted numerals of equal parity, tries the
    growth occurrence.  Opposite parity selects the original launch redex.
    Both exits compose with caller-supplied finite controls.
    """
    growth = _compile_growth(builder, yes, no)
    second = tuple(_compile_second(builder, bit, yes, no, growth)
                   for bit in (0, 1))
    finished = (
        (_up(builder, 3, no), _up(builder, 3, no)),
        (_up(builder, 3, second[0]), _up(builder, 3, second[1])),
    )
    unary = _compile_unary(builder, 0, finished)
    return builder.rows(FIRST_ROWS, unary, growth)
