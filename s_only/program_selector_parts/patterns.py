"""Immutable compile-time row families for any fixed two-phase CTS program.

The input-independent definitions transcribe the pinned completed-Local,
carrier, fuel, dispatcher and selected-appender rows. Every wildcard is
independent. No source-machine step or input term is used to build a family.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from ..cts import Program
from .. import encoding
from ..probes import HOLE as H, LITERAL_S as S, Pattern
from ..terms import App, Term


def app(*patterns):
    out = patterns[0]
    for pattern in patterns[1:]:
        out = (out, pattern)
    return out


def literal(term):
    """Expand fixed code into a pattern; this never receives an input tree."""
    # Static code can have long appender spines. Preserve sharing by identity
    # while expanding bottom-up, without Python recursion or recursive hashes.
    expanded = {}
    pending = [(term, False)]
    while pending:
        node, visited = pending.pop()
        key = id(node)
        if key in expanded:
            continue
        if not isinstance(node, App):
            expanded[key] = S
        elif visited:
            expanded[key] = expanded[id(node.left)], expanded[id(node.right)]
        else:
            pending.extend(((node, True), (node.right, False), (node.left, False)))
    return expanded[id(term)]


B = literal(encoding.B)
C0 = literal(encoding.C0)
PI = literal(encoding.PI)
HALT = literal(encoding.HALT)
HALT_TAG = literal(App(encoding.B, encoding.S))
VALUES = tuple(map(literal, encoding.VALUES))
LIVE = tuple(map(literal, encoding.LIVE))
SHELL_ADDRESS = (0, 0, 1)


def chosen_pattern(response):
    return app(S, H, response)


def call_pattern(code):
    return literal(code), H


def action_pattern(count):
    return history_pattern((PI, H), count)


def history_pattern(base, count):
    for _ in range(count):
        base = base, H
    return base


def route_response_address(route):
    return tuple(direction for side in route for direction in (1, side)) + (1,)


@dataclass(frozen=True, slots=True)
class Dispatch:
    code: Term
    left: Dispatch | None = None
    right: Dispatch | None = None
    label: tuple[int, int] | None = None


def _dispatch(compiled):
    leaves = tuple(Dispatch(App(encoding.B, action), label=divmod(i, 2))
                   for i, action in enumerate(compiled.action_terms))

    def branch(left, right):
        fork = App(App(encoding.S, left.code), right.code)
        return Dispatch(App(encoding.B, fork), left, right)

    return branch(branch(*leaves[:2]), branch(*leaves[2:]))


@dataclass(frozen=True, slots=True)
class PatternFamily:
    """Static program parameter, discarded when the primitive table is built."""
    program: Program
    compiled: encoding.CompiledProgram = field(init=False)
    dispatch: Dispatch = field(init=False)
    act: Pattern = field(init=False)

    def __post_init__(self):
        if not isinstance(self.program, Program):
            raise TypeError('program must be s_only.cts.Program')
        if len(self.program.appendants) != 2:
            raise ValueError('this compiler supports exactly two CTS phases')
        compiled = encoding.compile_program(self.program)
        object.__setattr__(self, 'compiled', compiled)
        object.__setattr__(self, 'dispatch', _dispatch(compiled))
        object.__setattr__(self, 'act', literal(compiled.act))

    def environment_pattern(self):
        return app(S, app(S, self.act, (S, H)))

    def pending_pattern(self, child=H):
        return app(self.environment_pattern(), H, child)

    def base_pattern(self):
        e = self.environment_pattern()
        return app(H, app(e, (B, e), H), H)

    def base_row(self):
        return self.base_pattern(), (0, 1, 0, 0, 1, 1, 1)

    def local_pattern(self, status, dispatch=H):
        if status == 'fresh':
            halt = HALT, H
        elif status == 'marked':
            halt = app(S, H, (HALT_TAG, H))
        else:
            raise ValueError('Local status must be fresh or marked')
        return app(halt, dispatch, app(S, H, H), (H, H))

    def emitted(self, label):
        phase, bit = label
        return self.program.appendants[phase] if bit else ''

    def history_count(self, label):
        return len(self.emitted(label))

    def dispatch_records(self):
        """Completed route pattern, route, label, in phase-major row order."""
        def visit(spec):
            if spec.label is not None:
                return ((chosen_pattern(action_pattern(self.history_count(spec.label))),
                         (), spec.label),)
            left, right = spec.left, spec.right
            left_rows = tuple((chosen_pattern((p, call_pattern(right.code))), (0,) + r, label)
                              for p, r, label in visit(left))
            right_rows = tuple((chosen_pattern((call_pattern(left.code), p)), (1,) + r, label)
                               for p, r, label in visit(right))
            return left_rows + right_rows
        return visit(self.dispatch)

    def local_patterns(self, status):
        return tuple(self.local_pattern(status, pattern)
                     for pattern, _, _ in self.dispatch_records())

    def local_rows(self, status):
        return tuple((self.local_pattern(status, pattern), SHELL_ADDRESS +
                      route_response_address(route) + (0,) * self.history_count(label) + (1,))
                     for pattern, route, label in self.dispatch_records())

    def live_patterns(self):
        return tuple((code, H) for code in LIVE)

    def live_rows(self):
        return tuple((pattern, (1,)) for pattern in self.live_patterns())

    def tombstone_patterns(self):
        return tuple(app(S, H, (value, H)) for value in VALUES)

    def tombstone_rows(self):
        return tuple((pattern, (0, 1)) for pattern in self.tombstone_patterns())

    def nonempty_carrier_rows(self):
        return ((self.base_row(),) + self.local_rows('fresh') +
                self.local_rows('marked') + self.tombstone_rows())

    def complete_carrier_rows(self):
        return self.nonempty_carrier_rows() + self.live_rows()

    def empty_origin_rows(self):
        return (self.base_row(),) + self.local_rows('fresh') + self.live_rows()

    def deleted_bit_rows(self):
        return ((self.base_row(),) + self.local_rows('fresh') +
                self.local_rows('marked') + self.live_rows())

    def cell_rows(self):
        return self.live_rows() + self.tombstone_rows()

    def frame_pending_rows(self):
        return ((app(S, H, H, H), (1,)),)

    def frame_head_rows(self):
        first = app(S, app(S, HALT, H), H, H, H)
        second = app(S, HALT, H, H, H, H)
        return ((first, (0,)), (second, (0, 0)))

    def fuel_rows(self):
        e = self.environment_pattern()
        return (
            ('call_zero', app(C0, e, H), (0,)),
            ('call_positive', app(B, H, e, H), (0,)),
            ('positive_half', app(S, e, (H, e), H), ()),
            ('zero_first', app(B, e, (B, e), H), (0,)),
            ('zero_second', app(S, (B, e), (e, (B, e)), H), ()),
            ('zero_third', app(B, e, H, app(e, (B, e), H)), (0,)),
            ('zero_fourth', app(S, H, (e, H), H), ()),
        )

    def pending_admission_rows(self):
        children = ((self.pending_pattern(), self.local_pattern('fresh')) +
                    tuple(pattern for pattern, _ in self.frame_head_rows()) +
                    tuple(pattern for _, pattern, _ in self.fuel_rows()) +
                    self.local_patterns('marked') + self.local_patterns('fresh'))
        return tuple((self.pending_pattern(child), (1,)) for child in children)

    def phase_labels(self):
        return ((0, self.base_pattern()),) + tuple(
            ((label[0] + 1) % 2, self.local_pattern(status, pattern))
            for status in ('fresh', 'marked')
            for pattern, _, label in self.dispatch_records())

    def dispatcher_rows(self, label):
        """Initial call and fixed exposed/forked rows for the recovered label."""
        def visit(spec, remaining):
            if spec.label is not None or not remaining:
                return ()
            side, rest = remaining[0], remaining[1:]
            left, right = spec.left, spec.right
            fork = App(App(encoding.S, left.code), right.code)
            head = ((chosen_pattern(call_pattern(fork)), (1,)),
                    (chosen_pattern((call_pattern(left.code), call_pattern(right.code))),
                     (1, side)))
            if side == 0:
                nested = tuple((chosen_pattern((p, call_pattern(right.code))), (1, 0) + a)
                               for p, a in visit(left, rest))
            else:
                nested = tuple((chosen_pattern((call_pattern(left.code), p)), (1, 1) + a)
                               for p, a in visit(right, rest))
            return head + nested
        rows = ((call_pattern(self.compiled.actions), ()),) + visit(self.dispatch, label)
        return tuple((self.local_pattern('fresh', pattern), SHELL_ADDRESS + address)
                     for pattern, address in rows)

    def route_pattern(self, route, response):
        def visit(spec, remaining):
            if spec.label is not None:
                return chosen_pattern(response)
            side, rest = remaining[0], remaining[1:]
            if side == 0:
                return chosen_pattern((visit(spec.left, rest), call_pattern(spec.right.code)))
            return chosen_pattern((call_pattern(spec.left.code), visit(spec.right, rest)))
        return visit(self.dispatch, route)

    def appender_rows(self, word):
        """Exact specsFrom 0 word: first Push, next-call, then deeper history."""
        rows = []
        for count, bit in enumerate(word):
            rest = word[count + 1:]
            first = app(S, literal(encoding.append_routine(rest)), H, (LIVE[int(bit)], H))
            rows.append((history_pattern(first, count), (0,) * count))
            if rest:
                second = app(literal(encoding.append_routine(rest)), H, H)
                rows.append((history_pattern(second, count), (0,) * (count + 1)))
        return tuple(rows)

    def selected_action_rows(self):
        """Initial nonempty actions, followed by every live Push-stage row."""
        initial, stages = [], []
        for _, route, label in self.dispatch_records():
            emitted = self.emitted(label)
            if not emitted:
                continue
            address = SHELL_ADDRESS + route_response_address(route)
            action = self.compiled.action_terms[2 * label[0] + label[1]]
            initial.append((self.local_pattern('fresh', self.route_pattern(route, call_pattern(action))),
                            address))
            stages.extend((self.local_pattern('fresh', self.route_pattern(route, pattern)),
                           address + relative)
                          for pattern, relative in self.appender_rows(emitted))
        return tuple(initial + stages)
