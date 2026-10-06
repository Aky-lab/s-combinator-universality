"""Executable reading of the two-phase fixture in Pure S, Sections 3–4 and E.

Construction and grammar: Cinematic Strawberry, pinned upstream 85a8679884.
This module is an independently written, fixed-fixture implementation of the
mathematical constructors and checkpoint grammar. It does not select rewrites.
See docs/queue-replication.md for scope, provenance and attribution.
"""
from dataclasses import dataclass

from .terms import App, S, Term


def apply(*terms: Term) -> Term:
    if not terms:
        raise ValueError("application needs a head")
    out = terms[0]
    for child in terms[1:]:
        out = App(out, child)
    return out


B = apply(S, S)
C0 = apply(S, B, B)
PI = apply(S, B)
VALUES = (apply(S, C0), apply(S, apply(S, C0)))
LIVE = tuple(apply(B, value) for value in VALUES)
HALT_TAG = apply(B, S)
HALT = apply(B, HALT_TAG)
APPENDANTS = ((1,), ())


def _leaf(action):
    return apply(B, action)


def _branch(left, right):
    return apply(B, apply(S, left, right))


# The four phase-major leaves are (0,0), (0,1), (1,0), (1,1).
EMPTY_ACTION = _leaf(PI)
ONE_ACTION = _leaf(apply(S, apply(S, PI), LIVE[1]))
LEFT_BRANCH = _branch(EMPTY_ACTION, ONE_ACTION)
RIGHT_BRANCH = _branch(EMPTY_ACTION, EMPTY_ACTION)
ACTIONS = _branch(LEFT_BRANCH, RIGHT_BRANCH)
ACT = apply(S, HALT, ACTIONS)


def encode_word(bits) -> Term:
    out = S
    for bit in bits:
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("word must contain Boolean integers")
        out = apply(LIVE[bit], out)
    return out


def encode(bits=(1, 0, 1)) -> Term:
    seed = apply(S, encode_word(bits))
    environment = apply(S, apply(S, ACT, seed))
    return apply(C0, C0, environment)


class _Miss(ValueError):
    pass


def _pair(term):
    if not isinstance(term, App):
        raise _Miss("application required")
    return term.left, term.right


def _spine(term):
    arguments = []
    while isinstance(term, App):
        arguments.append(term.right)
        term = term.left
    return tuple(reversed(arguments))


def _arity(term, count):
    arguments = _spine(term)
    if len(arguments) != count:
        raise _Miss("wrong head arity")
    return arguments


def _numeral(term):
    count = 0
    while term != C0:
        function, term = _pair(term)
        if function != B:
            raise _Miss("wrong clock numeral")
        count += 1
    return count


def _environment(term):
    (body,) = _arity(term, 1)
    action, seed = _arity(body, 2)
    if action != ACT:
        raise _Miss("wrong fixture action table")
    (word,) = _arity(seed, 1)
    return word


def _cell(term):
    """Return (label, consumed, canonical predecessor), ignoring audit copies."""
    function, payload = _pair(term)
    for label in (0, 1):
        if function == LIVE[label]:
            return label, False, payload
    predecessor, tagged_audit = _arity(term, 2)
    tag, _audit = _pair(tagged_audit)
    for label in (0, 1):
        if tag == VALUES[label]:
            return label, True, predecessor
    raise _Miss("unrecognized queue cell")


def _word(term, literal=False):
    reversed_bits = []
    while term != S:
        bit, consumed, term = _cell(term)
        if consumed and literal:
            raise _Miss("initial word contains a consumed cell")
        if not consumed:
            reversed_bits.append(bit)
    return tuple(reversed(reversed_bits))


def _base_word(term):
    left, _retained = _pair(term)
    continuation, alpha = _pair(left)
    applied_environment, same_continuation = _pair(alpha)
    active_environment, dormant = _pair(applied_environment)
    b, dormant_environment = _pair(dormant)
    if continuation != same_continuation or b != B:
        raise _Miss("wrong base frame")
    _environment(dormant_environment)
    return _word(_environment(active_environment))


# Each entry is (compiled term, left child, right child, leaf label).
LEAF00 = (EMPTY_ACTION, None, None, (0, 0))
LEAF01 = (ONE_ACTION, None, None, (0, 1))
LEAF10 = (EMPTY_ACTION, None, None, (1, 0))
LEAF11 = (EMPTY_ACTION, None, None, (1, 1))
DISPATCH = (ACTIONS, (LEFT_BRANCH, LEAF00, LEAF01, None),
            (RIGHT_BRANCH, LEAF10, LEAF11, None), None)


def _dormant(term, compiled):
    function, _accumulator_copy = _pair(term)
    if function != compiled:
        raise _Miss("wrong dormant dispatcher branch")


def _route(term, specification=DISPATCH):
    _audit, branch = _arity(term, 2)
    _compiled, left_spec, right_spec, label = specification
    if label is not None:
        return label, branch
    left, right = _pair(branch)
    if len(_spine(left)) == 2:
        _dormant(right, right_spec[0])
        return _route(left, left_spec)
    _dormant(left, left_spec[0])
    return _route(right, right_spec)


@dataclass(frozen=True)
class _Local:
    marked: bool
    phase: int
    accumulator: Term
    continuation: Term


def _local(term):
    previous, continuation_audit = _pair(term)
    earlier, seed_audit = _pair(previous)
    halt, route = _pair(earlier)
    halt_function, halt_argument = _pair(halt)
    if halt_function == HALT:
        marked = False
    else:
        _left_audit, tagged_right_audit = _arity(halt, 2)
        tag, _right_audit = _pair(tagged_right_audit)
        if tag != HALT_TAG:
            raise _Miss("wrong halt field")
        marked = True
    _arity(seed_audit, 2)
    continuation, _ = _pair(continuation_audit)
    (phase, front_bit), action = _route(route)
    emitted = APPENDANTS[phase] if front_bit else ()
    _arity(action, len(emitted) + 2)
    completed = action
    for _ in emitted:
        completed, _audit = _pair(completed)
    head, accumulator = _pair(completed)
    if head != PI:
        raise _Miss("unfinished append action")
    predecessor = accumulator
    for expected in reversed(emitted):
        label, _consumed, predecessor = _cell(predecessor)
        if label != expected:
            raise _Miss("wrong appended cell label")
    return _Local(marked, phase, accumulator, continuation)


def _queue(term):
    reversed_bits = []
    while True:
        try:
            return _base_word(term) + tuple(reversed(reversed_bits))
        except _Miss:
            pass
        try:
            term = _local(term).accumulator
            continue
        except _Miss:
            pass
        label, consumed, term = _cell(term)
        if not consumed:
            reversed_bits.append(label)


def decode(term):
    """Read this fixture's structural checkpoints from the current bare tree.

    No source transition, cursor, prior sample or expected queue is consulted.
    The source comparison belongs to the experiment runner, outside this parser.
    """
    try:
        clock, environment = _pair(term)
        left, right = _pair(clock)
        if _numeral(left) == _numeral(right) == 0:
            word = _word(_environment(environment), literal=True)
            return {"horizon": 0, "phase": 0, "data": "".join(map(str, word))}
    except _Miss:
        pass
    try:
        current = term
        last = None
        while True:
            try:
                local = _local(current)
            except _Miss:
                break
            last, current = local, local.continuation
        if last is None:
            return None
        clock, environment = _pair(current)
        left, right = _pair(clock)
        k = _numeral(left)
        if k < 2 or _numeral(right) != k:
            return None
        _environment(environment)
        word = _queue(last.accumulator)
        horizon = k - 1
        if last.phase != (horizon - 1) % 2 or last.marked != (len(word) == 0):
            return None
        return {"horizon": horizon, "phase": horizon % 2, "data": "".join(map(str, word))}
    except _Miss:
        return None


def source_config(horizon):
    if type(horizon) is not int or horizon < 0:
        raise ValueError("horizon must be a nonnegative integer")
    word, phase = (1, 0, 1), 0
    for _ in range(horizon):
        if word:
            word = word[1:] + (APPENDANTS[phase] if word[0] else ())
        phase = (phase + 1) % len(APPENDANTS)
    return {"horizon": horizon, "phase": phase, "data": "".join(map(str, word))}
