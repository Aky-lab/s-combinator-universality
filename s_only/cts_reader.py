"""Program-static, history-free structural readers for binary CTS checkpoints.

The current bare S term is the only run-time input.  This is an independent
implementation of the public grammar in the pinned Pure S paper, Sections
4.2--4.3.  The repeated Base continuation is checked structurally; audit
fields remain independent.  See docs/cts-reader.md for the relationship to
the pinned Lean parser.  Acceptance is syntax, not a reachability certificate.
"""
from __future__ import annotations

from dataclasses import dataclass

from .cts import Program
from .encoding import B, C0, HALT, LIVE, PI, VALUES, compile_program
from .terms import App, S, Term


HALT_TAG = App(B, S)
_ATOM_TYPE = type(S)


class _Miss(ValueError):
    """A required public constructor is absent."""


def _atom(term: Term) -> bool:
    return isinstance(term, _ATOM_TYPE)


def _pair(term: Term) -> tuple[Term, Term]:
    if not isinstance(term, App):
        raise _Miss("application required")
    return term.left, term.right


def _same(term: Term, expected_tree: Term) -> bool:
    """Iterative equality for fixed code or the repeated Base continuation.

    Pair identities memoize shared syntax, without recursive Term equality,
    recursive Term hashing, serialization, or digest comparisons.
    """
    pending = [(term, expected_tree)]
    checked: set[tuple[int, int]] = set()
    while pending:
        actual, expected = pending.pop()
        if actual is expected:
            continue
        if isinstance(expected, App):
            if not isinstance(actual, App):
                return False
            pair = (id(actual), id(expected))
            if pair not in checked:
                checked.add(pair)
                # Check the fixed left spine before right arguments. A failed
                # alternative (e.g. fresh vs. marked halt) must reject on its
                # public prefix before it can enter the other form's audit.
                pending.extend(((actual.right, expected.right),
                                (actual.left, expected.left)))
        elif not _atom(expected) or not _atom(actual):
            return False
    return True


def _arity(term: Term, count: int) -> tuple[Term, ...]:
    """Unpack exactly count arguments headed by S; do not enter arguments."""
    arguments = []
    for _ in range(count):
        term, child = _pair(term)
        arguments.append(child)
    if not _atom(term):
        raise _Miss("wrong S head arity")
    arguments.reverse()
    return tuple(arguments)


def _has_arity(term: Term, count: int) -> bool:
    try:
        _arity(term, count)
        return True
    except _Miss:
        return False


def _numeral(term: Term) -> int:
    count = 0
    while not _same(term, C0):
        function, term = _pair(term)
        if not _same(function, B):
            raise _Miss("wrong carrier numeral")
        count += 1
    return count


def _cell(term: Term) -> tuple[str, bool, Term]:
    """Return label, consumed flag and strict canonical predecessor child."""
    function, payload = _pair(term)
    for bit in (0, 1):
        if _same(function, LIVE[bit]):
            return str(bit), False, payload
    predecessor, tagged_audit = _arity(term, 2)
    tag, _audit = _pair(tagged_audit)
    for bit in (0, 1):
        if _same(tag, VALUES[bit]):
            return str(bit), True, predecessor
    raise _Miss("unrecognized queue cell")


def _word(term: Term, *, literal: bool = False) -> str:
    reversed_bits = []
    while not _atom(term):
        bit, consumed, term = _cell(term)
        if consumed and literal:
            raise _Miss("initial word contains a tombstone")
        if not consumed:
            reversed_bits.append(bit)
    return "".join(reversed(reversed_bits))


@dataclass(frozen=True, slots=True, eq=False)
class _Dispatch:
    code: Term
    left: _Dispatch | None = None
    right: _Dispatch | None = None
    label: tuple[int, int] | None = None


@dataclass(frozen=True, slots=True, eq=False)
class _Local:
    marked: bool
    phase: int
    accumulator: Term
    continuation: Term


@dataclass(frozen=True, slots=True, eq=False)
class CompiledReader:
    """Reusable static grammar.  No seed, source state, cursor or sample cache.

    Construct with compile_reader(program), then call decode(term) in any order.
    The result uses the same horizon/phase/data keys as the original fixture.
    """

    program: Program
    actions: Term
    act: Term
    _dispatch: _Dispatch

    def _environment(self, term: Term) -> Term:
        (body,) = _arity(term, 1)
        action, seed = _arity(body, 2)
        if not _same(action, self.act):
            raise _Miss("wrong compiled action table")
        (payload,) = _arity(seed, 1)
        return payload

    def _base_queue(self, term: Term) -> Term:
        left, _retained = _pair(term)
        outer_continuation, alpha = _pair(left)
        applied_environment, inner_continuation = _pair(alpha)
        active_environment, dormant = _pair(applied_environment)
        # Reject alternative carrier forms on their fixed environment prefix
        # first. In a Local, this candidate dormant field is its opaque seed.
        queue = self._environment(active_environment)
        found_b, dormant_environment = _pair(dormant)
        if not _same(found_b, B):
            raise _Miss("wrong Base prefix")
        if not _same(outer_continuation, inner_continuation):
            raise _Miss("unequal Base continuations")
        # The two B occurrences in (B ((E_Q (b E_seed)) B)) beta agree.
        # Dormant seed payload and retained beta remain opaque and independent.
        self._environment(dormant_environment)
        return queue

    def _route(self, term: Term) -> tuple[tuple[int, int], Term]:
        specification = self._dispatch
        while True:
            _audit, branch = _arity(term, 2)
            if specification.label is not None:
                return specification.label, branch
            left_spec, right_spec = specification.left, specification.right
            assert left_spec is not None and right_spec is not None
            left, right = _pair(branch)
            if _has_arity(left, 2):
                dormant_code, _dormant_audit = _pair(right)
                if not _same(dormant_code, right_spec.code):
                    raise _Miss("wrong dormant right branch")
                term, specification = left, left_spec
            else:
                dormant_code, _dormant_audit = _pair(left)
                if not _same(dormant_code, left_spec.code):
                    raise _Miss("wrong dormant left branch")
                term, specification = right, right_spec

    def _local(self, term: Term) -> _Local:
        previous, continuation_audit = _pair(term)
        earlier, seed_audit = _pair(previous)
        halt, route = _pair(earlier)
        halt_function, _halt_audit = _pair(halt)
        if _same(halt_function, HALT):
            marked = False
        else:
            _left_audit, tagged_right_audit = _arity(halt, 2)
            tag, _right_audit = _pair(tagged_right_audit)
            if not _same(tag, HALT_TAG):
                raise _Miss("wrong halt field")
            marked = True
        _arity(seed_audit, 2)
        continuation, _continuation_audit = _pair(continuation_audit)
        (phase, bit), completed = self._route(route)
        history_count = len(self.program.appendants[phase]) if bit else 0
        for _ in range(history_count):
            completed, _history = _pair(completed)
        head, accumulator = _pair(completed)
        if not _same(head, PI):
            raise _Miss("unfinished or wrong-arity append action")
        # Pinned ActionParser constrains PI and history count only.  The
        # accumulator is checked later as a public carrier, without asserting
        # that its outer labels were emitted by this particular action.
        return _Local(marked, phase, accumulator, continuation)

    def _queue(self, term: Term) -> str:
        reversed_bits = []
        while True:
            try:
                queue = self._base_queue(term)
            except _Miss:
                pass
            else:
                # Once a Base boundary matches, malformed cell syntax rejects;
                # it does not fall through to an unrelated carrier production.
                return _word(queue) + "".join(reversed(reversed_bits))
            try:
                local = self._local(term)
            except _Miss:
                pass
            else:
                term = local.accumulator
                continue
            bit, consumed, term = _cell(term)
            if not consumed:
                reversed_bits.append(bit)

    def decode(self, term: Term) -> dict[str, int | str] | None:
        """Read the current finite bare tree, or return None for a noncheckpoint.

        Positive horizons use the paper's totalized empty-word trajectory:
        an empty word can remain empty as phase advances.  The reader does not
        invoke either that transition or the ordinary CTS stopping semantics.
        """
        try:
            clock, environment = _pair(term)
            left, right = _pair(clock)
            if _same(left, C0) and _same(right, C0):
                data = _word(self._environment(environment), literal=True)
                return {"horizon": 0, "phase": 0, "data": data}
        except _Miss:
            pass
        try:
            current, last = term, None
            while True:
                try:
                    local = self._local(current)
                except _Miss:
                    break
                last, current = local, local.continuation
            if last is None:
                return None
            clock, environment = _pair(current)
            left, right = _pair(clock)
            index = _numeral(left)
            if index < 2 or _numeral(right) != index:
                return None
            self._environment(environment)
            horizon = index - 1
            period = len(self.program.appendants)
            if last.phase != (horizon - 1) % period:
                return None
            data = self._queue(last.accumulator)
            if last.marked != (not data):
                return None
            return {"horizon": horizon, "phase": horizon % period, "data": data}
        except _Miss:
            return None


def compile_reader(program: Program) -> CompiledReader:
    """Compile the encoder's adjacent-pairing, unpadded phase-major grammar."""
    compiled = compile_program(program)
    forest = [_Dispatch(App(B, action), label=divmod(index, 2))
              for index, action in enumerate(compiled.action_terms)]
    while len(forest) > 1:
        following = []
        for index in range(0, len(forest) - 1, 2):
            left, right = forest[index:index + 2]
            code = App(B, App(App(S, left.code), right.code))
            following.append(_Dispatch(code, left, right))
        if len(forest) % 2:
            following.append(forest[-1])
        forest = following
    return CompiledReader(program, compiled.actions, compiled.act, forest[0])


def decode(program: Program, term: Term) -> dict[str, int | str] | None:
    """Convenience form; reuse compile_reader(program) for repeated samples."""
    return compile_reader(program).decode(term)
