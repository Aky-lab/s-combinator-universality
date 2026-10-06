"""Independent structural checks for the finite nested CLOCK graph."""
from functools import lru_cache
import unittest

from s_only.probes import OBSERVATIONS, Cursor
from s_only.queue_fixture import B, C0, apply
from s_only.selector_parts.clock import compile_clock
from s_only.selector_parts.graph import GraphBuilder
from s_only.terms import App, S


def _arguments(term):
    arguments = []
    while isinstance(term, App):
        arguments.append(term.right)
        term = term.left
    return tuple(reversed(arguments))


def _numeral_parity(term):
    bit = 0
    while isinstance(term, App) and term.left == B:
        bit = 1 - bit
        term = term.right
    return bit if term == C0 else None


def _oracle(term):
    """Return the selected relative path, or None; inspect no graph state."""
    first = _arguments(term)
    parity = _numeral_parity(first[0]) if len(first) == 3 else None
    if len(first) == 3 and parity is None:
        return None
    if not isinstance(term, App):
        return None
    core, path = term.left, (0,)
    while len(_arguments(core)) == 2:
        core, path = core.right, path + (1,)
    head = _arguments(core)
    if len(head) != 3:
        return None
    if len(first) == 3:
        other = _numeral_parity(head[-1])
        if other is None:
            return None
        if parity != other:
            return ()
    return path


@lru_cache(maxsize=None)
def _trees(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for split in range(1, leaves)
                 for left in _trees(split) for right in _trees(leaves - split))


def _positions(term, path=()):
    yield path
    if isinstance(term, App):
        yield from _positions(term.left, path + (0,))
        yield from _positions(term.right, path + (1,))


def _numeral(number):
    term = C0
    for _ in range(number):
        term = App(B, term)
    return term


def _wrap(stage, count, term):
    for _ in range(count):
        term = apply(S, stage, term)
    return term


class ClockSelectorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        builder = GraphBuilder()
        cls.yes = builder.uniform("true")
        cls.no = builder.uniform("false")
        cls.start = compile_clock(builder, cls.yes, cls.no)
        cls.states = builder.finish()

    def checked(self, ambient, path=()):
        cursor = original = Cursor.at(ambient, path)
        expected = _oracle(cursor.focus)
        control = self.start
        # External test instrumentation only; emitted controls have no counter.
        for _ in range(100000):
            if control in (self.yes, self.no):
                break
            instruction = self.states[control][
                OBSERVATIONS.index((cursor.kind, cursor.incoming))]
            if instruction.command != "stay":
                cursor = cursor.move(instruction.command)
            control = instruction.next_state
        else:
            self.fail("CLOCK graph did not terminate")
        self.assertEqual(control == self.yes, expected is not None)
        wanted = Cursor.at(ambient, path if expected is None else path + expected)
        self.assertEqual(cursor.path, wanted.path)
        self.assertIs(cursor.focus, wanted.focus)
        self.assertIs(cursor.root, original.root)
        for actual, required in zip(cursor.parents, wanted.parents):
            self.assertIs(actual.parent, required.parent)
            self.assertEqual(actual.side, required.side)
        if expected is not None:
            self.assertEqual(len(_arguments(cursor.focus)), 3)

    def test_all_626_small_trees_and_8788_nested_starts(self):
        trees = starts = 0
        for leaves in range(1, 9):
            for term in _trees(leaves):
                trees += 1
                for path in _positions(term):
                    starts += 1
                    self.checked(term, path)
        self.assertEqual((trees, starts), (626, 8788))

    def test_generated_parity_and_growth_under_nested_contexts(self):
        for stage in range(4):
            for wrappers in range(5):
                for left in range(4):
                    for right in range(4):
                        core = _wrap(_numeral(stage), wrappers,
                                     App(_numeral(left), _numeral(right)))
                        source = App(core, apply(S, S, S))
                        self.checked(source)
                        # Incoming R below an inverse-looking parent must not
                        # let either restoration pass escape this invocation.
                        self.checked(apply(S, S, source), (1,))
                        self.checked(App(source, C0), (0,))

    def test_malformed_numerals_and_wrapper_fields(self):
        malformed = (S, B, App(S, C0), App(C0, S), App(B, S))
        for stage in malformed + (_numeral(0), _numeral(1)):
            for right in malformed + (_numeral(0), _numeral(1)):
                for wrappers in range(1, 4):
                    source = App(_wrap(stage, wrappers, App(C0, right)), S)
                    self.checked(source)
                    self.checked(App(B, source), (1,))
        # A malformed first numeral rejects even though growth could find the
        # core redex.  This guard is stronger than simply recognizing growth.
        source = apply(S, S, App(C0, C0), S)
        self.assertIsNone(_oracle(source))
        self.checked(source)

    def test_exact_first_second_and_growth_source_branches(self):
        one = _numeral(1)
        cases = (
            # Head miss and non-application growth entry.
            (S, None),
            # Head miss, followed by growth selecting the left core redex.
            (apply(C0, C0, S), (0,)),
            # Parsed first head with an invalid first numeral.
            (apply(S, S, App(C0, C0), S), None),
            # Valid first numeral, second core has no saturated endpoint.
            (apply(S, C0, S, S), None),
            # Valid first numeral/core, invalid second numeral.
            (apply(S, C0, App(C0, S), S), None),
            # Accepted opposite parity launches at the invocation itself.
            (apply(S, C0, App(C0, one), S), ()),
            # Accepted equal parity chooses the nested growth redex.
            (apply(S, one, App(C0, one), S), (0, 1)),
        )
        for source, expected in cases:
            self.assertEqual(_oracle(source), expected)
            self.checked(source)
            self.checked(App(B, source), (1,))

    def test_compilation_has_only_finite_six_observation_controls(self):
        self.assertLess(len(self.states), 1000)
        for row in self.states:
            self.assertIs(type(row), tuple)
            self.assertEqual(len(row), 6)
            for instruction in row:
                self.assertIn(instruction.command,
                              ("true", "false", "stay", "L", "R", "U"))
                if instruction.command not in ("true", "false"):
                    self.assertIs(type(instruction.next_state), int)
                    self.assertIn(instruction.next_state, range(len(self.states)))


if __name__ == "__main__":
    unittest.main()
