"""Finite instances of the general appender lemma, checked by two kernels."""
from itertools import product
import unittest

from s_only.encoding import LIVE, PI, append_routine
from s_only.reduction import contract_at, root_arguments, at
from s_only.terms import App, S, nodes, prefix
from s_only.traces import _rewrite, _spans


def apply(*terms):
    out = terms[0]
    for term in terms[1:]:
        out = App(out, term)
    return out


def context(term, address):
    audit = apply(S, S, App(S, S), S)
    for direction in reversed(address):
        term = App(term, audit) if direction == 0 else App(audit, term)
    return term


def routine(constructors, terminal):
    out = terminal
    for constructor in reversed(constructors):
        out = apply(S, App(S, out), constructor)
    return out


class AppenderLemmaTests(unittest.TestCase):
    def check_instance(self, constructors, terminal, value, *, address=(), initial=None):
        cells, histories = [value], []
        for constructor in constructors:
            cells.append(App(constructor, cells[-1]))
            histories.append(App(cells[-2], cells[-1]))
        expected = context(apply(terminal, cells[-1], *reversed(histories)), address)
        initial = routine(constructors, terminal) if initial is None else initial
        current = context(App(initial, value), address)
        serialized = prefix(current)
        for index in range(len(constructors)):
            before = nodes(current)
            path = address + (0,) * index
            for _ in range(2):
                self.assertIsNotNone(root_arguments(at(current, path)))
                serialized = _rewrite(serialized, _spans(serialized), ''.join(map(str, path)))
                current = contract_at(current, path)
                self.assertEqual(prefix(current), serialized)
            self.assertEqual(nodes(current) - before, nodes(cells[index]) + nodes(cells[index + 1]) - 2)
        self.assertEqual(prefix(expected), serialized)

    def test_all_binary_words_through_six_bits(self):
        for size in range(7):
            for word in product('01', repeat=size):
                word = ''.join(word)
                constructors = tuple(LIVE[int(bit)] for bit in word)
                for value in (S, apply(S, S, S, S), apply(S, App(S, S), S, S)):
                    self.check_instance(constructors, PI, value, initial=append_routine(word))

    def test_arbitrary_closed_parameters_and_history_order(self):
        choices = (S, App(S, S), apply(S, S, S, S))
        terminal = apply(S, App(S, S), App(S, S), S)
        for size in range(5):
            for constructors in product(choices, repeat=size):
                self.check_instance(constructors, terminal, apply(S, S, S, S))

    def test_contextual_occurrences_preserve_unrelated_redexes(self):
        constructors = (LIVE[0], apply(S, S, S, S), LIVE[1], S)
        for address in ((0,), (1,), (1, 0, 1), (0, 1, 1, 0)):
            self.check_instance(constructors, App(S, S), apply(S, S, S, S), address=address)


if __name__ == '__main__':
    unittest.main()
