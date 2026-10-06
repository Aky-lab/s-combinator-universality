"""Finite fuel rows tested with independent holes and explicit native redexes."""
import json
from pathlib import Path
import unittest

from s_only import App, S, parse
from s_only.fuel_probe import fuel_rows, fuel_table, select_fuel
from s_only.probes import Cursor, execute
from s_only.reduction import at, contract_at, root_arguments
from s_only.terms import prefix


def instantiate(pattern, values):
    if pattern == "S":
        return S
    if pattern == "_":
        return next(values)
    return App(instantiate(pattern[0], values), instantiate(pattern[1], values))


def matches(pattern, term):
    if pattern == "_":
        return True
    if pattern == "S":
        return term == S
    return isinstance(term, App) and matches(pattern[0], term.left) and matches(pattern[1], term.right)


def cycle_values(offset):
    terms = (S, parse("S S"), parse("S (S S)"), parse("S S S S"), parse("S (S S S S)"))
    index = offset
    while True:
        yield terms[index % len(terms)]
        index += 1


class FuelProbeTests(unittest.TestCase):
    def test_all_seven_patterns_with_independent_payload_occurrences(self):
        for name, pattern, expected_path in fuel_rows():
            for seed in range(5):
                term = instantiate(pattern, cycle_values(seed))
                selected = select_fuel(term)
                with self.subTest(row=name, seed=seed):
                    self.assertTrue(matches(pattern, term))
                    self.assertEqual(selected, expected_path)
                    self.assertIsNotNone(root_arguments(at(term, selected)))
                    before = prefix(term)
                    contract_at(term, selected)
                    self.assertEqual(prefix(term), before)

    def test_nested_invocations_and_complete_restoration_on_failure(self):
        table = fuel_table()
        for name, pattern, expected in fuel_rows():
            term = instantiate(pattern, cycle_values(0))
            outer = App(S, App(term, S))
            answer = execute(table, Cursor.at(outer, (1, 0)))
            with self.subTest(row=name):
                self.assertTrue(answer.answer)
                self.assertEqual(answer.cursor.path, (1, 0) + expected)
                self.assertIs(answer.cursor.root, outer)
        malformed = App(S, S)
        outer = App(malformed, S)
        answer = execute(table, Cursor.at(outer, (0,)))
        self.assertFalse(answer.answer)
        self.assertEqual(answer.cursor.path, (0,))
        self.assertIs(answer.cursor.root, outer)

    def test_symbolic_head_arity_for_every_pattern_instance(self):
        def fixed_arity(pattern):
            if pattern == "S":
                return 0
            if pattern == "_":
                return None
            left = fixed_arity(pattern[0])
            return None if left is None else left + 1
        for name, pattern, address in fuel_rows():
            with self.subTest(row=name):
                self.assertEqual(fixed_arity(pattern), 3 + len(address))

    def test_all_overlapping_rows_select_the_same_address(self):
        rows = fuel_rows()
        for _, pattern, expected in rows:
            term = instantiate(pattern, cycle_values(1))
            selected = {address for _, candidate, address in rows if matches(candidate, term)}
            self.assertEqual(selected, {expected})

    def test_recorded_fuel_occurrences(self):
        from s_only.queue_fixture import encode
        fixture = json.loads((Path(__file__).resolve().parents[1] / "fixtures/queue_101_path.json").read_text())
        term = encode()
        matched = []
        for index, record in enumerate(fixture["steps"], 1):
            expected = tuple(map(int, record["path"]))
            candidates = [expected]
            if expected and expected[-1] == 0:
                candidates.append(expected[:-1])
            for origin in candidates:
                if select_fuel(term, origin) == expected:
                    matched.append(index)
                    break
            term = contract_at(term, expected)
        self.assertEqual(matched, [5, 6, 7, 8, 9, 10, 11, 27, 28, 29, 30, 31, 32, 33, 34, 35, 57, 58, 59, 60, 61, 62, 63, 64, 65])
        self.assertTrue({5, 6, 7, 8, 9, 10, 11}.issubset(set(matched)))


if __name__ == "__main__":
    unittest.main()
