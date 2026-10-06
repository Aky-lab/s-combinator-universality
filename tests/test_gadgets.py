"""Closed instances of symbolic identities and occurrence isolation."""
import unittest
import json
from pathlib import Path
from s_only import App, S, contract_at, format_term, parse, reduce
from s_only.terms import nodes
from s_only.traces import certificate, verify_certificate


class GadgetTests(unittest.TestCase):
    def test_fork_identity_on_closed_payloads(self):
        # F = S S S; F z -> S z (S z).
        for source in ("S", "S S", "S (S S)", "S S S S"):
            z = parse(source)
            initial = App(parse("S S S"), z)
            expected = App(App(S, z), App(S, z))
            self.assertEqual(contract_at(initial, ()), expected)

    def test_duplicated_payloads_are_distinct_occurrences(self):
        payload = parse("S S S S")
        forked = contract_at(App(parse("S S S"), payload), ())
        rewritten = contract_at(forked, (0, 1))
        self.assertEqual(rewritten.left.right, parse("S S (S S)"))
        self.assertIs(rewritten.right.right, payload)
        self.assertEqual(forked.left.right, payload)

    def test_two_stage_fork(self):
        result = reduce(parse("S (S S) S S"))
        self.assertEqual(len(result.paths), 2)
        self.assertEqual(result.final, parse("S (S S) (S (S S))"))
        self.assertEqual(verify_certificate(certificate(result)), format_term(result.final))

    def test_checked_example_certificates(self):
        files = sorted((Path(__file__).resolve().parents[1] / "examples").glob("*.json"))
        self.assertEqual(len(files), 6)
        for file in files:
            with self.subTest(file=file.name):
                verify_certificate(json.loads(file.read_text()))

    def test_deep_input_and_formatting_do_not_use_python_recursion(self):
        source = "S " * 1500 + "S"
        term = parse(source)
        self.assertEqual(nodes(term), 3001)
        canonical = format_term(term)
        self.assertEqual(format_term(parse(canonical)), canonical)
        result = reduce(term, max_steps=1, max_nodes=10000)
        self.assertEqual(len(result.paths), 1)
        self.assertEqual(verify_certificate(certificate(result)), format_term(result.final))


if __name__ == "__main__":
    unittest.main()
