"""Source-identity checks for the independently kernel-checked fixed CTS module.

These tests do not run Lean and do not replace its proof check. They ensure that
editing the Python UT19 table cannot silently leave the Lean instance behind.
"""
import ast
from pathlib import Path
import re
import unittest

from s_only import ut19


FORMAL_SOURCE = Path(__file__).resolve().parents[1] / "formal" / "SOnly38.lean"


class FormalCTSInstanceTests(unittest.TestCase):
    def test_production_literal_matches_python_source(self):
        source = FORMAL_SOURCE.read_text(encoding="utf-8")
        match = re.search(
            r"def productions : List \(List Nat\) :=\s*(\[.*?\])\s*\n\n",
            source,
            re.DOTALL,
        )
        self.assertIsNotNone(match, "Cannot locate the concrete Lean production table")
        rows = ast.literal_eval(match.group(1))
        self.assertEqual(tuple(tuple(row) for row in rows), ut19.UT19_PRODUCTIONS)

    def test_one_hot_compilation_matches_the_formal_definition(self):
        source = FORMAL_SOURCE.read_text(encoding="utf-8")
        self.assertIn(
            "(List.range 19).map (fun index => decide (index + 1 = symbol))",
            source,
        )
        self.assertIn(
            "productions.map (fun word => word.flatMap oneHot) ++ List.replicate 19 []",
            source,
        )
        literal = tuple(
            "".join("1" if index + 1 == symbol else "0"
                    for symbol in row for index in range(19))
            for row in ut19.UT19_PRODUCTIONS
        ) + ("",) * 19
        self.assertEqual(ut19.compile_cts().appendants, literal)
        self.assertEqual(len(literal), 38)
        self.assertEqual(sum(map(len, literal)), 760)
        self.assertEqual(sum(row.count("1") for row in literal), 40)
        self.assertEqual(literal[17], "0" * 17 + "10")

    def test_module_does_not_declare_proof_escape_hatches(self):
        source = FORMAL_SOURCE.read_text(encoding="utf-8")
        # Ignore documentation; this is a source hygiene check, not a kernel audit.
        code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
        code = re.sub(r"--[^\n]*", "", code)
        self.assertNotRegex(code, r"\b(?:axiom|sorry|admit|native_decide)\b")
        self.assertEqual(
            re.findall(r"^import (\S+)$", code, re.MULTILINE),
            ["PureSFormal.Research.RootResetFiniteAllInputsTraceAgreement",
             "PureSFormal.Research.RootResetContractProjection"],
        )


if __name__ == "__main__":
    unittest.main()
