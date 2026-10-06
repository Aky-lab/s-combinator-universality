"""Independent publication-boundary regressions for the compact checkpoint.

These checks do not widen the two-input simulation claim. In particular, a
structural boundary may describe an implicit blank outside the explicit tape,
while source_step deliberately checks only an in-window source transition.
"""
from dataclasses import replace
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from s_only.cts import Configuration, Machine, Program, ResourceLimit, step
from s_only import neary_fixture as nf
from tools.inspect_cts_encoding import inspect
from tools.neary_fixture import generate


ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts" / "neary-left-toggle"


class CompactReviewTests(unittest.TestCase):
    def test_implicit_blank_head_and_narrow_source_step_domain(self):
        # Neary p.73, Figure 4.3.2 begins with an empty left block. The last
        # boundary token then denotes the implicit blank under the head.
        for state in (1, 2):
            for right in ("", "ab"):
                counter_count = 1 << (len(right) + 1).bit_length()
                word = (nf.state_object("1", state)
                        + "".join(nf.OBJECTS[cell] for cell in right)
                        + nf.OBJECTS["B"] + nf.OBJECTS["mu"] * counter_count
                        + nf.OBJECTS["B"])
                decoded = nf.decode_boundary(Configuration(word))
                self.assertEqual(decoded.source,
                                 nf.SourceConfiguration(state, right, -1))
                with self.assertRaises(ValueError):
                    nf.source_step(decoded.source)
        # Moving left off the first explicit cell also legitimately produces
        # a halting head at -1 without requiring an extra written tape cell.
        self.assertEqual(nf.source_step(nf.SourceConfiguration(1, "b", 0)),
                         nf.SourceConfiguration(2, "a", -1))

    def test_decoder_ignores_source_answer_and_rejects_single_bit_damage(self):
        # Build both final words directly from the published output grammar,
        # without calling run_fixture or using its expected-answer field.
        for read, written in (("a", "b"), ("b", "a")):
            final = (nf.HALT_TOKEN + nf.OBJECTS[written] + nf.OBJECTS["B"]
                     + (nf.OBJECTS["mu/"] + nf.OBJECTS["mup"]) * 2
                     + nf.OBJECTS["B"] + nf.OBJECTS["b"])
            with patch.object(nf, "source_step", side_effect=AssertionError("oracle used")):
                self.assertEqual(nf.decode_boundary(Configuration(final)).source,
                                 nf.SourceConfiguration(2, "b" + written, 0))
                for word in (nf.encode_seed(read).word, final):
                    for position, bit in enumerate(word):
                        damaged = word[:position] + ("1" if bit == "0" else "0") + word[position + 1:]
                        with self.subTest(read=read, length=len(word), position=position):
                            with self.assertRaises(ValueError):
                                nf.decode_boundary(Configuration(damaged))

    def test_exact_completion_and_peak_limits(self):
        for symbol in ("a", "b"):
            result = nf.run_fixture(symbol, max_steps=60250, max_word_bits=5187)
            self.assertEqual(result["cts_steps"], 60250)
            self.assertEqual(result["peak_word_bits"], 5187)
            self.assertEqual(result["source_transition_boundary_step"], 55912)
            self.assertEqual(result["source_halt_event"]["cts_step"], 56083)
            self.assertEqual(result["source_halt_event"]["phase_before"], 170)
            with self.assertRaises(ResourceLimit):
                nf.run_fixture(symbol, max_steps=60249, max_word_bits=5187)
            with self.assertRaises(ResourceLimit):
                nf.run_fixture(symbol, max_steps=60250, max_word_bits=5186)

    def test_actual_peak_rejection_preserves_machine_and_event_number(self):
        fixture = nf.compile_fixture()
        machine = Machine(fixture.program, nf.encode_seed(),
                          max_steps=60250, max_word_bits=5186)
        while True:
            before = machine.snapshot()
            steps_before, peak_before = machine.steps, machine.peak_word_bits
            try:
                machine.tick()
            except ResourceLimit:
                break
        self.assertEqual(machine.snapshot(), before)
        self.assertEqual(machine.steps, steps_before)
        self.assertEqual(machine.peak_word_bits, peak_before)
        expected = step(fixture.program, before)
        self.assertEqual(len(expected.word), 5187)
        machine.max_word_bits = 5187
        event = machine.tick()
        self.assertEqual(machine.snapshot(), expected)
        self.assertEqual(event.step, steps_before + 1)
        self.assertEqual(event.phase, before.phase)

    def test_selected_unused_and_corrupt_halt_appendants_fail(self):
        fixture = nf.compile_fixture()
        provenance = list(fixture.provenance)
        provenance[110] = ("unused: epsilon",)
        altered = replace(fixture, provenance=tuple(provenance))
        with patch.object(nf, "compile_fixture", return_value=altered):
            with self.assertRaisesRegex(AssertionError, "unassigned appendant used at phase 110"):
                nf.run_fixture()
        appendants = list(fixture.program.appendants)
        appendants[170] = ""
        altered = replace(fixture, program=Program(tuple(appendants)))
        with patch.object(nf, "compile_fixture", return_value=altered):
            with self.assertRaisesRegex(AssertionError, "designated halt appendant differs"):
                nf.run_fixture()

    def test_published_artifacts_and_s_reports_reproduce(self):
        with TemporaryDirectory() as directory:
            output = Path(directory)
            generate(output)
            self.assertEqual(sorted(path.name for path in output.iterdir()),
                             sorted(path.name for path in ARTIFACTS.iterdir()))
            for path in output.iterdir():
                self.assertEqual(path.read_bytes(), (ARTIFACTS / path.name).read_bytes())
        document = json.loads((ARTIFACTS / "program.json").read_text())
        program = Program(tuple(document["appendants"]))
        for symbol in ("a", "b"):
            raw = (ARTIFACTS / f"seed-{symbol}.txt").read_bytes()
            self.assertTrue(raw.endswith(b"\n"))
            measured = inspect(program, raw[:-1].decode("ascii"), with_sha256=True)
            saved = json.loads((ROOT / "results" / f"neary_s_initial_{symbol}.json").read_text())
            self.assertEqual(measured, saved)


if __name__ == "__main__":
    unittest.main()
