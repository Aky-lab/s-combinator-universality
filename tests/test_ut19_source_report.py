"""Determinism and independent complete tiny-fixture/cycle replay."""
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from s_only import cts, ut19
from tools import ut19_source_report as driver

ROWS = ((2, 3), (4, 4), (18, 4), (1, 1, 19), (7, 9), (8, 9),
        (10, 10), (11, 10), (18, 10), (5, 6), (6, 5, 19),
        (14, 14, 14, 14), (15,), (16, 16), (16, 17), (12, 13),
        (12, 12, 12, 12), (18,), ())
BITS = {
    "+1": ("10001000", "00111100", "11111000"),
    "-1": ("11011000", "00111100", "10101000"),
    "-1 -1": ("0011110010000010", "1100001100000000", "1000000010000010"),
}
EXPECTED = {
    "+1": (90, 1508, 28669, 111, 2124, "b8fb1a29238d02cbe5249637205fe999646ec54f918418f158d279977f983155"),
    "-1": (90, 2476, 47061, 111, 2124, "e9453275c3991d8687f8027a4d12d18e8a1b97fa16ae3b954e9e6f9dc67e5283"),
    "-1 -1": (144, 4124, 78356, 175, 3340, "546d054d7fa2ed0688b4e9224f7f8d8b9461eaf5bcc8da1f87393cad3680622c"),
}


def hot(queue):
    return "".join("1" if symbol == column else "0"
                   for symbol in queue for column in range(1, 20))


def initial(text):
    queue = [19]
    for block, bits in enumerate(BITS[text]):
        for bit in bits:
            queue.extend((5, 6, 1, 1, 19) if bit == "1" else (5, 6))
        if block < 2:
            queue.extend((12, 13, 12, 13))
    return tuple(queue)


def tag_hash(queue, take):
    raw = json.dumps({"queue": queue, "phase": "take" if take else "skip"},
                     separators=(",", ":"), sort_keys=True)
    return sha256(raw.encode("ascii")).hexdigest()


class UT19ReportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = driver.report()

    def test_expected_sizes_event_indices_and_scope(self):
        self.assertEqual(self.result["source_simulation_argument"]["path"],
                         "docs/ut19-simulation-invariants.md")
        self.assertTrue(self.result["result_counter_decoder_implemented"])
        self.assertFalse(self.result["native_s_terms_constructed"])
        self.assertEqual(self.result["native_s_reductions_performed"], 0)
        for fixture in self.result["fixtures"]:
            text, encoded, run = fixture["source_program"], fixture["encoding"], fixture["tag_and_cts_execution"]
            symbols, tag_steps, cts_steps, peak_tag, peak_bits, digest = EXPECTED[text]
            self.assertEqual((encoded["seed_symbols"], encoded["seed_bits"], encoded["seed_bit_sha256"]),
                             (symbols, 19 * symbols, digest))
            self.assertEqual((run["end"]["tag_completed_steps"], run["end"]["cts_completed_steps"]),
                             (tag_steps, cts_steps))
            self.assertEqual((run["peak_tag_queue_symbols"], run["peak_cts_queue_bits"]), (peak_tag, peak_bits))
            self.assertEqual(run["full_boundaries_checked"], tag_steps + 1)
            source = fixture["source_execution"]
            if text != "-1 -1":
                self.assertEqual(source["outcome"], "fallthrough_halt")
                self.assertEqual(source["final_configuration"]["counters"], (1 if text == "+1" else 0,))
                self.assertEqual(run["end"]["decoded_tag_counters"], source["final_configuration"]["counters"])
                self.assertEqual(run["end"]["decoded_cts_counters"], source["final_configuration"]["counters"])
                self.assertEqual(source["restarts"], 0 if text == "+1" else 1)
                self.assertEqual(run["end"]["cts_phase"], 17)
                self.assertEqual(run["end"]["cts_head_bit"], "1")
                self.assertEqual(run["end"]["cts_logged_step_if_executed"], cts_steps + 1)
                self.assertEqual(run["cts_prestates_checked_for_event"], cts_steps + 1)
                self.assertEqual(run["end"]["earlier_cts_event_count"], 0)
            else:
                self.assertEqual(source["outcome"], "exact_recurrence")
                self.assertEqual((source["recurrence"]["first_step"], source["recurrence"]["repeated_step"]), (1, 3))
                self.assertEqual(run["cts_prestates_checked_for_event"], cts_steps)

    def test_all_intermediates_and_exact_cycle_replayed_by_literal_oracle(self):
        # No source encoder, tag step, CTS step/Machine, or generic one-hot
        # implementation supplies a state in this replay.
        appendants = tuple(hot(row) for row in ROWS) + ("",) * 19
        for fixture in self.result["fixtures"]:
            text = fixture["source_program"]
            run = fixture["tag_and_cts_execution"]
            queue, take = initial(text), True
            word, phase = hot(queue), 0
            source_steps, peak_tag, peak_bits = 0, len(queue), len(word)
            seen, events, tag_events, hashes = {}, [], [], []
            repeated = None
            for tick in range(run["end"]["cts_completed_steps"] + 1):
                if tick % 19 == 0:
                    self.assertEqual(word, hot(queue))
                    self.assertEqual(phase, 0 if take else 19)
                    if take and queue[0] == 18:
                        tag_events.append(source_steps)
                    state = (queue, take)
                    if state in seen:
                        repeated = (seen[state], source_steps)
                    else:
                        seen[state] = source_steps
                        hashes.append(bytes.fromhex(tag_hash(queue, take)))
                if phase == 17 and word.startswith("1"):
                    events.append(tick)
                if tick == run["end"]["cts_completed_steps"]:
                    break
                self.assertTrue(word)
                word = word[1:] + (appendants[phase] if word[0] == "1" else "")
                phase = (phase + 1) % 38
                peak_bits = max(peak_bits, len(word))
                if tick % 19 == 18:
                    head = queue[0]
                    queue = queue[1:] + (ROWS[head - 1] if take else ())
                    take = not take
                    source_steps += 1
                    peak_tag = max(peak_tag, len(queue))
            self.assertEqual((peak_tag, peak_bits),
                             (run["peak_tag_queue_symbols"], run["peak_cts_queue_bits"]))
            if text != "-1 -1":
                self.assertEqual(events, [run["end"]["cts_completed_steps"]])
                self.assertEqual(tag_events, [run["end"]["tag_completed_steps"]])
                self.assertEqual(run["end"]["tag_configuration"], {"queue": list(queue), "phase": "take"})
                self.assertEqual(run["end"]["tag_configuration_sha256"], tag_hash(queue, take))
            else:
                self.assertEqual(events, [])
                self.assertEqual(tag_events, [])
                self.assertEqual(repeated, (1562, 4124))
                certificate = run["recurrence"]
                self.assertEqual(certificate["period_tag_steps"], 2562)
                self.assertEqual(certificate["period_cts_steps"], 48678)
                self.assertEqual(certificate["configuration"], {"queue": list(queue), "phase": "take"})
                self.assertEqual(certificate["first_tag_configuration_sha256"], tag_hash(queue, take))
                self.assertEqual(certificate["repeated_tag_configuration_sha256"], tag_hash(queue, take))
                first = repeated[0]
                self.assertEqual(certificate["prefix_boundary_digest_sha256"], sha256(b"".join(hashes[:first])).hexdigest())
                self.assertEqual(certificate["cycle_boundary_digest_sha256"], sha256(b"".join(hashes[first:])).hexdigest())
                self.assertEqual(certificate["prefix_cts_prestate_checks"], 29678)
                self.assertEqual(certificate["cycle_cts_prestate_checks"], 48678)
                self.assertEqual(certificate["prefix_selected_event_count"], 0)
                self.assertEqual(certificate["cycle_selected_event_count"], 0)
                # Replay one more entire cycle independently; equal state and
                # event-free cycle give an infinite-run certificate by determinism.
                repeated_word, repeated_phase = word, phase
                for _ in range(certificate["period_cts_steps"]):
                    self.assertTrue(word)
                    self.assertFalse(phase == 17 and word[0] == "1")
                    word = word[1:] + (appendants[phase] if word[0] == "1" else "")
                    phase = (phase + 1) % 38
                self.assertEqual((word, phase), (repeated_word, repeated_phase))

    def test_limits_raise_instead_of_false_completed_report(self):
        for kwargs in ({"max_source_steps": 0}, {"max_counter_value": 0},
                       {"max_tag_steps": 1507}, {"max_cts_steps": 28668},
                       {"max_queue_symbols": 143}, {"max_word_bits": 2735},
                       {"max_seen_symbols": 89}):
            with self.assertRaises(cts.ResourceLimit):
                driver.report(**kwargs)
        for name in self.result["bounds"]:
            for value in (-1, True, 1.0):
                with self.assertRaises(ValueError):
                    driver.report(**{name: value})
        with patch.object(driver, "_source_run", side_effect=AssertionError("ran source")):
            with self.assertRaises(cts.ResourceLimit):
                driver.report(max_queue_symbols=143)
        with patch.object(driver, "_source_run", side_effect=AssertionError("ran source")):
            with self.assertRaises(cts.ResourceLimit):
                driver.report(encoding_limits=ut19.EncodingLimits(max_seed_bits=1710))

    def test_artifact_and_generation_are_deterministic(self):
        with TemporaryDirectory() as directory:
            first, second = Path(directory) / "first.json", Path(directory) / "second.json"
            self.assertEqual(driver.generate(first), self.result)
            self.assertEqual(driver.generate(second), self.result)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            checked_in = Path(__file__).resolve().parents[1] / "results" / "ut19_source.json"
            self.assertEqual(first.read_bytes(), checked_in.read_bytes())
            invalid = Path(directory) / "invalid.json"
            with self.assertRaises(cts.ResourceLimit):
                driver.generate(invalid, max_tag_steps=0)
            self.assertFalse(invalid.exists())

    def test_a_structural_result_mismatch_prevents_a_report(self):
        for name in ('read_tag_result', 'read_cts_result'):
            with self.subTest(reader=name), patch.object(driver, name, return_value=(7,)):
                with self.assertRaisesRegex(AssertionError, 'structural result differs'):
                    driver.report()


if __name__ == "__main__":
    unittest.main()
