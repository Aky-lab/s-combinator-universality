"""Finite compiler audit, including independent binary-string execution.

The literal table below is an independent Q=2 expansion of the primary PDF,
not a call into the production token or table constructors. Passing it does
not prove the thesis's general compiler or an S-only simulation theorem.
"""
from hashlib import sha256
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tools.neary_fixture import generate

from s_only.cts import Configuration, ResourceLimit
from s_only import neary_fixture as nf


def literal_hot(length, position):
    bits = ["0"] * length
    bits[position] = "1"
    return "".join(bits)


def literal_program():
    result = [""] * 482
    a, b, blank = [literal_hot(482, i) for i in (1, 2, 3)]
    am, bm, blankm = [literal_hot(482, i) for i in (4, 5, 6)]
    mu, mup, mum = literal_hot(241, 7), literal_hot(482, 8), literal_hot(482, 9)
    ap, bp, blankp, dp = [literal_hot(241, i) for i in (10, 11, 12, 13)]
    h1, h2 = literal_hot(482, 110), literal_hot(482, 170)
    for phase in (0, 241):
        for offset, value in ((1, a), (2, b), (3, blank), (4, am), (5, bm),
                              (6, blankm), (8, mup), (9, mum)):
            result[phase + offset] = value
    result[7], result[248] = mum, mup
    result[110] = literal_hot(492, 111)
    result[115] = literal_hot(492, 116)
    result[351] = result[356] = "0" * 241 + literal_hot(492, 116)
    result[111], result[116] = literal_hot(492, 102), literal_hot(492, 107)
    result[352], result[357] = literal_hot(351, 104), literal_hot(361, 109)
    for phase in (10, 251):
        for offset, value in ((4, am), (5, bm), (6, blankm), (8, mup), (9, mum)):
            result[phase + offset] = value
    result[11:14] = [ap, bp, blankp]
    result[252:255] = [a, b, blank]
    result[112], result[117] = literal_hot(492, 93), literal_hot(492, 98)
    for phase in (20, 261, 30, 271):
        for offset, value in ((4, am), (5, bm), (6, blankm), (8, mup), (9, mum),
                              (10, ap), (11, bp), (12, blankp)):
            result[phase + offset] = value
    result[113] = literal_hot(482, 13) + literal_hot(492, 84) + dp
    result[118] = literal_hot(482, 13) + literal_hot(492, 89) + dp
    result[354], result[359] = literal_hot(492, 84), literal_hot(492, 89)
    result[43] = dp
    result[114], result[119] = "0" * 442 + h1, "0" * 442 + literal_hot(482, 115)
    for phase in (40, 281):
        for offset, value in ((4, am), (5, bm), (6, blankm), (8, mu), (9, mum)):
            result[phase + offset] = value
    result[50:53], result[291:294] = [a, b, blank], [am, bm, blankm]
    result[355], result[360] = "0" * 362, "0" * 352
    for phase in (120, 130):
        for offset, value in ((1, h2 + b), (2, h2 + a), (4, a), (5, b), (6, blank), (9, mu)):
            result[phase + offset] = value
    result[123] = blank + literal_hot(552, 69) + h2 + a
    result[133] = blank + h2 + a
    result[69] = "0" * 412
    result[180], result[240] = h1, h2
    result[71:74] = [a, b, blank]
    result[77] = result[318] = mu + mu
    result[78], result[79] = mup + mup, mum + mum
    result[170] = h2
    return tuple(result)


class NearyFixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = nf.compile_fixture()
        cls.runs = {symbol: nf.run_fixture(symbol) for symbol in ("a", "b")}

    def test_all_appendants_match_independent_table_expansion(self):
        self.assertEqual(self.fixture.program.appendants, literal_program())
        self.assertEqual(len(self.fixture.program.appendants), 482)
        self.assertEqual(sum(p != ("unused: epsilon",) for p in self.fixture.provenance), 128)
        self.assertEqual(self.fixture.provenance[53], ("4.3.5 erase dummy",))
        self.assertEqual(self.fixture.provenance[0], ("unused: epsilon",))

    def test_seed_exact_bits_and_size(self):
        prefix = literal_hot(482, 110) + literal_hot(482, 3)
        counter = literal_hot(241, 7) * 4
        suffix = literal_hot(482, 3) + literal_hot(482, 2)
        for symbol, position in (("a", 1), ("b", 2)):
            seed = nf.encode_seed(symbol)
            self.assertEqual(seed, Configuration(prefix + counter + suffix + literal_hot(482, position)))
            self.assertEqual(len(seed.word), 3374)
        self.assertEqual(nf.digest(nf.encode_seed().word),
                         "0e5e14f2577232d416db387de45280b61e03e1df49e748713c50a8ad6ef463c1")

    def test_both_source_symbols_toggle_and_move_left(self):
        for symbol, output in (("a", "bb"), ("b", "ba")):
            run = self.runs[symbol]
            self.assertEqual(run["source_initial"], {"state": 1, "tape": "b" + symbol, "head": 1})
            self.assertEqual(run["source_decoded"], {"state": 2, "tape": output, "head": 0})
            self.assertEqual(run["source_expected"], run["source_decoded"])
            self.assertEqual(run["source_transition_boundary_step"], 55912)
            self.assertEqual(run["source_halt_event"]["cts_step"], 56083)
            self.assertEqual(run["source_halt_event"]["phase_before"], 170)
            self.assertEqual(run["cts_steps"], 60250)
            self.assertEqual(run["peak_word_bits"], 5187)
            self.assertFalse(run["table_4_3_7_exercised"])
            self.assertEqual(run["s_reductions_performed"], 0)

    def test_full_runs_replayed_by_independent_string_semantics(self):
        # Directly interpret the independently expanded table. No CTS step,
        # Machine, one_hot, state_object, or boundary encoder is used here.
        appendants = literal_program()
        for symbol in ("a", "b"):
            run = self.runs[symbol]
            word = nf.encode_seed(symbol).word
            phase, peak, halt_steps = 0, len(word), []
            selected, one_count = set(), 0
            saved = {0: word}
            checkpoints = {entry["cts_step"]: entry for entry in run["macro_boundaries"]}
            for number in range(1, run["cts_steps"] + 1):
                bit = word[0]
                if bit == "1":
                    selected.add(phase)
                    one_count += 1
                    self.assertNotEqual(self.fixture.provenance[phase], ("unused: epsilon",))
                    if phase == 170:
                        halt_steps.append(number)
                    word = word[1:] + appendants[phase]
                else:
                    word = word[1:]
                phase = (phase + 1) % 482
                peak = max(peak, len(word))
                if number in checkpoints:
                    saved[number] = word
                    self.assertEqual(phase, 0)
                    self.assertEqual(sha256(word.encode()).hexdigest(), checkpoints[number]["word_sha256"])
            self.assertEqual(sorted(selected), run["selected_appendant_indices"])
            self.assertEqual(one_count, run["consumed_one_events"])
            self.assertEqual(halt_steps[0], 56083)
            self.assertEqual(peak, run["peak_word_bits"])
            self.assertEqual(saved[55912], saved[60250])
            self.assertEqual(len(word), 4338)
            output = "b" if symbol == "a" else "a"
            expected_word = (literal_hot(482, 170) + literal_hot(482, 1 if output == "a" else 2)
                             + literal_hot(482, 3)
                             + (literal_hot(482, 9) + literal_hot(482, 8)) * 2
                             + literal_hot(482, 3) + literal_hot(482, 2))
            self.assertEqual(word, expected_word)

    def test_source_halt_and_ordinary_recurrence_are_separate(self):
        run = self.runs["b"]
        self.assertEqual(run["ordinary_cts_observation"], "repeated_nonempty_configuration")
        self.assertLess(run["source_halt_event"]["cts_step"], run["recurrence"]["repeated_step"])
        self.assertEqual(run["recurrence"]["period_steps"], 4338)
        self.assertEqual(run["recurrence"]["word_bits"], 4338)
        self.assertEqual(self.fixture.program.appendants[170], literal_hot(482, 170))

    def test_all_used_appendants_have_source_provenance(self):
        for run in self.runs.values():
            self.assertEqual(run["distinct_phases_visited"], 482)
            self.assertEqual(run["distinct_phases_consuming_zero"], 482)
            self.assertEqual(run["selected_unspecified_appendant_events"], 0)
            self.assertEqual(run["consumed_one_events"] + run["consumed_zero_events"], run["cts_steps"])
            for phase in run["selected_appendant_indices"]:
                self.assertNotEqual(self.fixture.provenance[phase], ("unused: epsilon",))

    def test_decoder_accepts_only_complete_boundary_grammar(self):
        seed = nf.encode_seed()
        self.assertEqual(nf.decode_boundary(seed).source, nf.SourceConfiguration(1, "bb", 1))
        invalid = [Configuration(seed.word, 1), Configuration(seed.word[1:]),
                   Configuration(seed.word + "0"), Configuration(seed.word[:-1]),
                   Configuration(seed.word.replace(nf.OBJECTS["mu"] * 4, nf.OBJECTS["mu"] * 3)),
                   Configuration(nf.state_object("1") + seed.word[482:].replace(nf.OBJECTS["b"], nf.OBJECTS["b/"], 1)),
                   Configuration(nf.state_object("2") + seed.word[482:]),
                   Configuration("")]
        for config in invalid:
            with self.subTest(length=len(config.word), phase=config.phase):
                with self.assertRaises(ValueError):
                    nf.decode_boundary(config)

    def test_resource_bounds_do_not_claim_completion(self):
        with self.assertRaises(ResourceLimit):
            nf.run_fixture(max_steps=56082)
        with self.assertRaises(ResourceLimit):
            nf.run_fixture(max_word_bits=4000)
        with self.assertRaises(ResourceLimit):
            nf.run_fixture(max_word_bits=3373)

    def test_invalid_source_and_token_inputs(self):
        for symbol in ("", "aa", "0", None):
            with self.assertRaises(ValueError):
                nf.encode_seed(symbol)
        for args in ((-1, 4), (4, 4)):
            with self.assertRaises(ValueError):
                nf.one_hot(*args)
        for state in (0, 3):
            with self.assertRaises(ValueError):
                nf.state_object("1", state)
        with self.assertRaises(ValueError):
            nf.state_object("2", 2)
        with self.assertRaises(ValueError):
            nf.state_object("missing")
        for source in (nf.SourceConfiguration(2, "bb", 1), nf.SourceConfiguration(1, "b", 1),
                       nf.SourceConfiguration(1, "bc", 1)):
            with self.assertRaises(ValueError):
                nf.source_step(source)

    def test_artifact_files_are_verified_and_deterministic(self):
        with TemporaryDirectory() as first, TemporaryDirectory() as second:
            first, second = Path(first), Path(second)
            self.assertEqual(generate(first), generate(second))
            self.assertEqual(sorted(p.name for p in first.iterdir()),
                             ["manifest.json", "program.json", "runs.json", "seed-a.txt", "seed-b.txt"])
            for path in first.iterdir():
                self.assertEqual(path.read_bytes(), (second / path.name).read_bytes())
            self.assertEqual((first / "seed-b.txt").read_text().strip(), nf.encode_seed().word)
        with TemporaryDirectory() as folder:
            with self.assertRaises(ResourceLimit):
                generate(Path(folder), max_steps=10)
            self.assertEqual(list(Path(folder).iterdir()), [])

    def test_generation_is_deterministic(self):
        self.assertEqual(nf.compile_fixture(), self.fixture)
        self.assertEqual(nf.run_fixture("b"), self.runs["b"])


if __name__ == "__main__":
    unittest.main()
