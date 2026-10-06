"""Independent Reset-word fixtures; no source program or evaluator supplies output."""
from contextlib import ExitStack
from dataclasses import FrozenInstanceError, replace
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from s_only import alternating_tag as tag
from s_only import cts, ut19_readout as reader


def reset(bits):
    return tuple(symbol for bit in bits
                 for symbol in ((18, 10, 18, 4) if bit else (18, 10)))


def final(bits, states):
    return tuple(symbol for bit, state in zip(bits, states)
                 for symbol in ((10 + state, 10, 4, 4) if bit else (10 + state, 10)))


def event(values, widths=None):
    """Construct grammar words directly, independently of any source encoding."""
    if widths is None:
        widths = (3,) * (len(values) + 2)
    assert len(widths) == len(values) + 2
    result = []
    for block in range(len(values) + 1):
        result.extend(reset(tuple((i + block) % 2 for i in range(widths[block]))))
        if block < len(values):
            result.extend((16,) * (4 ** (values[block] + 1)))
    width = widths[-1]
    result.extend(final(tuple(i % 2 for i in range(width)),
                        tuple((i + 1) % 2 for i in range(width))))
    return tuple(result)


def hot(word):
    # Direct literal position definition, not the production one-hot compiler.
    return "".join("1" if symbol == column else "0"
                   for symbol in word for column in range(1, 20))


def tag_state(word, phase=tag.TAKE):
    return tag.Configuration(tuple(symbol - 1 for symbol in word), phase)


def cts_state(word):
    return cts.Configuration(hot(word)[17:], 17)


def forged(kind, **fields):
    """Exercise the reader's own field checks without constructor filtering."""
    value = object.__new__(kind)
    for name, field in fields.items():
        object.__setattr__(value, name, field)
    return value


class UT19ReadoutTests(unittest.TestCase):
    def assert_result(self, word, expected, limits=None):
        kwargs = {} if limits is None else {"limits": limits}
        for result in (reader.read_tag_result(tag_state(word), **kwargs),
                       reader.read_cts_result(cts_state(word), **kwargs)):
            self.assertIs(type(result), tuple)
            self.assertEqual(result, expected)
            self.assertTrue(all(type(value) is int for value in result))

    def assert_invalid(self, word):
        with self.assertRaises(ValueError):
            reader.read_tag_result(tag_state(word))
        with self.assertRaises(ValueError):
            reader.read_cts_result(cts_state(word))

    def test_complete_checked_in_first_event_queues(self):
        path = Path(__file__).resolve().parents[1] / "results" / "ut19_source.json"
        fixtures = json.loads(path.read_text())["fixtures"]
        checked = []
        for fixture in fixtures:
            end = fixture["tag_and_cts_execution"]["end"]
            if end["outcome"] != "designated_event":
                continue
            word = tuple(end["tag_configuration"]["queue"])
            expected = {"+1": (1,), "-1": (0,)}[fixture["source_program"]]
            self.assert_result(word, expected)
            binary = cts_state(word)
            self.assertEqual(len(binary.word), end["cts_word_bits"])
            raw = json.dumps({"phase": binary.phase, "word": binary.word},
                             sort_keys=True, separators=(",", ":")).encode("ascii")
            self.assertEqual(sha256(raw).hexdigest(), end["cts_configuration_sha256"])
            checked.append(fixture["source_program"])
        self.assertEqual(checked, ["+1", "-1"])

    def test_varied_values_counts_and_equal_memory_widths(self):
        cases = 0
        for count in range(1, 4):
            for values in product(range(3), repeat=count):
                for width in (1, 2, 3, 8):
                    self.assert_result(event(values, (width,) * (count + 2)), values)
                    cases += 1
        self.assertEqual(cases, 156)
        self.assert_result(event((0, 1, 2, 3, 4)), (0, 1, 2, 3, 4))

    def test_independent_widths_and_bits_are_intentional(self):
        # No source program, common W, power-of-two W, or initializer equality
        # is asserted. These are structural words, not claimed reachable words.
        values = (2, 0, 1)
        self.assert_result(event(values, (1, 3, 5, 2, 7)), values)
        for bits in product((0, 1), repeat=3):
            for states in product((0, 1), repeat=3):
                word = reset(bits) + (16,) * 4 + reset(bits[::-1]) + final(bits, states)
                self.assert_result(word, (0,))

    def test_counter_count_is_not_fixed_by_the_19_symbol_alphabet(self):
        values = (0,) * 1025
        self.assert_result(event(values, (1,) * 1027), values)

    def test_no_evaluator_encoder_boundary_parser_or_trace_is_used(self):
        word = event((1, 0))
        tag_input, binary_input = tag_state(word), cts_state(word)
        with ExitStack() as stack:
            for module, names in ((tag, ("step", "Machine", "evaluate", "encode_word",
                                         "encode_configuration", "decode_boundary")),
                                  (cts, ("step", "Machine"))):
                for name in names:
                    stack.enter_context(patch.object(module, name,
                                                     side_effect=AssertionError(name)))
            self.assertEqual(reader.read_tag_result(tag_input), (1, 0))
            self.assertEqual(reader.read_cts_result(binary_input), (1, 0))

    def test_ignored_18_and_wrong_tag_head_or_phase_are_not_results(self):
        word = event((0,))
        for state in (tag_state(word, tag.SKIP), tag_state((10,) + word),
                      tag_state((16,) + word), tag.Configuration(())):
            with self.assertRaises(ValueError):
                reader.read_tag_result(state)
        # An 18 can occur in the queue without being the selected head.
        self.assert_invalid((10, 10) + word)

    def test_actual_cts_zero_steps_give_exact_phase_17_suffix(self):
        word = event((2, 0))
        binary, phase = hot(word), 0
        for offset in range(17):
            self.assertEqual(binary[0], "0")
            with self.assertRaises(ValueError):
                reader.read_cts_result(cts.Configuration(binary, phase))
            # The ordinary rule at a zero appends nothing, for any appendant.
            binary, phase = binary[1:], phase + 1
        self.assertEqual((phase, binary[:2]), (17, "10"))
        self.assertEqual(reader.read_cts_result(cts.Configuration(binary, phase)), (2, 0))
        self.assertEqual("0" * 17 + binary, hot(word))
        for wrong in (hot(word), hot(word)[16:], hot(word)[18:], hot(word)[19:]):
            with self.assertRaises(ValueError):
                reader.read_cts_result(cts.Configuration(wrong, 17))

    def test_all_wrong_cts_phases_and_skipped_18_reject(self):
        word = cts_state(event((0,))).word
        for phase in (*range(17), *range(18, 38), 55, 10 ** 100):
            with self.assertRaises(ValueError):
                reader.read_cts_result(cts.Configuration(word, phase))

    def test_forbidden_reset_alphabet_symbols_reject(self):
        word = event((0,))
        for symbol in set(range(1, 21)) - {4, 10, 11, 16, 18}:
            self.assert_invalid(word[:-1] + (symbol,))

    def test_run_lengths_must_be_positive_powers_of_four_at_least_four(self):
        for length in (0, 1, 2, 3, 5, 8, 12, 15, 17, 32, 63, 65, 255):
            self.assert_invalid((18, 10) + (16,) * length + (18, 10, 10, 10))
        for length, value in ((4, 0), (16, 1), (64, 2), (256, 3), (1024, 4)):
            self.assert_result((18, 10) + (16,) * length + (18, 10, 10, 10), (value,))

    def test_malformed_or_truncated_reset_and_final_memory_reject(self):
        counter = (16,) * 4
        good_r, good_t = (18, 10), (11, 10, 4, 4)
        for bad_r in ((), (18,), (18, 4), (18, 11), (18, 10, 18),
                      (18, 10, 18, 4, 18, 4), (18, 10, 4, 4)):
            self.assert_invalid(bad_r + counter + good_r + good_t)
            self.assert_invalid(good_r + counter + bad_r + good_t)
        for bad_t in ((), (10,), (11,), (11, 11), (4, 4, 10, 10),
                      (10, 10, 4), (10, 10, 4, 4, 4, 4), (10, 4),
                      (10, 10, 18, 10), (10, 10, 16, 16, 16, 16)):
            self.assert_invalid(good_r + counter + good_r + bad_t)
        # Legal alphabet and valid runs alone are insufficient.
        self.assert_invalid((18,) + counter + (10, 10))
        self.assert_invalid(good_r + good_t)  # C=0 is outside the source grammar.

    def test_malformed_cts_head_codes_blocks_and_truncation_reject(self):
        original = cts_state(event((0,))).word
        for head in ("00", "01", "11"):
            with self.assertRaises(ValueError):
                reader.read_cts_result(cts.Configuration(head + original[2:], 17))
        for block in ("0" * 19, "1" * 19, "11" + "0" * 17,
                      "1" + "0" * 18):  # Last block encodes forbidden label 1.
            with self.assertRaises(ValueError):
                reader.read_cts_result(cts.Configuration(original[:2] + block + original[21:], 17))
        for word in ("", "1", "10", original[:-1], original + "0"):
            with self.assertRaises(ValueError):
                reader.read_cts_result(cts.Configuration(word, 17))
        malformed = original[:2] + "2" + original[3:]
        with self.assertRaises(ValueError):
            reader.read_cts_result(forged(cts.Configuration, word=malformed, phase=17))

    def test_exact_input_and_output_resource_boundaries(self):
        values = (0, 1, 2, 3, 4)
        word = event(values)
        binary = cts_state(word)
        output_bits = sum(max(1, value.bit_length()) for value in values)
        limits = reader.ReadoutLimits(len(word), len(binary.word), len(values), output_bits)
        self.assert_result(word, values, limits)
        for name in ("max_queue_symbols", "max_counters", "max_output_bits"):
            too_small = replace(limits, **{name: getattr(limits, name) - 1})
            with self.assertRaises(reader.ResourceLimit):
                reader.read_tag_result(tag_state(word), limits=too_small)
            with self.assertRaises(reader.ResourceLimit):
                reader.read_cts_result(binary, limits=too_small)
        with self.assertRaises(reader.ResourceLimit):
            reader.read_cts_result(binary, limits=replace(limits, max_word_bits=len(binary.word) - 1))
        # The fixed zero prefix is virtual, so only actual input bits are charged.
        self.assertEqual(limits.max_word_bits, 19 * limits.max_queue_symbols - 17)
        self.assertEqual(reader.read_cts_result(binary, limits=limits), values)
        # A tag configuration contains no CTS string and does not spend its cap.
        self.assertEqual(reader.read_tag_result(tag_state(word),
                                                limits=replace(limits, max_word_bits=0)), values)

    def test_zero_output_caps_reject_and_zero_value_costs_one_bit(self):
        word = event((0,))
        self.assert_result(word, (0,), reader.ReadoutLimits(max_output_bits=1, max_counters=1))
        for limits in (reader.ReadoutLimits(max_counters=0), reader.ReadoutLimits(max_output_bits=0)):
            for function, state in ((reader.read_tag_result, tag_state(word)),
                                    (reader.read_cts_result, cts_state(word))):
                with self.assertRaises(reader.ResourceLimit):
                    function(state, limits=limits)

    def test_input_caps_preflight_before_any_scan(self):
        bad_tag = forged(tag.Configuration, queue=(17, object()), phase=tag.TAKE)
        bad_cts = forged(cts.Configuration, word="10" + "x" * 19, phase=17)
        with patch.object(reader, "_read_symbols", side_effect=AssertionError("parsed")):
            with self.assertRaises(reader.ResourceLimit):
                reader.read_tag_result(bad_tag, limits=reader.ReadoutLimits(max_queue_symbols=1))
            with self.assertRaises(reader.ResourceLimit):
                reader.read_cts_result(bad_cts, limits=reader.ReadoutLimits(max_word_bits=20))
            with self.assertRaises(reader.ResourceLimit):
                reader.read_cts_result(bad_cts, limits=reader.ReadoutLimits(max_queue_symbols=1))

    def test_limits_are_exact_plain_immutable_and_rechecked(self):
        class Integer(int):
            pass

        class Limits(reader.ReadoutLimits):
            pass

        for name in reader.ReadoutLimits.__dataclass_fields__:
            for value in (-1, True, 1.0, "1", Integer(1)):
                with self.assertRaises(ValueError):
                    reader.ReadoutLimits(**{name: value})
        limits = reader.ReadoutLimits()
        with self.assertRaises(FrozenInstanceError):
            limits.max_counters = 1
        for bad in (None, {}, Limits()):
            with self.assertRaises(ValueError):
                reader.read_tag_result(tag_state(event((0,))), limits=bad)
        object.__setattr__(limits, "max_output_bits", True)
        with self.assertRaises(ValueError):
            reader.read_cts_result(cts_state(event((0,))), limits=limits)

    def test_configuration_and_field_subclasses_or_mutations_reject(self):
        class Integer(int):
            pass

        class String(str):
            pass

        class Tuple(tuple):
            pass

        class TagState(tag.Configuration):
            pass

        class CTSState(cts.Configuration):
            pass

        good_tag = tag_state(event((0,)))
        good_cts = cts_state(event((0,)))
        for state in (None, good_cts, TagState(good_tag.queue),
                      forged(tag.Configuration, queue=list(good_tag.queue), phase=tag.TAKE),
                      forged(tag.Configuration, queue=Tuple(good_tag.queue), phase=tag.TAKE),
                      forged(tag.Configuration, queue=good_tag.queue, phase=String(tag.TAKE)),
                      forged(tag.Configuration, queue=(Integer(17),) + good_tag.queue[1:], phase=tag.TAKE),
                      forged(tag.Configuration, queue=good_tag.queue[:-1] + (Integer(9),), phase=tag.TAKE),
                      forged(tag.Configuration, queue=good_tag.queue[:-1] + (True,), phase=tag.TAKE)):
            with self.assertRaises(ValueError):
                reader.read_tag_result(state)
        for state in (None, good_tag, CTSState(good_cts.word, 17),
                      cts.Configuration(String(good_cts.word), 17),
                      forged(cts.Configuration, word=list(good_cts.word), phase=17),
                      forged(cts.Configuration, word=good_cts.word, phase=Integer(17)),
                      forged(cts.Configuration, word=good_cts.word, phase=True)):
            with self.assertRaises(ValueError):
                reader.read_cts_result(state)

    def test_pure_repeatable_reads_leave_both_inputs_unchanged(self):
        word = event((1, 0, 2))
        tag_input, binary_input = tag_state(word), cts_state(word)
        for _ in range(3):
            self.assertEqual(reader.read_tag_result(tag_input), (1, 0, 2))
            self.assertEqual(reader.read_cts_result(binary_input), (1, 0, 2))
        self.assertEqual(tag_input, tag_state(word))
        self.assertEqual(binary_input, cts_state(word))


if __name__ == "__main__":
    unittest.main()
