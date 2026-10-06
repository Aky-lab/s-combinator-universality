"""Independent bounded source semantics, subset-XOR and literal seed oracles."""
from dataclasses import FrozenInstanceError, replace
from itertools import product
import unittest
from unittest.mock import patch

from s_only import alternating_tag as tag
from s_only import cts, ut19

# Numerical primary table, independently transcribed for an oracle.
ROWS = ((2, 3), (4, 4), (18, 4), (1, 1, 19), (7, 9), (8, 9),
        (10, 10), (11, 10), (18, 10), (5, 6), (6, 5, 19),
        (14, 14, 14, 14), (15,), (16, 16), (16, 17), (12, 13),
        (12, 12, 12, 12), (18,), ())
SEED_BLOCKS = {
    "+1": (("00001000", "10001000"), ("00010100", "00111100"), ("10011000", "11111000")),
    "-1": (("00111000", "11011000"), ("00010100", "00111100"), ("10101000", "10101000")),
    "-1 -1": (("0011111000101010", "0011110010000010"),
              ("0001010100000000", "1100001100000000"),
              ("1010101000101010", "1000000010000010")),
}


def literal_seed(text):
    queue = [19]
    for block, (_, bits) in enumerate(SEED_BLOCKS[text]):
        for bit in bits:
            queue += [5, 6] + ([1, 1, 19] if bit == "1" else [])
        if block < 2:
            queue += [12, 13, 12, 13]
    return tuple(queue)


def literal_encode(queue):
    return "".join("1" if symbol == offset else "0"
                   for symbol in queue for offset in range(1, 20))


class UT19Tests(unittest.TestCase):
    def test_published_table_and_exact_fixed_cts(self):
        self.assertEqual(ut19.UT19_PRODUCTIONS, ROWS)
        self.assertEqual(ut19.TAG_PROGRAM.productions,
                         tuple(tuple(x - 1 for x in row) for row in ROWS))
        appendants = ut19.compile_cts().appendants
        self.assertEqual(appendants, tuple(literal_encode(row) for row in ROWS) + ("",) * 19)
        self.assertEqual((len(appendants), sum(bool(x) for x in appendants),
                          sum(map(len, appendants)), sum(x.count("1") for x in appendants),
                          max(map(len, appendants))), (38, 18, 760, 40, 76))
        for kwargs in ({"max_phases": 37}, {"max_program_bits": 759}):
            with self.assertRaises(cts.ResourceLimit):
                ut19.compile_cts(**kwargs)

    def test_rx_matches_subset_oracle_temporal_oracle_and_involution(self):
        for length in (1, 2, 4, 8):
            for vector in product((0, 1), repeat=length):
                expected = tuple(sum(vector[j] for j in range(length) if i & j == i) % 2
                                 for i in range(length))
                actual = ut19.running_xor_initial(vector, max_entries=length)
                self.assertEqual(actual, expected)
                self.assertEqual(ut19.running_xor_initial(actual, max_entries=length), vector)
                # Independently simulate simultaneous running-XOR cell updates.
                current, outputs = list(actual), []
                for _ in range(length):
                    outputs.append(sum(current) % 2)
                    current = [sum(current[:i + 1]) % 2 for i in range(length)]
                self.assertEqual(tuple(outputs), vector)

    def test_literal_seed_vectors_sizes_and_generic_conversion(self):
        for text, blocks in SEED_BLOCKS.items():
            encoded = ut19.encode_source(ut19.parse_source(text))
            self.assertEqual(encoded.queue, literal_seed(text))
            for actual, (desired, initial) in zip(encoded.blocks, blocks):
                self.assertEqual("".join(map(str, actual.desired)), desired)
                self.assertEqual("".join(map(str, actual.initial)), initial)
            symbols = 144 if text == "-1 -1" else 90
            self.assertEqual((encoded.seed_symbols, encoded.seed_bits), (symbols, 19 * symbols))
            self.assertEqual(encoded.cts_configuration(max_word_bits=19 * symbols),
                             cts.Configuration(literal_encode(literal_seed(text)), 0))
            self.assertEqual(encoded.tag_configuration(max_queue_symbols=symbols),
                             tag.Configuration(tuple(x - 1 for x in literal_seed(text)), tag.TAKE))
            with self.assertRaises(cts.ResourceLimit):
                encoded.cts_configuration(max_word_bits=19 * symbols - 1)
            with self.assertRaises(cts.ResourceLimit):
                encoded.tag_configuration(max_queue_symbols=symbols - 1)

    def test_size_formula_over_small_dense_programs(self):
        for length in range(1, 5):
            for signed in product((1, -1, 2, -2), repeat=length):
                if set(map(abs, signed)) != set(range(1, max(map(abs, signed)) + 1)):
                    continue
                program = ut19.SourceProgram(tuple(ut19.Command(abs(x), 1 if x > 0 else -1)
                                                   for x in signed))
                encoded = ut19.encode_source(program)
                count, expanded = program.counter_count, encoded.expanded_commands
                self.assertGreaterEqual(expanded, length + 3)
                self.assertLess(expanded // 2, length + 3)
                inverters = sum(sum(block.initial) for block in encoded.blocks)
                exact = 1 + 4 * (count + 1) + 4 * expanded * (count + 2) + 3 * inverters
                self.assertEqual(encoded.seed_symbols, exact)
                self.assertLessEqual(exact, 1 + 4 * (count + 1) + 10 * expanded * (count + 2))

    def test_source_semantics_restart_halt_and_no_counter_reset(self):
        cases = {
            "+1": [(0, (0,)), (1, (1,))],
            "-1": [(0, (0,)), (0, (1,)), (1, (0,))],
            "+1 -1": [(0, (0,)), (1, (1,)), (2, (0,))],
            "+1 -2": [(0, (0, 0)), (1, (1, 0)), (0, (1, 1)), (1, (2, 1)), (2, (2, 0))],
        }
        for text, expected in cases.items():
            program = ut19.parse_source(text)
            state = ut19.initial_source(program, max_counters=2)
            self.assertEqual(state, ut19.SourceConfiguration(*expected[0]))
            for pair in expected[1:]:
                state = ut19.source_step(program, state, max_counters=2, max_counter_value=2)
                self.assertEqual(state, ut19.SourceConfiguration(*pair))
            with self.assertRaises(StopIteration):
                ut19.source_step(program, state, max_counters=2, max_counter_value=2)
        program = ut19.parse_source("-1 -1")
        state = ut19.initial_source(program, max_counters=1)
        observed = []
        for _ in range(7):
            observed.append(state)
            state = ut19.source_step(program, state, max_counters=1, max_counter_value=1)
        self.assertEqual(observed[1], observed[3])
        self.assertEqual(observed[1], observed[5])
        self.assertEqual(observed[2], observed[4])

    def test_source_step_limits_are_before_mutation(self):
        for text in ("+1", "-1"):
            program = ut19.parse_source(text)
            state = ut19.initial_source(program, max_counters=1)
            with self.assertRaises(cts.ResourceLimit):
                ut19.source_step(program, state, max_counters=1, max_counter_value=0)
            self.assertEqual(state, ut19.SourceConfiguration(0, (0,)))
        with self.assertRaises(cts.ResourceLimit):
            ut19.initial_source(ut19.parse_source("+1 -2"), max_counters=1)
        with self.assertRaises(cts.ResourceLimit):
            ut19.source_step(ut19.parse_source("+1"), ut19.SourceConfiguration(0, (2,)),
                             max_counters=1, max_counter_value=1)

    def test_encoder_preflights_before_vectors_or_seed_allocation(self):
        program = ut19.parse_source("+1")
        for changed in ({"max_commands": 0}, {"max_counters": 0},
                        {"max_memory_entries": 23}, {"max_seed_symbols": 56},
                        {"max_seed_bits": 1082}):
            with patch.object(ut19, "_widths", side_effect=AssertionError("allocated vector")):
                with self.assertRaises(cts.ResourceLimit):
                    ut19.encode_source(program, limits=replace(ut19.EncodingLimits(), **changed))
        for changed in ({"max_seed_symbols": 89}, {"max_seed_bits": 1709}):
            with patch.object(ut19, "_materialize_seed", side_effect=AssertionError("allocated seed")):
                with self.assertRaises(cts.ResourceLimit):
                    ut19.encode_source(program, limits=replace(ut19.EncodingLimits(), **changed))
        limits = ut19.EncodingLimits(max_commands=1, max_counters=1, max_memory_entries=24,
                                    max_seed_symbols=90, max_seed_bits=1710)
        self.assertEqual(ut19.encode_source(program, limits=limits).seed_symbols, 90)

    def test_event_is_pretransition_take_head_only(self):
        self.assertTrue(ut19.selected_source_event(tag.Configuration((17,), tag.TAKE)))
        for state in (tag.Configuration((), tag.TAKE), tag.Configuration((17,), tag.SKIP),
                      tag.Configuration((0, 17), tag.TAKE), tag.Configuration((18,), tag.TAKE)):
            self.assertFalse(ut19.selected_source_event(state))
        initial = tag.Configuration((17,), tag.TAKE)
        self.assertEqual(tag.step(ut19.TAG_PROGRAM, initial, max_queue_symbols=1),
                         tag.Configuration((17,), tag.SKIP))
        # Native singleton event production does not itself stop the queue.
        next_state = tag.step(ut19.TAG_PROGRAM, initial, max_queue_symbols=1)
        self.assertEqual(tag.step(ut19.TAG_PROGRAM, next_state, max_queue_symbols=1),
                         tag.Configuration((), tag.TAKE))

    def test_subclass_inputs_cannot_bypass_immutable_preflight(self):
        class MutableCommand(ut19.Command):
            pass
        class MutableProgram(ut19.SourceProgram):
            pass
        class MutableState(ut19.SourceConfiguration):
            pass
        class MutableLimits(ut19.EncodingLimits):
            pass
        with self.assertRaises(ValueError):
            ut19.SourceProgram((MutableCommand(1, 1),))
        program = ut19.parse_source("+1")
        evil_program = MutableProgram(program.commands)
        object.__setattr__(evil_program, "changes", [])
        for function in (lambda: ut19.encode_source(evil_program),
                         lambda: ut19.initial_source(evil_program, max_counters=1),
                         lambda: ut19.source_step(evil_program, ut19.SourceConfiguration(0, (0,)),
                                                  max_counters=1, max_counter_value=1),
                         lambda: ut19.source_step(program, MutableState(0, (0,)),
                                                  max_counters=1, max_counter_value=1),
                         lambda: ut19.encode_source(program, limits=MutableLimits())):
            with self.assertRaises(ValueError):
                function()

    def test_strict_validation_and_immutability(self):
        for args in ((0, 1), (-1, 1), (True, 1), (1, 0), (1, True), (1, 1.0)):
            with self.assertRaises(ValueError):
                ut19.Command(*args)
        for commands in ([], (), (1,), (ut19.Command(2, 1),),
                         (ut19.Command(10**100, 1),)):
            with self.assertRaises(ValueError):
                ut19.SourceProgram(commands)
        for args in ((-1, (0,)), (True, (0,)), (0, [0]), (0, (True,)), (0, (-1,))):
            with self.assertRaises(ValueError):
                ut19.SourceConfiguration(*args)
        for text in ("", " ", "1", "+0", "-0", "+01", "+1x", "++1", "+1-1", "+2"):
            with self.assertRaises(ValueError):
                ut19.parse_source(text)
        for kwargs in ({"max_chars": 1}, {"max_commands": 0}, {"max_counters": 0}):
            with self.assertRaises(cts.ResourceLimit):
                ut19.parse_source("+1", **kwargs)
        with self.assertRaises(cts.ResourceLimit):
            ut19.parse_source("+" + "9" * 10000)
        for vector in ((), (0, 1, 0), [0, 1], (False,), (2,)):
            with self.assertRaises(ValueError):
                ut19.running_xor_initial(vector, max_entries=8)
        with self.assertRaises(cts.ResourceLimit):
            ut19.running_xor_initial((0, 1), max_entries=1)
        for name in ut19.EncodingLimits.__dataclass_fields__:
            for invalid in (-1, True, 1.0):
                with self.assertRaises(ValueError):
                    ut19.EncodingLimits(**{name: invalid})
        command = ut19.Command(1, 1)
        with self.assertRaises(FrozenInstanceError):
            command.counter = 2
        state = ut19.SourceConfiguration(0, (0,))
        with self.assertRaises(FrozenInstanceError):
            state.pc = 1
        for state in (ut19.SourceConfiguration(2, (0,)), ut19.SourceConfiguration(0, (0, 0))):
            with self.assertRaises(ValueError):
                ut19.source_step(ut19.parse_source("+1"), state, max_counters=2, max_counter_value=10)


if __name__ == "__main__":
    unittest.main()
