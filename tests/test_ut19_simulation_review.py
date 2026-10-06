"""Independent review regressions, not a substitute for the all-input proof.

These cover the last protected clock observations, exact event memory grammar,
the phase-17 decoder offset, and input-computable bounds beyond default caps.
Only the seed encoder and generic boundary decoder are imported as subjects.
"""
from collections import deque
import unittest

from s_only import alternating_tag as tag
from s_only import cts, ut19


ROWS = ((2, 3), (4, 4), (18, 4), (1, 1, 19), (7, 9), (8, 9),
        (10, 10), (11, 10), (18, 10), (5, 6), (6, 5, 19),
        (14, 14, 14, 14), (15,), (16, 16), (16, 17),
        (12, 13), (12, 12, 12, 12), (18,), ())


def hot(word):
    return "".join("0" * (symbol - 1) + "1" + "0" * (19 - symbol)
                   for symbol in word)


class UT19SimulationReviewTests(unittest.TestCase):
    def first_event(self, source, max_passes):
        encoded = ut19.encode_source(ut19.parse_source(source))
        queue = deque(encoded.queue)
        self.assertEqual(queue.popleft(), 19)
        alignment, steps = 1, 1  # The leading 19 is taken and produces nothing.
        for passes in range(max_passes + 1):
            self.assertTrue(queue)
            if alignment == 0 and queue[0] == 18:
                return encoded, tuple(queue), passes, steps
            if passes == max_passes:
                self.fail("event not reached within the independent pass cap")
            for _ in range(len(queue)):
                self.assertTrue(queue)
                head = queue.popleft()
                if alignment == 0:
                    # A first event inside a pass would contradict the theorem.
                    self.assertNotEqual(head, 18)
                    queue.extend(ROWS[head - 1])
                alignment ^= 1
                steps += 1
                self.assertLess(len(queue), 100_000)

    def check_event_grammar(self, encoded, word, values):
        cursor = 0
        for index, block in enumerate(encoded.blocks[:-1]):
            expected = tuple(symbol for bit in block.initial
                             for symbol in ((18, 10, 18, 4) if bit else (18, 10)))
            self.assertEqual(word[cursor:cursor + len(expected)], expected)
            cursor += len(expected)
            if index < len(values):
                expected = (16,) * (4 ** (values[index] + 1))
                self.assertEqual(word[cursor:cursor + len(expected)], expected)
                cursor += len(expected)
        # The halt counter has vanished; final-memory cells have normal pairs.
        for bit in encoded.blocks[-1].initial:
            self.assertIn(word[cursor], (10, 11))
            self.assertEqual(word[cursor + 1], 10)
            cursor += 2
            if bit:
                self.assertEqual(word[cursor:cursor + 2], (4, 4))
                cursor += 2
        self.assertEqual(cursor, len(word))

        # Execute the 17 actual ordinary CTS zero steps at the tag event.
        binary, phase = hot(word), 0
        for _ in range(17):
            self.assertEqual(binary[0], "0")
            binary, phase = binary[1:], phase + 1
        self.assertEqual(phase, 17)
        self.assertTrue(binary.startswith("10"))
        event = cts.Configuration(binary, phase)
        with self.assertRaises(ValueError):
            tag.decode_boundary(ut19.TAG_PROGRAM, event,
                                max_word_bits=19 * len(word),
                                max_queue_symbols=len(word))
        restored = cts.Configuration("0" * 17 + binary, 0)
        decoded = tag.decode_boundary(ut19.TAG_PROGRAM, restored,
                                      max_word_bits=19 * len(word),
                                      max_queue_symbols=len(word))
        self.assertEqual(decoded.queue, tuple(symbol - 1 for symbol in word))
        self.assertEqual(decoded.phase, tag.TAKE)

    def test_late_restart_and_last_protected_clock_observations(self):
        # L = N-3 makes the final halt observation exactly W-3. The last source
        # command fails once, resets the memory, and succeeds on its next visit.
        for length in (1, 5, 13, 29):
            source = "-1" if length == 1 else " ".join(
                ["+1", "-1"] * ((length - 1) // 2) + ["-2"])
            expected_passes = 12 * length + 17
            encoded, word, passes, _ = self.first_event(source, expected_passes)
            self.assertEqual(passes, expected_passes)
            self.assertEqual(2 * length + 3, 2 * encoded.expanded_commands - 3)
            values = (0,) if length == 1 else (0, 0)
            self.check_event_grammar(encoded, word, values)

    def test_restart_preserves_other_counter_and_exact_output_grammar(self):
        # Restart targets on both sides of the ordinary counter list.
        for source, values, passes in (("+1 -2", (2, 0), 41),
                                        ("-1 +2", (0, 1), 35)):
            encoded, word, actual, _ = self.first_event(source, passes)
            self.assertEqual(actual, passes)
            self.check_event_grammar(encoded, word, values)

    def test_encoder_beyond_default_cap_uses_only_static_input_bounds(self):
        length = 257
        source = " ".join(["+1", "-1"] * 128 + ["+1"])
        program = ut19.parse_source(source, max_commands=length)
        with self.assertRaises(cts.ResourceLimit):
            ut19.encode_source(program)
        expanded = 1
        while expanded < length + 3:
            expanded *= 2
        count = 1
        entries = 2 * expanded * (count + 2)
        symbol_bound = 1 + 4 * (count + 1) + 10 * expanded * (count + 2)
        limits = ut19.EncodingLimits(
            max_commands=length, max_counters=count, max_memory_entries=entries,
            max_seed_symbols=symbol_bound, max_seed_bits=19 * symbol_bound)
        encoded = ut19.encode_source(program, limits=limits)
        self.assertEqual(encoded.expanded_commands, expanded)
        self.assertLessEqual(encoded.seed_symbols, symbol_bound)
        self.assertEqual(encoded.cts_configuration(max_word_bits=19 * symbol_bound),
                         cts.Configuration(hot(encoded.queue), 0))
        # Check the larger butterfly against a direct subset-sum specification.
        for block in encoded.blocks:
            expected = tuple(sum(block.desired[j] for j in range(2 * expanded)
                                 if j & i == i) % 2 for i in range(2 * expanded))
            self.assertEqual(block.initial, expected)


if __name__ == "__main__":
    unittest.main()
