"""Independent UT19 running-XOR kernel checks; no production-code imports.

Source component rules: https://esolangs.org/wiki/UT19#Program_memory (CC0).
See docs/running-xor-memory.md for pass-alignment assumptions and time indices.
All observations occur BEFORE the next prefix update.
"""
from itertools import product
from math import comb
import unittest


# Only the memory/inverter alphabet is needed. These are literal source rules,
# not rules obtained from an encoder or from a production tag-system module.
RULES = {
    1: (2, 3), 2: (4, 4), 3: (18, 4), 4: (1, 1, 19),
    5: (7, 9), 6: (8, 9), 7: (10, 10), 8: (11, 10),
    9: (18, 10), 10: (5, 6), 11: (6, 5, 19), 18: (18,), 19: (),
}


def vectors(width):
    return product((0, 1), repeat=width)


def xor(left, right):
    return tuple(a ^ b for a, b in zip(left, right))


def prefix_step(state, incoming=0):
    result = []
    carry = incoming
    for bit in state:
        carry ^= bit
        result.append(carry)
    return tuple(result)


def trajectory(initial, forcing):
    """len(forcing)+1 outputs, including the final post-update boundary."""
    state = initial
    result = [sum(state) & 1]
    for incoming in forcing:
        state = prefix_step(state, incoming)
        result.append(sum(state) & 1)
    return tuple(result)


def supermask_transform(bits):
    return tuple(sum(value for j, value in enumerate(bits) if j & i == i) & 1
                 for i in range(len(bits)))


def butterfly_transform(bits):
    """Independently implemented fast transform, for power-of-two lengths."""
    width = len(bits)
    if not width or width & (width - 1):
        raise ValueError("positive power-of-two width required")
    result = list(bits)
    stride = 1
    while stride < width:
        for base in range(0, width, 2 * stride):
            for offset in range(stride):
                result[base + offset] ^= result[base + stride + offset]
        stride *= 2
    return tuple(result)


def block_word(dynamic, inverters):
    result = []
    for bit, inverter in zip(dynamic, inverters):
        result.extend((6, 5, 19) if bit else (5, 6))
        if inverter:
            result.extend((1, 1, 19))
    return tuple(result)


def raw_pass(word, incoming):
    """Restrict a complete alternating pass to this block, given alignment.

    This is not an execution of the block as a standalone tag queue. The
    enclosing queue supplies each pass's incoming alignment. Record selected
    symbols separately so a merely present 18 is not treated as a halt event.
    """
    selected = tuple(symbol for index, symbol in enumerate(word)
                     if (index + incoming) % 2 == 0)
    output = tuple(child for symbol in selected for child in RULES[symbol])
    return output, selected, incoming ^ (len(word) & 1)


def raw_cycle(word, command_alignment, parity_alignment, reset_alignment):
    parity_word, command_selected, command_out = raw_pass(word, command_alignment)
    reset_word, parity_selected, parity_out = raw_pass(parity_word, parity_alignment)
    next_word, reset_selected, reset_out = raw_pass(reset_word, reset_alignment)
    return (next_word, parity_word, reset_word,
            (command_selected, parity_selected, reset_selected),
            (command_out, parity_out, reset_out))


def identity(width):
    return tuple(tuple(int(i == j) for j in range(width)) for i in range(width))


def prefix_matrix(width):
    return tuple(tuple(int(j <= i) for j in range(width)) for i in range(width))


def matrix_product(left, right):
    width = len(left)
    return tuple(tuple(sum(left[i][k] * right[k][j] for k in range(width)) & 1
                       for j in range(width)) for i in range(width))


def matrix_vector(matrix, state):
    return tuple(sum(a * b for a, b in zip(row, state)) & 1 for row in matrix)


def forced_formula(initial, forcing):
    width = len(initial)
    unforced = supermask_transform(initial)
    return tuple(unforced[t % width] ^
                 (sum(forcing[k] for k in range(t) if (t - k) % width == 0) & 1)
                 for t in range(len(forcing) + 1))


class RunningXorMemoryTests(unittest.TestCase):
    def test_literal_normal_cycle_all_small_states_and_alignments(self):
        checked = 0
        for width in range(1, 5):
            for dynamic in vectors(width):
                for inverters in vectors(width):
                    combined = xor(dynamic, inverters)
                    word = block_word(dynamic, inverters)
                    self.assertEqual(len(word) & 1, sum(combined) & 1)
                    for incoming in (0, 1):
                        next_word, parity_word, reset_word, selected, outgoing = raw_cycle(
                            word, incoming, 0, 0)
                        expected = xor(prefix_step(combined, incoming), inverters)
                        self.assertEqual(next_word, block_word(expected, inverters))
                        self.assertEqual(len(parity_word), 2 * (width + sum(inverters)))
                        self.assertEqual(len(reset_word), len(parity_word))
                        self.assertEqual(outgoing, (incoming ^ (len(word) & 1), 0, 0))
                        self.assertNotIn(18, sum(selected, ()))
                        checked += 1
        self.assertEqual(checked, 680)

    def test_literal_reset_wipes_dynamic_state_but_preserves_inverters(self):
        checked = 0
        for width in range(1, 5):
            for dynamic in vectors(width):
                for inverters in vectors(width):
                    for incoming, parity_alignment in product((0, 1), repeat=2):
                        result, parity_word, reset_word, selected, outgoing = raw_cycle(
                            block_word(dynamic, inverters), incoming, parity_alignment, 1)
                        self.assertEqual(result, block_word((0,) * width, inverters))
                        self.assertEqual(len(parity_word), 2 * (width + sum(inverters)))
                        self.assertEqual(len(reset_word), len(parity_word))
                        self.assertEqual(outgoing[1:], (parity_alignment, 1))
                        self.assertNotIn(18, sum(selected, ()))
                        self.assertEqual(18 in reset_word, bool(parity_alignment))
                        checked += 1
        self.assertEqual(checked, 1360)

    def test_odd_parity_even_reset_selects_halt_instead_of_updating_memory(self):
        checked = 0
        for width in range(1, 5):
            for dynamic in vectors(width):
                for inverters in vectors(width):
                    for incoming in (0, 1):
                        result, _, _, selected, _ = raw_cycle(
                            block_word(dynamic, inverters), incoming, 1, 0)
                        self.assertNotIn(18, selected[0] + selected[1])
                        self.assertEqual(selected[2], (18,) * (width + sum(inverters)))
                        # This is the formal continued production word; an
                        # event-halting machine would stop at the first 18.
                        self.assertEqual(result, selected[2])
                        checked += 1
        self.assertEqual(checked, 680)

    def test_all_small_initializers_and_independent_butterfly(self):
        checked = 0
        for width in (1, 2, 4, 8):
            for desired in vectors(width):
                initial = supermask_transform(desired)
                self.assertEqual(butterfly_transform(desired), initial)
                self.assertEqual(supermask_transform(initial), desired)
                self.assertEqual(trajectory(initial, (0,) * (width - 1)), desired)
                checked += 1
        self.assertEqual(checked, 278)
        for width in (0, 3, 5, 6, 7):
            with self.assertRaises(ValueError):
                butterfly_transform((0,) * width)

    def test_dense_matrix_oracle_matches_binomial_output_coefficients(self):
        # Dense multiplication does not call the prefix update or transform.
        for width in range(1, 17):
            matrix = prefix_matrix(width)
            power = identity(width)
            for time in range(3 * width + 1):
                coefficients = tuple(sum(row[i] for row in power) & 1
                                     for i in range(width))
                binomial = tuple(comb(time + width - 1 - i, width - 1 - i) & 1
                                 for i in range(width))
                self.assertEqual(coefficients, binomial, (width, time))
                if width & (width - 1) == 0:
                    supersets = tuple(int(i & (time % width) == time % width)
                                      for i in range(width))
                    self.assertEqual(coefficients, supersets, (width, time))
                    if time % width == 0:
                        self.assertEqual(power, identity(width), (width, time))
                power = matrix_product(matrix, power)

    def test_dense_matrix_oracle_matches_all_small_forced_steps(self):
        for width in range(1, 9):
            matrix = prefix_matrix(width)
            for state in vectors(width):
                for incoming in (0, 1):
                    expected = xor(matrix_vector(matrix, state), (incoming,) * width)
                    self.assertEqual(prefix_step(state, incoming), expected)

    def test_exhaustive_forcing_histories_through_two_widths(self):
        checked = 0
        for width in (1, 2, 4):
            for initial in vectors(width):
                for forcing in vectors(2 * width):
                    observed = trajectory(initial, forcing)
                    self.assertEqual(observed, forced_formula(initial, forcing))
                    self.assertEqual(observed[:width], supermask_transform(initial))
                    checked += 1
        self.assertEqual(checked, 4168)

    def test_exhaustive_width_eight_protected_window_and_exact_boundary(self):
        checked = 0
        width = 8
        for initial in vectors(width):
            desired = supermask_transform(initial)
            for forcing in vectors(width):
                observed = trajectory(initial, forcing)
                self.assertEqual(observed[:width], desired)
                self.assertEqual(observed[width], desired[0] ^ forcing[0])
                checked += 1
        self.assertEqual(checked, 65536)

    def test_raw_productions_match_forced_kernel_through_first_boundary(self):
        checked = 0
        for width in (1, 2, 4):
            for inverters in vectors(width):
                for forcing in vectors(width):
                    word = block_word((0,) * width, inverters)
                    state = inverters
                    observed = []
                    for incoming in forcing:
                        observed.append(len(word) & 1)
                        word, _, _, selected, _ = raw_cycle(word, incoming, 0, 0)
                        self.assertNotIn(18, sum(selected, ()))
                        state = prefix_step(state, incoming)
                        self.assertEqual(word, block_word(xor(state, inverters), inverters))
                    observed.append(len(word) & 1)
                    self.assertEqual(tuple(observed), forced_formula(inverters, forcing))
                    checked += 1
        self.assertEqual(checked, 276)

    def test_single_input_impulse_is_visible_at_width_and_every_width_later(self):
        for width in (1, 2, 4, 8, 16, 32):
            for impulse_time in (0, 1, width - 1, width + 1):
                forcing = tuple(int(t == impulse_time)
                                for t in range(impulse_time + 3 * width))
                outputs = trajectory((0,) * width, forcing)
                expected_times = [impulse_time + width * k for k in (1, 2, 3)]
                self.assertEqual([t for t, bit in enumerate(outputs) if bit], expected_times)

    def test_direct_state_flip_has_different_time_origin(self):
        for width in (1, 2, 4, 8, 16, 32):
            outputs = trajectory((1,) * width, (0,) * (3 * width - 1))
            self.assertEqual([t for t, bit in enumerate(outputs) if bit],
                             [width - 1, 2 * width - 1, 3 * width - 1])

    def test_power_of_two_suffix_flip_does_not_affect_the_prefix(self):
        for width in range(1, 18):
            suffix = 1
            while suffix <= width:
                state = (0,) * (width - suffix) + (1,) * suffix
                outputs = trajectory(state, (0,) * (3 * suffix - 1))
                self.assertEqual([t for t, bit in enumerate(outputs) if bit],
                                 [suffix - 1, 2 * suffix - 1, 3 * suffix - 1])
                for _ in range(3 * suffix):
                    self.assertEqual(state[:width - suffix], (0,) * (width - suffix))
                    state = prefix_step(state)
                suffix *= 2

    def test_non_power_of_two_counterexamples(self):
        width_three = trajectory((0, 0, 0), (1, 0, 0))
        self.assertEqual(width_three[:2], (0, 1))
        width_six = trajectory((0,) * 6, (1,) + (0,) * 5)
        self.assertEqual(width_six[:3], (0, 0, 1))
        self.assertEqual(trajectory((1, 0, 0), (0, 0)), (1, 1, 0))
        self.assertEqual(supermask_transform((1, 0, 0)), (1, 0, 0))
        matrix = prefix_matrix(3)
        self.assertNotEqual(matrix_product(matrix_product(matrix, matrix), matrix), identity(3))

    def test_compact_encoder_documented_example_vectors(self):
        examples = (
            ("00001000", "10001000"),
            ("00010100", "00111100"),
            ("10011000", "11111000"),
            ("00111000", "11011000"),
            ("10101000", "10101000"),
            ("0011111000101010", "0011110010000010"),
            ("0001010100000000", "1100001100000000"),
            ("1010101000101010", "1000000010000010"),
        )
        for desired, initial in examples:
            self.assertEqual(supermask_transform(tuple(map(int, desired))),
                             tuple(map(int, initial)))
            self.assertEqual(trajectory(tuple(map(int, initial)), (0,) * (len(initial) - 1)),
                             tuple(map(int, desired)))


if __name__ == "__main__":
    unittest.main()
