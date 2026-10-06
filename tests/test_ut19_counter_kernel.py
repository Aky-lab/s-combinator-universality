"""Independent raw-production checks of the compact UT19 simulation invariant.

The kernel and whole-pass checks use literal published productions, an explicit
FIFO, and an action-first width encoder. They do not execute the production
encoder or source interpreter. One separate check compares its width vectors.
See docs/ut19-simulation-invariants.md for the all-input algebraic proof.
"""
from collections import deque
from itertools import product
import unittest


RULES = {
    1: (2, 3), 2: (4, 4), 3: (18, 4), 4: (1, 1, 19),
    5: (7, 9), 6: (8, 9), 7: (10, 10), 8: (11, 10),
    9: (18, 10), 10: (5, 6), 11: (6, 5, 19),
    12: (14, 14, 14, 14), 13: (15,), 14: (16, 16),
    15: (16, 17), 16: (12, 13), 17: (12, 12, 12, 12),
    18: (18,), 19: (),
}


def counter(exponent):
    return (12, 13) * (1 << exponent)


def protected(exponent):
    return (12,) * (1 << (exponent + 1))


def raw_pass(word, alignment):
    selected = word[alignment::2]
    return (tuple(child for symbol in selected for child in RULES[symbol]),
            selected, alignment ^ (len(word) & 1))


def raw_counter_cycle(word, command, parity, reset):
    parity_word, command_selected, _ = raw_pass(word, command)
    reset_word, parity_selected, _ = raw_pass(parity_word, parity)
    following, reset_selected, _ = raw_pass(reset_word, reset)
    return following, parity_word, reset_word, (
        command_selected + parity_selected + reset_selected)


def flatten(parts):
    return tuple(symbol for part in parts for symbol in part)


def fifo_pass(parts, alignment):
    """Process exactly the original queue; compare FIFO to component splitting.

    This preserves empty components, which is useful for the deleted halt
    counter. No alignment is manually assigned to an interior component.
    """
    original = flatten(parts)
    queue = deque(original)
    selected = []
    phase = alignment
    for _ in original:
        symbol = queue.popleft()
        if phase == 0:
            selected.append(symbol)
            queue.extend(RULES[symbol])
        phase ^= 1
    next_parts = []
    cursor = alignment
    for part in parts:
        out, _, cursor = raw_pass(part, cursor)
        next_parts.append(out)
    assert tuple(queue) == flatten(next_parts)
    assert phase == cursor
    return tuple(next_parts), phase, tuple(selected)


def actions(count, marker):
    """Desired counter alignments and global Parity phase, by meaning.

    Counters include the halt counter. Widths are recovered as differences
    between adjacent alignments, rather than using the implementation formula.
    """
    number = count + 1
    if marker == "^":
        return ((1, (1,) * number, 0), (0, (0,) * number, 0))
    if marker == "=":
        return ((0, (1,) * number, 0), (0, (0,) * number, 0))
    if marker == "$a":
        return ((0, (1,) * number, 0),
                (0, (0,) * count + (1,), 1))
    if marker == "$b":
        return ((0, (0,) * number, 0), (0, (0,) * number, 0))
    target, delta = marker
    if delta == 1:
        return ((0, (0,) * number, 0),
                (0, tuple(int(k != target) for k in range(1, number + 1)), 0))
    return ((0, (1,) * number, 0),
            (0, tuple(int(k == target) for k in range(1, number + 1)), 0))


def widths_from_actions(start, counter_alignments, next_phase):
    endpoints = (start,) + counter_alignments + (next_phase,)
    return tuple(left ^ right for left, right in zip(endpoints, endpoints[1:]))


def memory_vectors(commands, count):
    expanded = 1
    while expanded < len(commands) + 3:
        expanded *= 2
    markers = ("^",) + tuple(commands) + ("$a", "$b")
    markers += ("=",) * (expanded - len(markers))
    columns = tuple(widths_from_actions(*half)
                    for marker in markers for half in actions(count, marker))
    return tuple(tuple(column[b] for column in columns) for b in range(count + 2))


def initial_memory(desired):
    # Slow direct subset sum, not the production butterfly implementation.
    initial = tuple(sum(desired[j] for j in range(len(desired)) if j & i == i) & 1
                    for i in range(len(desired)))
    return tuple(symbol for bit in initial
                 for symbol in ((5, 6, 1, 1, 19) if bit else (5, 6)))


def initial_parts(commands, values):
    """An epoch-entry invariant state; values need not all be initial zeroes."""
    count = len(values)
    memories = tuple(initial_memory(v) for v in memory_vectors(commands, count))
    parts = []
    for index, memory in enumerate(memories):
        parts.append(memory)
        if index <= count:
            value = values[index] if index < count else 0
            parts.append(counter(2 * value + 1))
    return tuple(parts), memories


def one_half(parts, phase):
    snapshots = []
    phases = [phase]
    selected = []
    for _ in range(3):
        parts, phase, symbols = fifo_pass(parts, phase)
        snapshots.append(parts)
        phases.append(phase)
        selected.extend(symbols)
    return parts, phase, snapshots, tuple(phases), tuple(selected)


class UT19CounterKernelTests(unittest.TestCase):
    def test_increment_all_exponents_and_exterior_alignments(self):
        for exponent in range(11):
            for parity, reset in product((0, 1), repeat=2):
                out, middle, last, selected = raw_counter_cycle(
                    counter(exponent), 0, parity, reset)
                self.assertEqual(middle, (14,) * (1 << (exponent + 2)))
                self.assertEqual(last, (16,) * (1 << (exponent + 2)))
                self.assertEqual(out, counter(exponent + 1))
                self.assertNotIn(18, selected)

    def test_nonzero_decrement_even_and_odd_reset_are_distinct(self):
        for exponent in range(1, 11):
            for parity, reset in product((0, 1), repeat=2):
                out, middle, last, selected = raw_counter_cycle(
                    counter(exponent), 1, parity, reset)
                self.assertEqual(middle, (15,) * (1 << exponent))
                self.assertEqual(last, (16, 17) * (1 << (exponent - 1)))
                self.assertEqual(out, protected(exponent) if reset
                                 else counter(exponent - 1))
                self.assertNotIn(18, selected)
        # The smallest counterexample to an unconditional decrement rule.
        self.assertEqual(raw_counter_cycle(counter(1), 1, 0, 1)[0], (12,) * 4)
        self.assertNotEqual((12,) * 4, counter(0))

    def test_zero_decrement_has_four_exterior_cases(self):
        for parity, reset in product((0, 1), repeat=2):
            out, middle, last, selected = raw_counter_cycle(counter(0), 1, parity, reset)
            self.assertEqual(middle, (15,))
            self.assertEqual(last, () if parity else (16, 17))
            expected = () if parity else ((12,) * 4 if reset else counter(0))
            self.assertEqual(out, expected)
            self.assertNotIn(18, selected)

    def test_protected_counter_increments_under_both_command_alignments(self):
        for exponent in range(9):
            for command, parity, reset in product((0, 1), repeat=3):
                out, middle, last, _ = raw_counter_cycle(
                    protected(exponent), command, parity, reset)
                self.assertEqual(middle, (14,) * (1 << (exponent + 2)))
                self.assertEqual(last, (16,) * (1 << (exponent + 2)))
                self.assertEqual(out, counter(exponent + 1))
        # D = protected(1); dummy decrement then increment restores source 1.
        middle = raw_counter_cycle((12,) * 4, 1, 0, 0)[0]
        self.assertEqual(middle, counter(2))
        self.assertEqual(raw_counter_cycle(middle, 0, 0, 0)[0], counter(3))

    def test_widths_telescope_to_actions_and_published_formula(self):
        for count in range(1, 9):
            for target, delta in product(range(1, count + 1), (-1, 1)):
                for marker in ((target, delta), "^", "=", "$a", "$b"):
                    for half, (start, expected, next_phase) in enumerate(actions(count, marker)):
                        widths = widths_from_actions(start, expected, next_phase)
                        cursor = start
                        recovered = []
                        for bit in widths[:-1]:
                            cursor ^= bit
                            recovered.append(cursor)
                        self.assertEqual(tuple(recovered), expected)
                        self.assertEqual(cursor ^ widths[-1], next_phase)
                        published = []
                        for position in range(1, count + 3):
                            first, last = int(position == 1), int(position == count + 2)
                            if marker == "^":
                                pair = (last, 0)
                            elif marker == "=":
                                pair = (first | last, 0)
                            elif marker == "$b":
                                pair = (0, 0)
                            else:
                                label = count + 1 if marker == "$a" else target
                                adjacent = int(label in (position - 1, position))
                                if marker == "$a":
                                    pair = (first | last, adjacent & (1 - last))
                                elif delta == 1:
                                    pair = (0, adjacent ^ first ^ last)
                                else:
                                    pair = (first | last, adjacent)
                            published.append(pair[half])
                        self.assertEqual(tuple(published), widths)

    def test_production_width_vectors_against_independent_action_encoder(self):
        from s_only import ut19
        for count in range(1, 9):
            for target, delta in product(range(1, count + 1), (-1, 1)):
                commands = ((target, delta),) + tuple((k, 1) for k in range(1, count + 1))
                program = ut19.SourceProgram(tuple(ut19.Command(*c) for c in commands))
                vectors = memory_vectors(commands, count)
                expanded = len(vectors[0]) // 2
                self.assertLessEqual(2 * len(commands) + 3, 2 * expanded - 3)
                for position, desired in enumerate(vectors, 1):
                    self.assertEqual(ut19._widths(program, position, expanded), desired)

    def test_initial_19_sets_odd_command_without_changing_the_pass_output(self):
        parts, _ = initial_parts(((1, 1),), (0,))
        without_prefix, phase, _ = fifo_pass(parts, 1)
        with_prefix, prefixed_phase, selected = fifo_pass(((19,),) + parts, 0)
        self.assertEqual(with_prefix[0], ())
        self.assertEqual(with_prefix[1:], without_prefix)
        self.assertEqual(prefixed_phase, phase)
        self.assertEqual(selected[0], 19)

    def test_all_small_legal_instruction_and_restart_boundaries(self):
        checked = resets = 0
        for count in range(1, 4):
            for values in product(range(3), repeat=count):
                for target, delta in product(range(1, count + 1), (-1, 1)):
                    commands = ((target, delta),) + tuple((k, 1) for k in range(1, count + 1)
                                                         if k != target)
                    parts, memories = initial_parts(commands, values)
                    phase = 1
                    for _ in range(2):  # Initial/restart dummy.
                        parts, phase, _, phases, selected = one_half(parts, phase)
                        self.assertEqual(phases[1:], (0, 0, 0))
                        self.assertNotIn(18, selected)
                    self.assertEqual(parts[1:-1:2], tuple(counter(2 * x + 1)
                                                         for x in values + (0,)))
                    for half in range(2):
                        parts, phase, snapshots, phases, selected = one_half(parts, phase)
                        self.assertEqual(phases[1], 0)
                        self.assertNotIn(18, selected)
                        self.assertTrue(all(len(block) % 2 == 0 for block in snapshots[1]))
                        if half == 0:
                            self.assertEqual(phases[2:], (0, 0))
                    reset = delta == -1 and values[target - 1] == 0
                    expected_values = list(values)
                    expected_values[target - 1] = 1 if reset else values[target - 1] + delta
                    self.assertEqual(phase, int(reset))
                    self.assertEqual(phases[2:], (int(reset), int(reset)))
                    if reset:
                        resets += 1
                        self.assertEqual(parts[::2], memories)
                        expected_counters = tuple((12,) * 4 if k == target else counter(2 * x + 1)
                                                  for k, x in enumerate(values + (0,), 1))
                        self.assertEqual(parts[1:-1:2], expected_counters)
                        for _ in range(2):
                            parts, phase, _, phases, selected = one_half(parts, phase)
                            self.assertEqual(phases[1:], (0, 0, 0))
                            self.assertNotIn(18, selected)
                    self.assertEqual(parts[1:-1:2], tuple(counter(2 * x + 1)
                                                         for x in tuple(expected_values) + (0,)))
                    checked += 1
        self.assertEqual(checked, 204)
        self.assertEqual(resets, 34)

    def test_first_halt_event_preserves_all_counter_output_runs(self):
        checked = 0
        for count in range(1, 4):
            commands = tuple((k, 1) for k in range(1, count + 1))
            for starting in product(range(3), repeat=count):
                parts, memories = initial_parts(commands, starting)
                phase = 1
                # Dummy, then the actual source commands, then $a's first half.
                for _ in range(2 + 2 * len(commands) + 1):
                    parts, phase, _, phases, selected = one_half(parts, phase)
                    self.assertEqual(phases[1:], (0, 0, 0))
                    self.assertNotIn(18, selected)
                self.assertEqual(parts[-2], counter(0))
                parity_parts, phase, selected = fifo_pass(parts, phase)
                self.assertEqual(phase, 1)
                self.assertNotIn(18, selected)
                self.assertEqual(parity_parts[-2], (15,))
                reset_parts, phase, selected = fifo_pass(parity_parts, phase)
                self.assertEqual(phase, 0)
                self.assertNotIn(18, selected)
                self.assertNotIn(15, selected)  # Halt singleton is skipped.
                self.assertEqual(reset_parts[-2], ())
                queue = flatten(reset_parts)
                self.assertEqual(queue[0], 18)  # First event is the next microstep.
                self.assertTrue(set(queue) <= {4, 10, 11, 16, 18})
                results = tuple(x + 1 for x in starting)
                expected_runs = tuple((16,) * (4 ** (x + 1)) for x in results)
                self.assertEqual(reset_parts[1:-2:2], expected_runs)
                self.assertTrue(all(len(part) % 2 == 0 for part in reset_parts))
                for memory in reset_parts[:-2:2]:
                    self.assertEqual(set(memory[::2]), {18})
                    self.assertTrue(set(memory[1::2]) <= {4, 10})
                self.assertTrue(set(reset_parts[-1]) <= {4, 10, 11})
                # A bounded structural read of maximal 16-runs needs no replay.
                runs, run = [], 0
                for symbol in queue + (0,):
                    if symbol == 16:
                        run += 1
                    elif run:
                        runs.append(run)
                        run = 0
                self.assertEqual(tuple(runs), tuple(4 ** (x + 1) for x in results))
                # The one-hot event has consumed exactly 17 leading zero bits.
                encoded = "".join("0" * (s - 1) + "1" + "0" * (19 - s) for s in queue)
                event_word = encoded[17:]
                self.assertTrue(event_word.startswith("10"))
                self.assertEqual("0" * 17 + event_word, encoded)
                checked += 1
        self.assertEqual(checked, 39)

    def test_zero_outputs_from_canonical_zero_start(self):
        for count in range(1, 4):
            commands = tuple((k, delta) for delta in (1, -1) for k in range(1, count + 1))
            parts, _ = initial_parts(commands, (0,) * count)
            phase = 1
            for _ in range(2 + 2 * len(commands) + 1):
                parts, phase, _, phases, selected = one_half(parts, phase)
                self.assertEqual(phases[1:], (0, 0, 0))
                self.assertNotIn(18, selected)
            for expected_phase in (1, 0):
                parts, phase, selected = fifo_pass(parts, phase)
                self.assertEqual(phase, expected_phase)
                self.assertNotIn(18, selected)
            self.assertEqual(parts[0][0], 18)
            self.assertEqual(parts[1:-2:2], ((16,) * 4,) * count)
            self.assertEqual(parts[-2], ())


if __name__ == "__main__":
    unittest.main()
