"""Ordinary CTS semantics tested without any source-machine halt convention."""
from itertools import product
import unittest

from s_only.cts import Configuration, Machine, Program, ResourceLimit, step


class CyclicTagTests(unittest.TestCase):
    def test_thesis_definition_4_2_2_example(self):
        program = Program(("001", "01", "11"))
        state = Configuration("011")
        observed = []
        for _ in range(4):
            state = step(program, state)
            observed.append((state.phase, state.word))
        self.assertEqual(observed, [(1, "11"), (2, "101"), (0, "0111"), (1, "111")])

    def test_both_bits_advance_phase(self):
        for bit in ("0", "1"):
            state = step(Program(("11", "0")), Configuration(bit, 1))
            self.assertEqual(state.phase, 0)
            self.assertEqual(state.word, "0" if bit == "1" else "")

    def test_all_short_programs_against_list_interpreter(self):
        # Deliberately uses neither production step() nor deque operations.
        words = ("", "0", "1", "00", "01", "10", "11")
        for appendants in product(words, repeat=2):
            for seed in words:
                machine = Machine(Program(appendants), Configuration(seed),
                                  max_steps=16, max_word_bits=64)
                queue, phase = list(seed), 0
                for count in range(16):
                    if not queue:
                        with self.assertRaises(StopIteration):
                            machine.tick()
                        break
                    first, queue = queue[0], queue[1:]
                    appended = appendants[phase] if first == "1" else ""
                    queue = queue + list(appended)
                    event = machine.tick()
                    self.assertEqual((event.step, event.phase, event.deleted, event.appended),
                                     (count + 1, phase, first, appended))
                    phase = (phase + 1) % 2
                    self.assertEqual(machine.snapshot(), Configuration("".join(queue), phase))

    def test_recurrence_is_not_empty_queue_or_halt_event(self):
        machine = Machine(Program(("1",)), Configuration("1"), max_steps=4, max_word_bits=1)
        before = machine.snapshot()
        for _ in range(4):
            self.assertEqual(machine.tick().appended, "1")
            self.assertEqual(machine.snapshot(), before)
        with self.assertRaises(ResourceLimit):
            machine.tick()
        self.assertEqual(machine.word_bits, 1)

    def test_step_limit_is_transactional(self):
        machine = Machine(Program(("1",)), Configuration("1"), max_steps=0, max_word_bits=1)
        with self.assertRaises(ResourceLimit):
            machine.tick()
        self.assertEqual(machine.snapshot(), Configuration("1"))
        self.assertEqual(machine.steps, 0)

    def test_size_limit_is_transactional(self):
        machine = Machine(Program(("111", "")), Configuration("10"), max_steps=10, max_word_bits=3)
        with self.assertRaises(ResourceLimit):
            machine.tick()
        self.assertEqual(machine.snapshot(), Configuration("10"))
        self.assertEqual(machine.steps, 0)

    def test_empty_queue_has_no_step_even_at_limit(self):
        machine = Machine(Program(("",)), Configuration(""), max_steps=0, max_word_bits=0)
        with self.assertRaises(StopIteration):
            machine.tick()
        with self.assertRaises(StopIteration):
            step(machine.program, machine.snapshot())

    def test_program_and_state_validation(self):
        for appendants in ((), [], ("2",), (0,)):
            with self.assertRaises(ValueError):
                Program(appendants)
        for word in ("2", "01\n", [0, 1], 1):
            with self.assertRaises(ValueError):
                Configuration(word)
        for phase in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                Configuration("1", phase)
        with self.assertRaises(ValueError):
            step(Program(("",)), Configuration("1", 1))
        with self.assertRaises(ValueError):
            Machine(Program(("",)), Configuration("1", 1), max_steps=1, max_word_bits=1)
        with self.assertRaises(ResourceLimit):
            Machine(Program(("",)), Configuration("11"), max_steps=1, max_word_bits=1)
        for key in ("max_steps", "max_word_bits"):
            for value in (-1, True, 1.5):
                limits = {"max_steps": 2, "max_word_bits": 2, key: value}
                with self.assertRaises(ValueError):
                    Machine(Program(("",)), Configuration("1"), **limits)


if __name__ == "__main__":
    unittest.main()
