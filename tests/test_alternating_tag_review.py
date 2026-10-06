"""Independent longer-trajectory and stopping-boundary translation checks."""
import random
import unittest

from s_only import alternating_tag as tag
from s_only import cts


class AlternatingTagReviewTests(unittest.TestCase):
    def test_longer_alphabets_both_initial_phases_against_literal_bit_loop(self):
        rng = random.Random(381907)
        for case in range(120):
            m = 4 + case % 4
            productions = tuple(tuple(rng.randrange(m) for _ in range(rng.randrange(4)))
                                for _ in range(m))
            source = tag.Program(productions)
            compiled = tag.compile_program(source, max_phases=14, max_program_bits=147)
            queue = [rng.randrange(m) for _ in range(1 + case % 5)]
            taking = bool(case % 2)
            encode = lambda word: ''.join(str(int(k == x)) for x in word for k in range(m))
            bits = list(encode(queue))
            phase = 0 if taking else m
            machine = tag.Machine(source, tag.Configuration(tuple(queue),
                                  tag.TAKE if taking else tag.SKIP),
                                  max_steps=30, max_queue_symbols=100)
            for j in range(30):
                if not queue:
                    self.assertFalse(bits)
                    self.assertEqual(machine.queue_symbols, 0)
                    break
                head = queue[0]
                signals = []
                for offset in range(m):
                    current = cts.Configuration(''.join(bits), phase)
                    for selected in range(m):
                        if tag.selected_cts_event(source, current, selected):
                            signals.append((offset, selected))
                    bit = bits.pop(0)
                    if bit == '1':
                        bits.extend(compiled.appendants[phase])
                    phase = (phase + 1) % (2 * m)
                self.assertEqual(signals, [(head, head)] if taking else [])
                queue = queue[1:] + (list(productions[head]) if taking else [])
                taking = not taking
                event = machine.tick()
                self.assertEqual(machine.snapshot().queue, tuple(queue))
                self.assertEqual(''.join(bits), encode(queue))
                self.assertEqual(phase, 0 if taking else m)
                self.assertEqual(tag.decode_boundary(source, cts.Configuration(''.join(bits), phase),
                                 max_word_bits=700, max_queue_symbols=100), machine.snapshot())
                position = tag.selection_position(source, event, head)
                if event.phase == tag.TAKE:
                    self.assertEqual(position.cts_prestate_step, m * j + head)
                else:
                    self.assertIsNone(position)

    def test_empty_is_reached_on_final_original_block_bit_only(self):
        for m in range(1, 12):
            program = tag.Program(((),) * m)
            binary = tag.compile_program(program, max_phases=22, max_program_bits=0)
            for phase in (tag.TAKE, tag.SKIP):
                for symbol in range(m):
                    machine = cts.Machine(binary, tag.encode_configuration(program,
                                          tag.Configuration((symbol,), phase), max_word_bits=11),
                                          max_steps=m, max_word_bits=m)
                    for k in range(m):
                        self.assertEqual(machine.word_bits, m - k)
                        machine.tick()
                    self.assertEqual(machine.word_bits, 0)
                    with self.assertRaises(StopIteration):
                        machine.tick()

    def test_transient_bound_is_sharp_at_zero_and_loose_at_last_symbol(self):
        for m in range(2, 15):
            program = tag.Program(tuple((h,) for h in range(m)))
            binary = tag.compile_program(program, max_phases=28, max_program_bits=196)
            for symbol in (0, m - 1):
                source = tag.Configuration((symbol,), tag.TAKE)
                steps, bound = tag.simulation_bounds(program, max_source_steps=1,
                                                     max_queue_symbols=1)
                machine = cts.Machine(binary, tag.encode_configuration(program, source,
                                      max_word_bits=m), max_steps=steps, max_word_bits=bound)
                for _ in range(m):
                    machine.tick()
                self.assertEqual(machine.peak_word_bits, 2 * m - symbol - 1)
                self.assertEqual(tag.decode_boundary(program, machine.snapshot(), max_word_bits=m,
                                 max_queue_symbols=1), tag.Configuration((symbol,), tag.SKIP))


if __name__ == '__main__':
    unittest.main()
