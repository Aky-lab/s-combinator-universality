"""Independent oracles and exhaustive small-domain checks for alternating tag."""
from dataclasses import FrozenInstanceError
from itertools import product
import unittest
from unittest.mock import patch

from s_only import alternating_tag as tag
from s_only import cts


def words(m, maximum):
    return tuple(word for length in range(maximum + 1)
                 for word in product(range(m), repeat=length))


def reference_encode(m, queue):
    return "".join("1" if offset == symbol else "0"
                   for symbol in queue for offset in range(m))


def reference_step(productions, queue, phase):
    if not queue:
        raise StopIteration
    result = list(queue)
    head = result.pop(0)
    if phase == tag.TAKE:
        result += list(productions[head])
    return tuple(result), tag.SKIP if phase == tag.TAKE else tag.TAKE


class AlternatingTagTests(unittest.TestCase):
    def compiled(self, program):
        m = program.alphabet_size
        return tag.compile_program(program, max_phases=2 * m,
                                   max_program_bits=m * sum(map(len, program.productions)))

    def assert_block(self, program, compiled, state):
        m = program.alphabet_size
        encoded = tag.encode_configuration(program, state, max_word_bits=1000)
        self.assertEqual(encoded.word, reference_encode(m, state.queue))
        self.assertEqual(encoded.phase, 0 if state.phase == tag.TAKE else m)
        self.assertEqual(tag.decode_boundary(program, encoded, max_word_bits=1000,
                                            max_queue_symbols=100), state)
        machine = cts.Machine(compiled, encoded, max_steps=m, max_word_bits=1000)
        if not state.queue:
            with self.assertRaises(StopIteration):
                machine.tick()
            with self.assertRaises(StopIteration):
                tag.step(program, state, max_queue_symbols=100)
            return
        expected_queue, expected_phase = reference_step(program.productions,
                                                        state.queue, state.phase)
        # Every original block has m bits, even when its production is empty.
        signals = []
        for offset in range(m):
            prestate = machine.snapshot()
            self.assertTrue(prestate.word, (program, state, offset))
            for symbol in range(m):
                if tag.selected_cts_event(program, prestate, symbol):
                    signals.append((offset, symbol))
            event = machine.tick()
            self.assertEqual(event.step, offset + 1)
        expected_signals = [(state.queue[0], state.queue[0])] if state.phase == tag.TAKE else []
        self.assertEqual(signals, expected_signals)
        boundary = tag.decode_boundary(program, machine.snapshot(),
                                       max_word_bits=1000, max_queue_symbols=100)
        expected = tag.Configuration(expected_queue, expected_phase)
        self.assertEqual(boundary, expected)
        self.assertEqual(tag.step(program, state, max_queue_symbols=100), expected)
        self.assertEqual(machine.steps, m)
        source = tag.Machine(program, state, max_steps=1, max_queue_symbols=100)
        event = source.tick()
        self.assertEqual(source.snapshot(), expected)
        self.assertEqual((event.step, event.phase, event.deleted, event.appended),
                         (1, state.phase, state.queue[0],
                          program.productions[state.queue[0]] if state.phase == tag.TAKE else ()))
        for symbol in range(m):
            position = tag.selection_position(program, event, symbol)
            if expected_signals and symbol == state.queue[0]:
                self.assertEqual(position, tag.SelectionPosition(0, symbol, symbol + 1))
            else:
                self.assertIsNone(position)

    def test_exhaustive_all_tables_and_queues_through_length_two(self):
        checked = 0
        for m in (1, 2, 3):
            domain = words(m, 2)
            for productions in product(domain, repeat=m):
                program = tag.Program(productions)
                compiled = self.compiled(program)
                self.assertEqual(compiled.appendants,
                                 tuple(reference_encode(m, p) for p in productions) + ("",) * m)
                for queue in domain:
                    for phase in (tag.TAKE, tag.SKIP):
                        self.assert_block(program, compiled, tag.Configuration(queue, phase))
                        checked += 1
        self.assertEqual(checked, 57826)

    def test_multistep_source_and_cts_against_independent_list_oracle(self):
        for m, production_length, queue_length in ((1, 3, 4), (2, 2, 3), (3, 1, 3)):
            for productions in product(words(m, production_length), repeat=m):
                program = tag.Program(productions)
                compiled = self.compiled(program)
                for seed in words(m, queue_length):
                    for phase in (tag.TAKE, tag.SKIP):
                        initial = tag.Configuration(seed, phase)
                        source = tag.Machine(program, initial, max_steps=10, max_queue_symbols=100)
                        bits = cts.Machine(compiled, tag.encode_configuration(
                            program, initial, max_word_bits=300), max_steps=10 * m,
                            max_word_bits=302)
                        queue, current_phase = seed, phase
                        for j in range(10):
                            if not queue:
                                self.assertEqual(bits.word_bits, 0)
                                break
                            selected = []
                            for offset in range(m):
                                prestate = bits.snapshot()
                                for h in range(m):
                                    if tag.selected_cts_event(program, prestate, h):
                                        selected.append((h, bits.steps, bits.steps + 1))
                                bits.tick()
                            source_event = source.tick()
                            expected = [(queue[0], m * j + queue[0], m * j + queue[0] + 1)] \
                                if current_phase == tag.TAKE else []
                            self.assertEqual(selected, expected)
                            for h, pre, logged in selected:
                                self.assertEqual(tag.selection_position(program, source_event, h),
                                                 tag.SelectionPosition(j, pre, logged))
                            queue, current_phase = reference_step(productions, queue, current_phase)
                            expected_state = tag.Configuration(queue, current_phase)
                            self.assertEqual(source.snapshot(), expected_state)
                            self.assertEqual(tag.decode_boundary(program, bits.snapshot(),
                                max_word_bits=302, max_queue_symbols=100), expected_state)

    def test_empty_and_singletons_are_not_conventional_delete_two(self):
        # A conventional deletion-two system makes no move from length < 2.
        def conventional_step(productions, queue):
            if len(queue) < 2:
                raise StopIteration
            return queue[2:] + productions[queue[0]]

        for phase in (tag.TAKE, tag.SKIP):
            self.assert_block(tag.Program(((0,),)), self.compiled(tag.Program(((0,),))),
                              tag.Configuration((), phase))
        program = tag.Program(((1, 0), ()))
        initial = tag.Configuration((0,))
        with self.assertRaises(StopIteration):
            conventional_step(program.productions, initial.queue)
        take = tag.step(program, initial, max_queue_symbols=2)
        self.assertEqual(take, tag.Configuration((1, 0), tag.SKIP))
        skip = tag.step(program, take, max_queue_symbols=2)
        self.assertEqual(skip, initial)
        # This alternating trajectory cycles although conventional semantics stops initially.
        result = tag.evaluate(program, initial, max_steps=8, max_queue_symbols=2,
                              selected_symbol=0)
        self.assertEqual((result.stop_reason, result.selected_count), ("step_limit", 4))
        self.assertEqual(result.first_selection, tag.SelectionPosition(0, 0, 1))
        for phase in (tag.TAKE, tag.SKIP):
            empty_rule = tag.Program(((), (), ()))
            state = tag.Configuration((2,), phase)
            self.assert_block(empty_rule, self.compiled(empty_rule), state)
            self.assertEqual(tag.step(empty_rule, state, max_queue_symbols=1).queue, ())
        # For length >= 2, a take/skip pair agrees with the conventional step.
        for seed in words(2, 4):
            if len(seed) >= 2:
                after_take = tag.step(program, tag.Configuration(seed), max_queue_symbols=10)
                after_skip = tag.step(program, after_take, max_queue_symbols=10)
                self.assertEqual(after_skip.queue, conventional_step(program.productions, seed))

    def test_ignored_selected_symbol_never_signals(self):
        program = tag.Program(((1,), (0,)))
        state = tag.Configuration((1,), tag.SKIP)
        self.assert_block(program, self.compiled(program), state)
        event = tag.Machine(program, state, max_steps=1, max_queue_symbols=1).tick()
        self.assertIsNone(tag.selection_position(program, event, 1))
        result = tag.evaluate(program, state, max_steps=1, max_queue_symbols=1, selected_symbol=1)
        self.assertEqual((result.selected_count, result.first_selection), (0, None))

    def test_transient_size_needs_more_than_encoded_endpoint_bound(self):
        program = tag.Program(((0,), (), ()))
        initial = tag.Configuration((0,))
        compiled = self.compiled(program)
        encoded = tag.encode_configuration(program, initial, max_word_bits=3)
        insufficient = cts.Machine(compiled, encoded, max_steps=3, max_word_bits=3)
        with self.assertRaises(cts.ResourceLimit):
            insufficient.tick()
        self.assertEqual(insufficient.snapshot(), encoded)
        limits = tag.simulation_bounds(program, max_source_steps=1, max_queue_symbols=1)
        self.assertEqual(limits, (3, 5))
        enough = cts.Machine(compiled, encoded, max_steps=limits[0], max_word_bits=limits[1])
        for _ in range(3):
            enough.tick()
        self.assertEqual(enough.peak_word_bits, 5)
        self.assertEqual(enough.snapshot(), cts.Configuration("100", 3))
        self.assertEqual(tag.simulation_bounds(program, max_source_steps=0,
                                               max_queue_symbols=0), (0, 0))

    def test_limits_are_transactional_and_empty_takes_precedence(self):
        program = tag.Program(((0, 0, 0),))
        initial = tag.Configuration((0,))
        for limits in ({"max_steps": 0, "max_queue_symbols": 3},
                       {"max_steps": 1, "max_queue_symbols": 2}):
            machine = tag.Machine(program, initial, **limits)
            with self.assertRaises(tag.ResourceLimit):
                machine.tick()
            self.assertEqual((machine.snapshot(), machine.steps, machine.peak_queue_symbols),
                             (initial, 0, 1))
        with self.assertRaises(tag.ResourceLimit):
            tag.step(program, initial, max_queue_symbols=2)
        with self.assertRaises(tag.ResourceLimit):
            tag.Machine(program, initial, max_steps=1, max_queue_symbols=0)
        with self.assertRaises(tag.ResourceLimit):
            tag.step(program, initial, max_queue_symbols=0)
        empty = tag.Machine(program, tag.Configuration(()), max_steps=0, max_queue_symbols=0)
        with self.assertRaises(StopIteration):
            empty.tick()
        self.assertEqual(tag.evaluate(program, tag.Configuration(()), max_steps=0,
                                      max_queue_symbols=0).stop_reason, "empty")
        result = tag.evaluate(program, initial, max_steps=0, max_queue_symbols=1)
        self.assertEqual((result.steps, result.stop_reason, result.first_selection),
                         (0, "step_limit", None))
        with self.assertRaises(tag.ResourceLimit):
            tag.evaluate(program, initial, max_steps=1, max_queue_symbols=2)

    def test_compiler_limits_preflight_all_output_allocations(self):
        program = tag.Program(((0, 1), (1,)))
        with patch.object(tag, "_encode_unchecked", side_effect=AssertionError("allocated")):
            for limits in ({"max_phases": 3, "max_program_bits": 100},
                           {"max_phases": 4, "max_program_bits": 5}):
                with self.assertRaises(tag.ResourceLimit):
                    tag.compile_program(program, **limits)
            with self.assertRaises(tag.ResourceLimit):
                tag.encode_word(program, (0, 1), max_word_bits=3)
        self.assertEqual(self.compiled(program).appendants, ("1001", "01", "", ""))
        self.assertEqual(tag.encode_word(program, (), max_word_bits=0), "")
        all_empty = tag.Program(((),) * 100)
        with self.assertRaises(tag.ResourceLimit):
            tag.compile_program(all_empty, max_phases=199, max_program_bits=0)
        self.assertEqual(len(tag.compile_program(all_empty, max_phases=200,
                                                max_program_bits=0).appendants), 200)

    def test_frozen_source_values_and_malformed_inputs(self):
        for bad in ((), [], [()], ([],), ((True,),), ((-1,),), ((1,),), ((0.0,),), (("0",),)):
            with self.assertRaises(ValueError, msg=repr(bad)):
                tag.Program(bad)
        for bad in ([], [0], (True,), (-1,), (0.0,), ("0",), "0", None):
            with self.assertRaises(ValueError):
                tag.Configuration(bad)
        for phase in ("TAKE", "", "stop", 0, 1, True, None):
            with self.assertRaises(ValueError):
                tag.Configuration((), phase)
        program = tag.Program(((0,),))
        state = tag.Configuration((0,))
        with self.assertRaises(FrozenInstanceError):
            program.productions = ((),)
        with self.assertRaises(FrozenInstanceError):
            state.phase = tag.SKIP
        outside = tag.Configuration((1,))
        for call in (lambda: tag.step(program, outside, max_queue_symbols=1),
                     lambda: tag.Machine(program, outside, max_steps=1, max_queue_symbols=1),
                     lambda: tag.encode_configuration(program, outside, max_word_bits=1),
                     lambda: tag.encode_word(program, (1,), max_word_bits=1),
                     lambda: tag.compile_program(None, max_phases=2, max_program_bits=1),
                     lambda: tag.step(program, None, max_queue_symbols=1)):
            with self.assertRaises(ValueError):
                call()
        for bad in (-1, True, 1.5, "1", None):
            for name in ("max_steps", "max_queue_symbols"):
                limits = {"max_steps": 1, "max_queue_symbols": 1, name: bad}
                with self.assertRaises(ValueError):
                    tag.Machine(program, state, **limits)
            for name in ("max_phases", "max_program_bits"):
                limits = {"max_phases": 2, "max_program_bits": 1, name: bad}
                with self.assertRaises(ValueError):
                    tag.compile_program(program, **limits)
            with self.assertRaises(ValueError):
                tag.encode_word(program, (0,), max_word_bits=bad)
            with self.assertRaises(ValueError):
                tag.simulation_bounds(program, max_source_steps=bad, max_queue_symbols=1)
            with self.assertRaises(ValueError):
                tag.simulation_bounds(program, max_source_steps=1, max_queue_symbols=bad)
        for h in (-1, True, 0.0, 1, None):
            with self.assertRaises(ValueError):
                tag.selected_cts_event(program, cts.Configuration("1"), h)
        with self.assertRaises(ValueError):
            tag.selected_cts_event(program, cts.Configuration("1", 2), 0)
        with self.assertRaises(ValueError):
            tag.selected_cts_event(program, None, 0)

    def test_boundary_parser_rejects_non_codes_and_non_boundaries(self):
        program = tag.Program(((), (), ()))
        for word, phase in (("1", 0), ("10", 0), ("000", 0), ("110", 0),
                            ("101", 0), ("100000", 0), ("100", 1), ("100", 4), ("", 6)):
            with self.assertRaises(ValueError, msg=repr((word, phase))):
                tag.decode_boundary(program, cts.Configuration(word, phase),
                                    max_word_bits=100, max_queue_symbols=100)
        for limits in ({"max_word_bits": 5, "max_queue_symbols": 2},
                       {"max_word_bits": 6, "max_queue_symbols": 1}):
            with self.assertRaises(tag.ResourceLimit):
                tag.decode_boundary(program, cts.Configuration("100010"), **limits)
        for phase in (0, 3):
            self.assertEqual(tag.decode_boundary(program, cts.Configuration("", phase),
                max_word_bits=0, max_queue_symbols=0).queue, ())
        for bad in (-1, True, 1.5, None):
            for name in ("max_word_bits", "max_queue_symbols"):
                limits = {"max_word_bits": 3, "max_queue_symbols": 1, name: bad}
                with self.assertRaises(ValueError):
                    tag.decode_boundary(program, cts.Configuration("100"), **limits)
        with self.assertRaises(ValueError):
            tag.decode_boundary(program, None, max_word_bits=0, max_queue_symbols=0)

    def test_hostile_subclasses_and_primitive_cts_fields_are_rejected(self):
        mutable_m = [1]

        class MutableProgram(tag.Program):
            @property
            def alphabet_size(self):
                return mutable_m[0]

        mutable_queue = [()]

        class MutableConfiguration(tag.Configuration):
            @property
            def queue(self):
                return mutable_queue[0]

            @queue.setter
            def queue(self, value):
                mutable_queue[0] = value

        mutable_deleted = [0]

        class MutableEvent(tag.Event):
            @property
            def deleted(self):
                return mutable_deleted[0]

            @deleted.setter
            def deleted(self, value):
                mutable_deleted[0] = value

        class CTSSubclass(cts.Configuration):
            pass

        class HostileWord(str):
            def startswith(self, *args):
                raise AssertionError("untrusted startswith called")

            def count(self, *args):
                raise AssertionError("untrusted count called")

            def index(self, *args):
                raise AssertionError("untrusted index called")

        program = tag.Program(((0,),))
        state = tag.Configuration((0,))
        event = tag.Event(1, tag.TAKE, 0, (0,), 1)
        foreign_program = MutableProgram(((0,),))
        foreign_state = MutableConfiguration((0,))
        foreign_event = MutableEvent(1, tag.TAKE, 0, (0,), 1)
        # These normally initialized subclasses have mutable interpretations.
        mutable_m[0] = True
        mutable_queue[0] = (True,)
        mutable_deleted[0] = True
        calls = (
            lambda: tag.step(foreign_program, state, max_queue_symbols=1),
            lambda: tag.Machine(foreign_program, state, max_steps=1, max_queue_symbols=1),
            lambda: tag.compile_program(foreign_program, max_phases=2, max_program_bits=1),
            lambda: tag.encode_word(foreign_program, (0,), max_word_bits=1),
            lambda: tag.encode_configuration(foreign_program, state, max_word_bits=1),
            lambda: tag.decode_boundary(foreign_program, cts.Configuration("1"),
                                       max_word_bits=1, max_queue_symbols=1),
            lambda: tag.selected_cts_event(foreign_program, cts.Configuration("1"), 0),
            lambda: tag.selection_position(foreign_program, event, 0),
            lambda: tag.evaluate(foreign_program, state, max_steps=1, max_queue_symbols=1),
            lambda: tag.simulation_bounds(foreign_program, max_source_steps=1,
                                         max_queue_symbols=1),
            lambda: tag.step(program, foreign_state, max_queue_symbols=1),
            lambda: tag.Machine(program, foreign_state, max_steps=1, max_queue_symbols=1),
            lambda: tag.encode_configuration(program, foreign_state, max_word_bits=1),
            lambda: tag.evaluate(program, foreign_state, max_steps=1, max_queue_symbols=1),
            lambda: tag.selection_position(program, foreign_event, 0),
        )
        for call in calls:
            with self.assertRaises(ValueError):
                call()
        for invalid_cts in (CTSSubclass("1"), cts.Configuration(HostileWord("1"))):
            with self.assertRaises(ValueError):
                tag.decode_boundary(program, invalid_cts, max_word_bits=1, max_queue_symbols=1)
            with self.assertRaises(ValueError):
                tag.selected_cts_event(program, invalid_cts, 0)
        # The boundary validates primitive phase fields even on deliberately
        # tampered exact CTS objects; bool must not alias phases zero or one.
        for bad_phase in (False, True, -1, 0.0, "0", None):
            invalid_cts = cts.Configuration("1")
            object.__setattr__(invalid_cts, "phase", bad_phase)
            with self.assertRaises(ValueError):
                tag.decode_boundary(program, invalid_cts, max_word_bits=1, max_queue_symbols=1)
            with self.assertRaises(ValueError):
                tag.selected_cts_event(program, invalid_cts, 0)

    def test_event_mapping_rejects_malformed_and_inconsistent_events(self):
        program = tag.Program(((0,),))
        for arguments in ((0, tag.TAKE, 0, (0,), 1), (True, tag.TAKE, 0, (0,), 1),
                          (1, "invalid", 0, (), 1), (1, tag.TAKE, True, (), 1),
                          (1, tag.TAKE, 0, [], 1), (1, tag.TAKE, 0, (), -1)):
            with self.assertRaises(ValueError):
                tag.Event(*arguments)
        for event in (None, tag.Event(1, tag.TAKE, 1, (), 0),
                      tag.Event(1, tag.TAKE, 0, (), 0), tag.Event(1, tag.SKIP, 0, (0,), 1)):
            with self.assertRaises(ValueError):
                tag.selection_position(program, event, 0)
        # Position depends on source microstep count, not on occurrence count.
        self.assertEqual(tag.selection_position(program, tag.Event(8, tag.TAKE, 0, (0,), 1), 0),
                         tag.SelectionPosition(7, 7, 8))


if __name__ == "__main__":
    unittest.main()
