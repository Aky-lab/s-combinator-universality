"""Bounded, independent checks of program-static two-phase controllers."""
from dataclasses import FrozenInstanceError
from itertools import cycle
import hashlib
import json
from pathlib import Path
import time
import unittest
from unittest.mock import patch

from s_only.cts import Program, Configuration as CTSState, step as cts_step
from s_only.encoding import B, HALT, LIVE, PI, append_routine, compile_program, encode
from s_only.probes import Configuration, Cursor, OBSERVATIONS, compile_rows
from s_only import probes
from s_only.program_selector import CompilationLimit, erase, selector_table, step
from s_only.program_selector_parts.patterns import PatternFamily, H, S as PS
from s_only.reduction import contract_at, root_arguments, select_path as preorder
from s_only.terms import App, S, nodes, prefix

ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = (('1', ''), ('0', '10'), ('10', '1'), ('', ''), ('01', '001'))


def bounded(table, term, *, max_ticks=2_000_000, seconds=15):
    """The driver owns all counters and time limits; none enter controller state."""
    state = Configuration(table.start, Cursor.at(term))
    deadline = time.monotonic() + seconds
    for ticks in range(max_ticks + 1):
        if table.status(state.control) in ('Rdx', 'normal'):
            return state, ticks
        if ticks % 1024 == 0 and time.monotonic() > deadline:
            raise AssertionError('external per-invocation wall-time cap')
        state = step(table, state)
    raise AssertionError('external per-invocation microtick cap')


def apply(*terms):
    out = terms[0]
    for term in terms[1:]:
        out = App(out, term)
    return out


def _chosen_response(code, route, response, audit):
    """Independent concrete S constructor; no generated pattern is consumed."""
    if not route:
        return apply(S, audit, response)
    # Every nonleaf compile_program code is B (S left right).
    left, right = code.right.left.right, code.right.right
    if route[0] == 0:
        body = App(_chosen_response(left, route[1:], response, audit), App(right, audit))
    else:
        body = App(App(left, audit), _chosen_response(right, route[1:], response, audit))
    return apply(S, audit, body)


def local_response(compiled, label, response, audit):
    dispatch = _chosen_response(compiled.actions, label, response, audit)
    return apply(App(HALT, audit), dispatch, apply(S, audit, audit), App(S, audit))


def instantiate(pattern, values):
    if pattern == H:
        return next(values)
    if pattern == PS:
        return S
    return App(instantiate(pattern[0], values), instantiate(pattern[1], values))


def probe_run(table, term):
    state = Configuration(table.start, Cursor.at(term))
    # This finite acyclic graph has a checked static path bound.
    for _ in range(table.tick_bound + 1):
        answer = table.answer(state.control)
        if answer is not None:
            return answer, state.cursor
        state = probes.step(table, state)
    raise AssertionError('probe exceeded its certified acyclic bound')


class ProgramPatternTests(unittest.TestCase):
    def test_legacy_static_families_are_exact(self):
        from s_only.selector_parts import patterns as legacy
        from s_only.fuel_probe import fuel_rows
        p = PatternFamily(Program(('1', '')))
        names = ('environment_pattern', 'pending_pattern', 'base_pattern', 'base_row',
                 'dispatch_records', 'live_patterns', 'live_rows', 'tombstone_patterns',
                 'tombstone_rows', 'nonempty_carrier_rows', 'complete_carrier_rows',
                 'empty_origin_rows', 'deleted_bit_rows', 'cell_rows', 'frame_pending_rows',
                 'frame_head_rows', 'pending_admission_rows', 'phase_labels', 'selected_action_rows')
        for name in names:
            self.assertEqual(getattr(p, name)(), getattr(legacy, name)(), name)
        for status in ('fresh', 'marked'):
            self.assertEqual(p.local_patterns(status), legacy.local_patterns(status))
            self.assertEqual(p.local_rows(status), legacy.local_rows(status))
        for label in ((0, 0), (0, 1), (1, 0), (1, 1)):
            self.assertEqual(p.dispatcher_rows(label), legacy.dispatcher_rows(label))
        self.assertEqual(p.fuel_rows(), fuel_rows())

    def test_family_is_immutable_input_independent_and_exactly_two_phase(self):
        for bad in (Program(('',)), Program(('', '', ''))):
            with self.assertRaisesRegex(ValueError, 'exactly two'):
                PatternFamily(bad)
        with self.assertRaises(TypeError):
            PatternFamily(('1', ''))
        p = PatternFamily(Program(('01', '001')))
        with self.assertRaises(FrozenInstanceError):
            p.program = Program(('', ''))
        self.assertEqual(p.dispatch.code, compile_program(p.program).actions)
        self.assertEqual(len(p.selected_action_rows()), 10)
        self.assertEqual(PatternFamily(Program(('', ''))).selected_action_rows(), ())

    def test_every_nonempty_appender_stage_selects_exact_native_redex(self):
        for appendants in PROGRAMS + (('1010', '00011'),):
            p = PatternFamily(Program(appendants))
            table = compile_rows(p.selected_action_rows())
            for phase, word in enumerate(appendants):
                if not word:
                    continue
                audit = apply(S, App(S, S), S)
                accumulator = App(LIVE[0], S)
                response = App(append_routine(word), accumulator)
                label = phase, 1
                route_address = (0, 0, 1, 1, phase, 1, 1, 1)
                for index in range(len(word)):
                    for half in (0, 1):
                        term = local_response(p.compiled, label, response, audit)
                        accepted, cursor = probe_run(table, term)
                        self.assertTrue(accepted, (appendants, phase, index, half))
                        self.assertEqual(cursor.path, route_address + (0,) * index)
                        self.assertIs(cursor.root, term)
                        self.assertIsNotNone(root_arguments(cursor.focus))
                        response = contract_at(response, (0,) * index)
                # A fully completed action is not an appender-stage candidate.
                accepted, cursor = probe_run(table, local_response(p.compiled, label, response, audit))
                self.assertFalse(accepted)
                self.assertEqual(cursor.path, ())

    def test_selected_action_rows_guard_redexes_for_independent_holes(self):
        for appendants in PROGRAMS:
            p = PatternFamily(Program(appendants))
            table = compile_rows(p.selected_action_rows())
            for pattern, address in p.selected_action_rows():
                term = instantiate(pattern, cycle((S, App(S, S), apply(S, S, S, S))))
                accepted, cursor = probe_run(table, term)
                self.assertTrue(accepted)
                self.assertEqual(cursor.path, address)
                self.assertIsNotNone(root_arguments(cursor.focus))

    def test_completed_carrier_rows_follow_program_dependent_history_arity(self):
        for appendants in PROGRAMS:
            p = PatternFamily(Program(appendants))
            table = compile_rows(p.local_rows('fresh'))
            for phase in (0, 1):
                for bit in (0, 1):
                    count = len(appendants[phase]) if bit else 0
                    accumulator = App(LIVE[1], App(LIVE[0], S))
                    response = App(PI, accumulator)
                    for _ in range(count):
                        response = App(response, S)
                    term = local_response(p.compiled, (phase, bit), response, App(S, S))
                    accepted, cursor = probe_run(table, term)
                    self.assertTrue(accepted)
                    self.assertIs(cursor.focus, accumulator)
                    self.assertEqual(cursor.path, (0, 0, 1, 1, phase, 1, bit, 1) +
                                     (0,) * count + (1,))


class ProgramExecutionTests(unittest.TestCase):
    def test_explicit_compile_budget_and_validation(self):
        from s_only import program_selector
        for name in ('select_cursor', 'select_path', 'execute', 'reduce_once'):
            with self.assertRaises(TypeError):
                getattr(program_selector, name)(S, None)
        with self.assertRaises(CompilationLimit):
            selector_table(Program(('1', '')), max_states=100)
        for cap in (0, -1, True, 1.5):
            with self.assertRaises(ValueError):
                selector_table(Program(('1', '')), max_states=cap)
        for bad in (Program(('',)), Program(('', '', ''))):
            with self.assertRaises(ValueError):
                selector_table(bad)
        long_program = Program(('1' * 1000, ''))
        # Static literal expansion itself is iterative; construction is bounded.
        PatternFamily(long_program)
        with self.assertRaises(CompilationLimit):
            selector_table(long_program, max_states=10)
        with self.assertRaisesRegex(CompilationLimit, '10 states'):
            selector_table(long_program, max_states=10, max_appendant_bits=None)
        with self.assertRaisesRegex(CompilationLimit, 'appendant bits'):
            selector_table(Program(('01', '1')), max_appendant_bits=2)
        for cap in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                selector_table(Program(('', '')), max_appendant_bits=cap)

    def test_legacy_85_selections_and_outputs(self):
        program = Program(('1', ''))
        table = selector_table(program, max_states=1_000_000)
        self.assertEqual(len(table.states), 257_299)
        records = json.loads((ROOT / 'fixtures/queue_101_path.json').read_text())
        term = encode(program, '101')
        self.assertEqual(prefix(term), records['initial_prefix'])
        for record in records['steps']:
            selected, _ = bounded(table, term)
            self.assertEqual(selected.cursor.path, tuple(map(int, record['path'])))
            self.assertIs(selected.cursor.root, term)
            result = step(table, selected)
            self.assertEqual(table.status(result.control), 'contracted')
            self.assertIs(step(table, result), result)
            term = erase(result.cursor)
            self.assertEqual(nodes(term), record['nodes'])
            self.assertEqual(hashlib.sha256(prefix(term).encode('ascii')).hexdigest(),
                             record['after_sha256'])
        self.assertEqual(len(records['steps']), 85)

    def test_runtime_retains_only_primitive_graph_and_no_compiler_access(self):
        program = Program(('0', '10'))
        table = selector_table(program, max_states=1_000_000)
        self.assertIs(table, selector_table(program, max_states=1_000_000))
        self.assertEqual(tuple(type(table).__dataclass_fields__), ('states', 'start'))
        self.assertEqual(tuple(Configuration.__dataclass_fields__), ('control', 'cursor'))
        for row in table.states:
            self.assertEqual(len(row), len(OBSERVATIONS))
            for instruction in row:
                self.assertIn(instruction.command,
                              ('stay', 'L', 'R', 'U', 'Rdx', 'normal', 'contracted'))
                self.assertIsInstance(instruction.next_state, (int, type(None)))
        term = encode(program, '11')
        blocked = AssertionError('runtime consulted a forbidden compiler or source operation')
        with patch('s_only.cts.step', side_effect=blocked), \
             patch('s_only.encoding.compile_program', side_effect=blocked), \
             patch('s_only.program_selector_parts.patterns.PatternFamily', side_effect=blocked), \
             patch('s_only.root_selector.selector_table', side_effect=blocked):
            for _ in range(30):
                selected, _ = bounded(table, term)
                self.assertEqual(table.status(selected.control), 'Rdx')
                self.assertIsNotNone(root_arguments(selected.cursor.focus))
                term = erase(step(table, selected).cursor)

    def test_two_completed_horizons_for_new_programs_and_seeds(self):
        from s_only.cts_reader import compile_reader
        for appendants in PROGRAMS[1:]:
            program = Program(appendants)
            table = selector_table(program, max_states=1_000_000)
            reader = compile_reader(program)
            for seed in ('11', '1', ''):
                term, source = encode(program, seed), CTSState(seed)
                horizon = 0
                deadline = time.monotonic() + 45
                for count in range(151):
                    self.assertLess(nodes(term), 5_000_000, 'external expanded-node cap')
                    self.assertLess(time.monotonic(), deadline, 'external run wall-time cap')
                    checkpoint = reader.decode(term)
                    if checkpoint is not None:
                        while horizon < checkpoint['horizon']:
                            # The readout convention advances its phase on EMPTY.
                            source = (cts_step(program, source) if source.word else
                                      CTSState('', (source.phase + 1) % 2))
                            horizon += 1
                        self.assertEqual(checkpoint, {'horizon': horizon, 'phase': source.phase,
                                                      'data': source.word},
                                         (appendants, seed, count))
                        if horizon == 2:
                            break
                    if count == 150:
                        self.fail(f'external 150-contraction cap: {appendants!r}, {seed!r}')
                    selected, _ = bounded(table, term)
                    self.assertEqual(table.status(selected.control), 'Rdx')
                    self.assertIsNotNone(root_arguments(selected.cursor.focus))
                    term = erase(step(table, selected).cursor)
                else:
                    self.fail(f'external 150-contraction cap: {appendants!r}, {seed!r}')
                self.assertEqual(horizon, 2)


if __name__ == '__main__':
    unittest.main()
