"""Bounded independent evidence for positive-period program-static controllers."""
from dataclasses import FrozenInstanceError
import hashlib
import json
from pathlib import Path
import time
import unittest
from unittest.mock import patch

from s_only import cts_reader, periodic_selector, program_selector, probes
from s_only.cts import Program
from s_only.encoding import B, HALT, LIVE, PI, VALUES, append_routine, compile_program, encode
from s_only.probes import Configuration, Cursor, OBSERVATIONS, compile_rows
from s_only.program_selector_parts.active import compile_dispatcher
from s_only.program_selector_parts.patterns import PatternFamily
from s_only.program_selector_parts.priority import compile_parity
from s_only.reduction import contract_at, root_arguments
from s_only.root_selector import SelectorTable, erase, step
from s_only.selector_parts.graph import GraphBuilder
from s_only.terms import App, S, nodes
from tools.program_selector_report import run_one

ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = (('01',), ('01', '', '01'), ('10', '1', '', '10'),
            ('01', '', '1', '01', '001'))
SHELL = (0, 0, 1)


def app(*terms):
    result = terms[0]
    for term in terms[1:]:
        result = App(result, term)
    return result


def independent_route(leaves, index):
    """Largest-power split, independent of the compiler's pairing/route walk."""
    if leaves == 1:
        return ()
    split = 1 << ((leaves - 1).bit_length() - 1)
    if index < split:
        return (0,) + independent_route(split, index)
    return (1,) + independent_route(leaves - split, index - split)


def response_address(route):
    return SHELL + tuple(edge for side in route for edge in (1, side)) + (1,)


def chosen(code, route, response, audit):
    """Construct a concrete chosen route without consuming generated patterns."""
    if not route:
        return app(S, audit, response)
    left, right = code.right.left.right, code.right.right
    if route[0] == 0:
        branch = App(chosen(left, route[1:], response, audit), App(right, audit))
    else:
        branch = App(App(left, audit), chosen(right, route[1:], response, audit))
    return app(S, audit, branch)


def local(dispatch, carrier=S, *, marked=False):
    halt = app(S, S, App(App(B, S), carrier)) if marked else App(HALT, carrier)
    return app(halt, dispatch, app(S, App(S, S), S), App(S, App(S, S)))


def completed(compiled, phase, bit, accumulator, *, marked=False):
    route = independent_route(len(compiled.action_terms), 2 * phase + bit)
    response = App(PI, accumulator)
    for _ in range(len(compiled.program.appendants[phase]) if bit else 0):
        response = App(response, App(S, S))
    return local(chosen(compiled.actions, route, response, S), marked=marked)


def probe(table, term):
    state = Configuration(table.start, Cursor.at(term))
    for _ in range(table.tick_bound + 1):
        answer = table.answer(state.control)
        if answer is not None:
            return answer, state.cursor
        state = probes.step(table, state)
    raise AssertionError('static acyclic probe tick bound exhausted')


def select(table, term, *, max_ticks=2_000_000, seconds=15):
    state = Configuration(table.start, Cursor.at(term))
    deadline = time.monotonic() + seconds
    for tick in range(max_ticks + 1):
        if table.status(state.control) is not None:
            return state
        if tick % 1024 == 0 and time.monotonic() >= deadline:
            raise AssertionError('external soft wall-time cap')
        state = step(table, state)
    raise AssertionError('external microtick cap')


def fragment(compiler, p):
    builder = GraphBuilder()
    no, contracted = builder.uniform('normal'), builder.uniform('contracted')
    yes = builder.uniform('Rdx', contracted)
    start = compiler(builder, p, yes, no)
    return SelectorTable(builder.finish(), start)


def digest(table):
    value = hashlib.sha256()
    for control, row in enumerate(table.states):
        for observation, instruction in enumerate(row):
            value.update(f'{control}:{observation}:{instruction.command}:{instruction.next_state}\n'.encode())
    return value.hexdigest()


class PeriodicPatternTests(unittest.TestCase):
    def test_layout_actual_routes_and_successors_for_every_phase(self):
        for appendants in PROGRAMS + (('', '', ''), ('',) * 5):
            program = Program(appendants)
            p = PatternFamily(program, required_period=None)
            self.assertEqual(p.dispatch.code, compile_program(program).actions)
            self.assertEqual(len(p.dispatch_records()), 2 * len(appendants))
            for index, (_, route, label) in enumerate(p.dispatch_records()):
                expected = independent_route(2 * len(appendants), index)
                self.assertEqual(label, divmod(index, 2))
                self.assertEqual(route, expected)
                self.assertEqual(p.route_for(label), expected)
            labels = p.phase_labels()
            self.assertEqual([phase for phase, _ in labels], [0] +
                             [((index // 2) + 1) % len(appendants)
                              for _ in range(2) for index in range(2 * len(appendants))])
            with self.assertRaises(FrozenInstanceError):
                p.program = Program(('',))
        p = PatternFamily(Program(('', '', '')), required_period=None)
        self.assertEqual(p.routes, ((0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0), (1, 1)))
        for label in ((-1, 0), (3, 0), (0, 2), (True, 0), (0, False)):
            with self.assertRaises(ValueError):
                p.route_for(label)
        # Historical internal default remains restricted along with its API.
        with self.assertRaisesRegex(ValueError, 'exactly two'):
            PatternFamily(Program(('',)))

    def test_concrete_dispatch_stages_and_phase_bit_recovery_every_label(self):
        for appendants in PROGRAMS + (('', '', ''), ('',) * 5):
            program = Program(appendants)
            p = PatternFamily(program, required_period=None)
            dispatcher = fragment(compile_dispatcher, p)
            for phase in range(len(appendants)):
                for bit in (0, 1):
                    route = independent_route(2 * len(appendants), 2 * phase + bit)
                    rows = compile_rows(p.dispatcher_rows((phase, bit)))
                    # Nearest completed Local determines the successor phase;
                    # the outer tombstone independently records the front bit.
                    previous = completed(p.compiled, (phase - 1) % len(appendants), 0, S)
                    carrier = app(S, previous, App(VALUES[bit], App(S, S)))
                    dispatch = App(p.compiled.actions, App(S, S))
                    addresses, address = [()], ()
                    for side in route:
                        addresses.extend((address + (1,), address + (1, side)))
                        address += (1, side)
                    for relative in addresses:
                        term = local(dispatch, carrier)
                        answer, cursor = probe(rows, term)
                        self.assertTrue(answer, (appendants, phase, bit, relative))
                        self.assertEqual(cursor.path, SHELL + relative)
                        recovered = select(dispatcher, term)
                        self.assertEqual(dispatcher.status(recovered.control), 'Rdx',
                                         (appendants, phase, bit, relative, recovered.cursor.path))
                        self.assertEqual(recovered.cursor.path, cursor.path)
                        self.assertIs(recovered.cursor.root, term)
                        self.assertIsNotNone(root_arguments(cursor.focus))
                        dispatch = contract_at(dispatch, relative)
                    answer, cursor = probe(rows, local(dispatch, carrier))
                    self.assertFalse(answer)
                    self.assertEqual(cursor.path, ())

    def test_concrete_appender_stages_and_accumulator_routes_every_phase(self):
        for appendants in PROGRAMS:
            p = PatternFamily(Program(appendants), required_period=None)
            appender = compile_rows(p.selected_action_rows())
            for phase, word in enumerate(appendants):
                route = independent_route(2 * len(appendants), 2 * phase + 1)
                accumulator = App(LIVE[0], S)
                response = App(append_routine(word), accumulator)
                for index in range(len(word)):
                    for half in (0, 1):
                        term = local(chosen(p.compiled.actions, route, response, App(S, S)))
                        answer, cursor = probe(appender, term)
                        self.assertTrue(answer, (appendants, phase, index, half))
                        self.assertEqual(cursor.path, response_address(route) + (0,) * index)
                        self.assertIsNotNone(root_arguments(cursor.focus))
                        response = contract_at(response, (0,) * index)
                answer, cursor = probe(appender, local(chosen(p.compiled.actions, route, response, S)))
                self.assertFalse(answer)
                self.assertEqual(cursor.path, ())
            for status in ('fresh', 'marked'):
                rows = compile_rows(p.local_rows(status))
                for phase in range(len(appendants)):
                    for bit in (0, 1):
                        accumulator = App(LIVE[1], App(LIVE[0], S))
                        term = completed(p.compiled, phase, bit, accumulator, marked=status == 'marked')
                        answer, cursor = probe(rows, term)
                        route = independent_route(2 * len(appendants), 2 * phase + bit)
                        history = len(appendants[phase]) if bit else 0
                        self.assertTrue(answer)
                        self.assertIs(cursor.focus, accumulator)
                        self.assertEqual(cursor.path, response_address(route) + (0,) * history + (1,))

    def test_chronology_stays_boolean_even_for_odd_periods(self):
        for period in (1, 3, 5):
            p = PatternFamily(Program(('',) * period), required_period=None)
            table = fragment(compile_parity, p)
            for phase in range(period):
                term = S
                for count in range(4):
                    selected = select(table, term)
                    self.assertEqual(table.status(selected.control), 'Rdx' if count % 2 == 0 else 'normal')
                    self.assertEqual(selected.cursor.path, ())
                    term = completed(p.compiled, phase, 0, term)


class PeriodicExecutionTests(unittest.TestCase):
    def tearDown(self):
        periodic_selector.selector_table.cache_clear()
        program_selector.selector_table.cache_clear()

    def test_legacy_api_and_all_five_frozen_graph_digests(self):
        golden = json.loads((ROOT / 'results/two_phase_programs.json').read_text())
        starts = (227379, 302379, 305984, 186666, 381908)
        for record, start in zip(golden['programs'], starts):
            program = Program(tuple(record['appendants']))
            table = program_selector.selector_table(program, max_states=1_000_000)
            self.assertEqual(len(table.states), record['finite_control_states'])
            self.assertEqual(table.start, start)
            self.assertEqual(digest(table), record['control_table_sha256'])
        program = Program(('01', '001'))
        general = periodic_selector.selector_table(program, max_states=1_000_000)
        self.assertEqual(general, table)
        for period in (1, 3, 4, 5):
            with self.assertRaisesRegex(ValueError, 'exactly two'):
                program_selector.selector_table(Program(('',) * period))

    def test_explicit_limits_typed_cache_and_controlled_host_recursion(self):
        p = Program(('',))
        for name in ('select_cursor', 'select_path', 'execute', 'reduce_once'):
            with self.assertRaises(TypeError):
                getattr(periodic_selector, name)(S, None)
        with self.assertRaises(TypeError):
            periodic_selector.selector_table(('1',))
        for name, good, bad_values in (
                ('max_states', 200_000, (0, -1, True, 2.5)),
                ('max_appendant_bits', 0, (-1, False, 0.0)),
                ('max_phases', 1, (0, -1, True, 1.0))):
            table = periodic_selector.selector_table(p, **{name: good})
            self.assertIs(table, periodic_selector.selector_table(p, **{name: good}))
            for bad in bad_values:
                with self.assertRaises(ValueError):
                    periodic_selector.selector_table(p, **{name: bad})
        with self.assertRaisesRegex(periodic_selector.CompilationLimit, 'phases'):
            periodic_selector.selector_table(Program(('',) * 17), max_states=10)
        with self.assertRaisesRegex(periodic_selector.CompilationLimit, 'appendant bits'):
            periodic_selector.selector_table(Program(('1' * 129,)), max_states=10)
        with patch('s_only.program_selector_parts.patterns.PatternFamily',
                   side_effect=AssertionError('patterns expanded despite tiny state cap')):
            with self.assertRaisesRegex(periodic_selector.CompilationLimit, 'states'):
                periodic_selector.selector_table(Program(('1' * 129,)), max_states=10,
                                                 max_appendant_bits=None, max_phases=None)
        with patch('s_only.program_selector_parts.active.compile_active', side_effect=RecursionError):
            with self.assertRaisesRegex(periodic_selector.CompilationLimit, 'host recursion'):
                periodic_selector.selector_table(p, max_states=200_001)
        self.assertIs(periodic_selector.CompilationLimit, program_selector.CompilationLimit)

    def test_two_checked_horizons_for_small_periods(self):
        for appendants in PROGRAMS:
            program = Program(appendants)
            table = periodic_selector.selector_table(program, max_states=3_000_000)
            reader = cts_reader.compile_reader(program)
            for seed in ('11', '1', ''):
                result = run_one(program, table, reader, seed, target_horizon=2,
                                 max_steps=180, max_ticks=2_000_000, max_nodes=5_000_000,
                                 deadline=time.monotonic() + 90)
                self.assertEqual([x['horizon'] for x in result['checkpoints']], [0, 1, 2])
                self.assertEqual(result['samples_checked'], result['native_contractions'] + 1)
                self.assertLessEqual(result['peak_expanded_nodes'], 5_000_000)

    def test_runtime_is_explicit_immutable_root_reset_and_one_native_contraction(self):
        program = Program(('01', '', '01'))
        table = periodic_selector.selector_table(program, max_states=2_000_000)
        self.assertEqual(tuple(SelectorTable.__dataclass_fields__), ('states', 'start'))
        self.assertEqual(tuple(Configuration.__dataclass_fields__), ('control', 'cursor'))
        with self.assertRaises(FrozenInstanceError):
            table.start = 0
        for row in table.states:
            self.assertEqual(len(row), len(OBSERVATIONS))
            self.assertTrue(all(instruction.command in
                                ('stay', 'L', 'R', 'U', 'Rdx', 'normal', 'contracted')
                                for instruction in row))
        term = encode(program, '11')
        forbidden = AssertionError('runtime consulted a compiler, evaluator, or reader')
        with patch('s_only.cts.step', side_effect=forbidden), \
             patch('s_only.encoding.compile_program', side_effect=forbidden), \
             patch('s_only.cts_reader.CompiledReader.decode', side_effect=forbidden), \
             patch('s_only.program_selector_parts.patterns.PatternFamily', side_effect=forbidden), \
             patch('s_only.periodic_selector.selector_table', side_effect=forbidden), \
             patch('s_only.program_selector.selector_table', side_effect=forbidden), \
             patch('s_only.root_selector.selector_table', side_effect=forbidden):
            for _ in range(30):
                selected = select(table, term)
                self.assertEqual(table.status(selected.control), 'Rdx')
                self.assertIs(selected.cursor.root, term)
                self.assertIsNotNone(root_arguments(selected.cursor.focus))
                expected = contract_at(term, selected.cursor.path)
                result = step(table, selected)
                self.assertEqual(table.status(result.control), 'contracted')
                self.assertIs(step(table, result), result)
                term = erase(result.cursor)
                self.assertEqual(term, expected)
                self.assertLess(nodes(term), 5_000_000)
            self.assertIsNone(periodic_selector.reduce_once(S, table))


if __name__ == '__main__':
    unittest.main()
