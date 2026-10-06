"""Independent, bounded adversarial review of the positive-period extension.

Expected syntax, source transitions, contraction results and limits below are
review instrumentation. None is supplied to the finite runtime controller.
"""
from contextlib import ExitStack
from functools import lru_cache
import gc
import time
import unittest
from unittest.mock import patch

from s_only import cts, cts_reader, encoding, periodic_selector, probes
from s_only.probes import Configuration, Cursor, compile_rows
from s_only.program_selector_parts.active import compile_dispatcher
from s_only.program_selector_parts.patterns import PatternFamily
from s_only.root_selector import SelectorTable, erase, step
from s_only.selector_parts.graph import GraphBuilder
from s_only.terms import App, S, nodes


def app(*terms):
    result = terms[0]
    for term in terms[1:]:
        result = App(result, term)
    return result


# Independent transcription of the source constructors.
B = app(S, S)
PI = app(S, B)
C0 = app(S, B, B)
VALUES = (app(S, C0), app(S, app(S, C0)))
LIVE = tuple(app(B, value) for value in VALUES)
HALT = app(B, app(B, S))
AUDIT = app(S, S, S, S)  # Deliberately reducible and unrelated to its siblings.
SHELL = (0, 0, 1)


def routine(word):
    result = PI
    for bit in reversed(word):
        result = app(S, app(S, result), LIVE[int(bit)])
    return result


def specification(appendants):
    """Largest-power recursive split, independent of adjacent-pairing code."""
    leaves = [(app(B, routine(word if bit else '')), (phase, bit), None, None)
              for phase, word in enumerate(appendants) for bit in (0, 1)]

    def split(start, count):
        if count == 1:
            return leaves[start]
        power = 1 << ((count - 1).bit_length() - 1)
        left, right = split(start, power), split(start + power, count - power)
        return app(B, app(S, left[0], right[0])), None, left, right
    return split(0, len(leaves))


def route_for(count, index):
    if count == 1:
        return ()
    power = 1 << ((count - 1).bit_length() - 1)
    return ((0,) + route_for(power, index) if index < power else
            (1,) + route_for(count - power, index - power))


def chosen(spec, route, response, corrupt_depth=None, depth=0):
    if not route:
        return app(S, AUDIT, response)
    side = route[0]
    child = chosen(spec[2 + side], route[1:], response, corrupt_depth, depth + 1)
    dormant = app(S if corrupt_depth == depth else spec[3 - side][0], app(S, S))
    branch = App(child, dormant) if side == 0 else App(dormant, child)
    return app(S, S, branch)


def local(dispatcher, carrier=S, *, marked=False):
    halt = app(S, AUDIT, app(app(B, S), carrier)) if marked else App(HALT, carrier)
    return app(halt, dispatcher, app(S, AUDIT, S), app(S, AUDIT))


def completed(appendants, phase, bit, accumulator, *, marked=False, history_delta=0,
              corrupt_depth=None):
    route = route_for(2 * len(appendants), 2 * phase + bit)
    response = App(PI, accumulator)
    count = (len(appendants[phase]) if bit else 0) + history_delta
    for _ in range(count):
        response = App(response, AUDIT)
    return local(chosen(specification(appendants), route, response, corrupt_depth), marked=marked)


def arguments(term):
    if (isinstance(term, App) and isinstance(term.left, App)
            and isinstance(term.left.left, App) and term.left.left.left is S):
        return term.left.left.right, term.left.right, term.right
    return None


def contract(term, address):
    parents = []
    for side in address:
        parents.append((term, side))
        term = term.left if side == 0 else term.right
    x, y, z = arguments(term)
    result = app(app(x, z), app(y, z))
    for parent, side in reversed(parents):
        result = App(result, parent.right) if side == 0 else App(parent.left, result)
    return result


def equal_tree(left, right):
    pending, seen = [(left, right)], set()
    while pending:
        left, right = pending.pop()
        if left is right:
            continue
        if not isinstance(left, App) or not isinstance(right, App):
            return False
        pair = id(left), id(right)
        if pair not in seen:
            seen.add(pair)
            pending.extend(((left.left, right.left), (left.right, right.right)))
    return True


def select(table, term, max_ticks=3_000_000, seconds=20):
    state = Configuration(table.start, Cursor.at(term))
    deadline = time.monotonic() + seconds
    for tick in range(max_ticks + 1):
        if table.status(state.control) in ('normal', 'Rdx'):
            return state
        if tick % 1024 == 0 and time.monotonic() > deadline:
            raise AssertionError('independent review selection deadline')
        state = step(table, state)
    raise AssertionError('independent review selection microtick limit')


def probe(table, term):
    state = Configuration(table.start, Cursor.at(term))
    for _ in range(table.tick_bound + 1):
        answer = table.answer(state.control)
        if answer is not None:
            return answer, state.cursor
        state = probes.step(table, state)
    raise AssertionError('acyclic row probe exceeded its static bound')


@lru_cache(maxsize=None)
def trees(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for cut in range(1, leaves)
                 for left in trees(cut) for right in trees(leaves - cut))


def first_redex(term):
    pending = [term]
    while pending:
        term = pending.pop()
        if arguments(term) is not None:
            return True
        if isinstance(term, App):
            pending.extend((term.right, term.left))
    return False


class IndependentPeriodicSyntaxTests(unittest.TestCase):
    def test_largest_power_layout_exact_source_code_and_every_route(self):
        for period in (1, 3, 4, 5, 6, 7, 9, 16, 17):
            appendants = tuple(('01', '', '01')[phase % 3] for phase in range(period))
            p = PatternFamily(cts.Program(appendants), required_period=None)
            self.assertTrue(equal_tree(p.dispatch.code, specification(appendants)[0]))
            routes = [route_for(2 * period, index) for index in range(2 * period)]
            self.assertEqual(p.routes, tuple(routes))
            self.assertEqual(len(set(routes)), 2 * period)
            for index, (_, path, label) in enumerate(p.dispatch_records()):
                self.assertEqual(label, divmod(index, 2))
                self.assertEqual(path, routes[index])
                self.assertEqual(p.route_for(label), routes[index])
            self.assertEqual([phase for phase, _ in p.phase_labels()],
                             [0] + [((index // 2) + 1) % period
                                    for _ in range(2) for index in range(2 * period)])

    def test_completed_rows_reject_wrong_histories_and_every_dormant_code(self):
        for appendants in (('01', '', '01'), ('',) * 5):
            p = PatternFamily(cts.Program(appendants), required_period=None)
            accumulator = app(LIVE[1], app(LIVE[0], S))
            for marked in (False, True):
                table = compile_rows(p.local_rows('marked' if marked else 'fresh'))
                for phase in range(len(appendants)):
                    for bit in (0, 1):
                        kwargs = dict(marked=marked)
                        term = completed(appendants, phase, bit, accumulator, **kwargs)
                        answer, cursor = probe(table, term)
                        self.assertTrue(answer)
                        self.assertIs(cursor.focus, accumulator)
                        route = route_for(2 * len(appendants), 2 * phase + bit)
                        count = len(appendants[phase]) if bit else 0
                        address = SHELL + tuple(edge for side in route for edge in (1, side))
                        self.assertEqual(cursor.path, address + (1,) + (0,) * count + (1,))
                        for delta in ((-1, 1) if count else (1,)):
                            bad = completed(appendants, phase, bit, accumulator,
                                            history_delta=delta, **kwargs)
                            answer, cursor = probe(table, bad)
                            self.assertFalse(answer)
                            self.assertEqual(cursor.path, ())
                            self.assertIs(cursor.root, bad)
                        for depth in range(len(route)):
                            bad = completed(appendants, phase, bit, accumulator,
                                            corrupt_depth=depth, **kwargs)
                            answer, cursor = probe(table, bad)
                            self.assertFalse(answer)
                            self.assertEqual(cursor.path, ())

    def test_all_phase_dispatch_uses_retained_carrier_and_ignores_decoy_audit(self):
        appendants = ('01', '', '01')
        p = PatternFamily(cts.Program(appendants), required_period=None)
        builder = GraphBuilder()
        no, terminal = builder.uniform('normal'), builder.uniform('contracted')
        yes = builder.uniform('Rdx', terminal)
        start = compile_dispatcher(builder, p, yes, no)
        table = SelectorTable(builder.finish(), start)
        for phase in range(3):
            for bit in (0, 1):
                previous = completed(appendants, (phase - 1) % 3, 0, S)
                decoy = completed(appendants, phase, 0, app(LIVE[1 - bit], S))
                carrier = app(S, previous, App(VALUES[bit], decoy))
                dispatcher = app(specification(appendants)[0], AUDIT)
                path = ()
                expected = [()]
                for side in route_for(6, 2 * phase + bit):
                    expected.extend((path + (1,), path + (1, side)))
                    path += (1, side)
                for address in expected:
                    term = local(dispatcher, carrier)
                    selected = select(table, term)
                    self.assertEqual(table.status(selected.control), 'Rdx')
                    self.assertEqual(selected.cursor.path, SHELL + address)
                    self.assertIs(selected.cursor.root, term)
                    self.assertIsNotNone(arguments(selected.cursor.focus))
                    dispatcher = contract(dispatcher, address)
                selected = select(table, local(dispatcher, carrier))
                self.assertEqual(table.status(selected.control), 'normal')
                self.assertEqual(selected.cursor.path, ())


class IndependentPeriodOneRuntimeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = cts.Program(('01',))
        cls.table = periodic_selector.selector_table(cls.program, max_states=129_268)

    @classmethod
    def tearDownClass(cls):
        del cls.table
        periodic_selector.selector_table.cache_clear()
        gc.collect()

    def test_exact_budget_cache_types_and_failure_not_cached(self):
        self.assertEqual(len(self.table.states), 129_268)
        self.assertEqual(self.table.start, 111_742)
        self.assertIs(self.table, periodic_selector.selector_table(self.program, max_states=129_268))
        with self.assertRaises(ValueError):
            periodic_selector.selector_table(self.program, max_states=129_268.0)
        for kwargs in ({'max_phases': 0}, {'max_phases': True}, {'max_phases': 1.0},
                       {'max_appendant_bits': False}, {'max_states': False}):
            with self.assertRaises(ValueError):
                periodic_selector.selector_table(self.program, **kwargs)
        with self.assertRaisesRegex(periodic_selector.CompilationLimit, 'phases'):
            periodic_selector.selector_table(cts.Program(('',) * 17), max_states=10)
        with self.assertRaisesRegex(periodic_selector.CompilationLimit, 'appendant bits'):
            periodic_selector.selector_table(cts.Program(('1' * 129,)), max_states=10)
        with patch('s_only.program_selector_parts.patterns.PatternFamily',
                   side_effect=AssertionError('expanded syntax despite state cap')):
            with self.assertRaisesRegex(periodic_selector.CompilationLimit, 'states'):
                periodic_selector.selector_table(cts.Program(('1' * 129,) * 17),
                                                 max_states=10, max_phases=None,
                                                 max_appendant_bits=None)
        self.assertIs(self.table, periodic_selector.selector_table(self.program, max_states=129_268))
        self.assertEqual(periodic_selector.selector_table.cache_info().currsize, 1)

    def test_unrelated_malformed_and_deep_terms_still_select_single_native_steps(self):
        unrelated = [term for size in range(1, 8) for term in trees(size)]
        self.assertEqual(len(unrelated), 197)
        malformed = [completed(('01',), 0, 1, S, history_delta=delta)
                     for delta in (-1, 1)]
        malformed += [completed(('01',), 0, 1, S, corrupt_depth=0)]
        deep_normal = deep_redex = S
        for _ in range(1100):
            deep_normal = App(S, deep_normal)
            deep_redex = App(deep_redex, S)
        for term in unrelated + malformed + [deep_normal, deep_redex]:
            selected = select(self.table, term)
            self.assertIs(selected.cursor.root, term)
            if not first_redex(term):
                self.assertEqual(self.table.status(selected.control), 'normal')
                self.assertIs(step(self.table, selected), selected)
            else:
                self.assertEqual(self.table.status(selected.control), 'Rdx')
                expected = contract(term, selected.cursor.path)
                terminal = step(self.table, selected)
                self.assertEqual(self.table.status(terminal.control), 'contracted')
                self.assertIs(step(self.table, terminal), terminal)
                self.assertTrue(equal_tree(erase(terminal.cursor), expected))
        for invalid in (None, 'S', (), 0):
            with self.assertRaises(TypeError):
                periodic_selector.select_path(invalid, self.table)
        self.assertIsNone(periodic_selector.reduce_once(S, self.table))

    def test_native_nonempty_and_empty_checkpoints_independent_source_oracle(self):
        check_native(self, self.program, self.table, seeds=('110', ''), horizon=2)


def check_native(test, program, table, *, seeds, horizon, max_nodes=5_000_000):
    reader = cts_reader.compile_reader(program)
    saved = []
    for seed in seeds:
        term = encoding.encode(program, seed)
        word, phase = seed, 0
        expected = [{'horizon': 0, 'phase': 0, 'data': seed}]
        for index in range(1, horizon + 1):
            if word:
                word = word[1:] + (program.appendants[phase] if word[0] == '1' else '')
            phase = (phase + 1) % len(program.appendants)
            expected.append({'horizon': index, 'phase': phase, 'data': word})
        found_horizons = []
        deadline = time.monotonic() + 90
        with patch('s_only.cts.step', side_effect=AssertionError('source oracle consulted')):
            for count in range(181):
                test.assertLess(time.monotonic(), deadline)
                test.assertLessEqual(nodes(term), max_nodes)
                found = reader.decode(term)
                if found is not None:
                    test.assertEqual(found, expected[found['horizon']])
                    found_horizons.append(found['horizon'])
                    saved.append(term)
                    if found['horizon'] == horizon:
                        break
                selected = select(table, term)
                test.assertEqual(table.status(selected.control), 'Rdx')
                test.assertIs(selected.cursor.root, term)
                increase = nodes(arguments(selected.cursor.focus)[2]) - 1
                test.assertLessEqual(nodes(term) + increase, max_nodes)
                expected_term = contract(term, selected.cursor.path)
                terminal = step(table, selected)
                test.assertEqual(table.status(terminal.control), 'contracted')
                test.assertIs(step(table, terminal), terminal)
                term = erase(terminal.cursor)
                test.assertTrue(equal_tree(term, expected_term))
            else:
                test.fail('independent 180-contraction allowance exhausted')
        test.assertEqual(found_horizons, list(range(horizon + 1)))
    # Reordered samples remain root/start-only, even with every source and
    # construction entry point denied after the immutable graph exists.
    expected_paths = [select(table, sample).cursor.path for sample in saved]
    with ExitStack() as stack:
        for target in ('s_only.cts.step', 's_only.cts_reader.CompiledReader.decode',
                       's_only.encoding.compile_program', 's_only.program_selector.selector_table',
                       's_only.periodic_selector.selector_table', 's_only.root_selector.selector_table',
                       's_only.program_selector_parts.patterns.PatternFamily'):
            stack.enter_context(patch(target, side_effect=AssertionError('auxiliary runtime call')))
        for index in reversed(range(len(saved))):
            test.assertEqual(select(table, saved[index]).cursor.path, expected_paths[index])
    with test.assertRaises(StopIteration):
        cts.step(program, cts.Configuration('', 0))


class IndependentPeriodThreeRuntimeTests(unittest.TestCase):
    def test_native_repeated_code_program_against_independent_source_oracle(self):
        periodic_selector.selector_table.cache_clear()
        program = cts.Program(('01', '', '01'))
        table = periodic_selector.selector_table(program, max_states=694_400)
        try:
            self.assertEqual(len(table.states), 694_400)
            self.assertEqual(table.start, 621_444)
            check_native(self, program, table, seeds=('110', ''), horizon=2)
        finally:
            del table
            periodic_selector.selector_table.cache_clear()
            gc.collect()


if __name__ == '__main__':
    unittest.main()
