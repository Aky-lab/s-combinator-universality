"""Independent, bounded checks of prospective priority-selected marker events."""
from contextlib import ExitStack
from dataclasses import FrozenInstanceError, fields
from functools import lru_cache
from itertools import cycle
import json
from pathlib import Path
import time
import unittest
from unittest.mock import patch

from s_only import marker_observer as observer
from s_only.cts import Program
from s_only.encoding import B, HALT, LIVE, PI, compile_program, encode
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit
from s_only.program_selector_parts.patterns import PatternFamily
from s_only.reduction import at, contract_at
from s_only.root_selector import selector_table, select_cursor
from s_only.selector_parts.graph import Command, GraphBuilder
from s_only.terms import App, S, nodes, prefix


ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = Program(('1', ''))


@lru_cache(maxsize=1)
def original_table():
    return observer.observer_table(ORIGINAL)


def app(*terms):
    result = terms[0]
    for term in terms[1:]:
        result = App(result, term)
    return result


def structural_marker(term):
    """Test-only literal predicate, without generated patterns or decoding.

    HALT = (S S) ((S S) S). The right payload of HALT payload is opaque.
    """
    def b(node):
        return (isinstance(node, App) and isinstance(node.left, type(S))
                and isinstance(node.right, type(S)))
    if not isinstance(term, App) or not isinstance(term.left, App):
        return False
    code = term.left
    return (b(code.left) and isinstance(code.right, App)
            and b(code.right.left) and isinstance(code.right.right, type(S)))


@lru_cache(maxsize=1)
def priority_table():
    """External reference assembly ends before any shape test or fallback."""
    from s_only.program_selector_parts.active import compile_active
    from s_only.program_selector_parts.priority import compile_fresh, compile_marked
    builder = GraphBuilder()
    no, yes = builder.uniform('false'), builder.uniform('true')
    p = PatternFamily(ORIGINAL)
    active = compile_active(builder, p, yes, no)
    marked = compile_marked(builder, p, yes, builder.root(active))
    fresh = compile_fresh(builder, p, yes, builder.root(marked))
    return observer.ObserverTable(builder.finish(), fresh)


def bounded(table, term, *, max_ticks=1_000_000, seconds=10):
    """Test-driver counters are external to the finite runtime configuration."""
    state = Configuration(table.start, Cursor.at(term))
    deadline = time.monotonic() + seconds
    bound = min(max_ticks, table.linear_coefficient * nodes(term))
    for tick in range(bound + 1):
        if table.answer(state.control) is not None:
            return state, tick
        if tick % 1024 == 0 and time.monotonic() > deadline:
            raise AssertionError('external marker-observer time cap')
        state = observer.step(table, state)
    raise AssertionError('external marker-observer microtick cap')


def route(leaves, index):
    # Largest-power partition, independent of adjacent-pair compiler traversal.
    if leaves == 1:
        return ()
    cut = 1 << ((leaves - 1).bit_length() - 1)
    return ((0,) + route(cut, index) if index < cut
            else (1,) + route(leaves - cut, index - cut))


def chosen(code, address, response, audit):
    if not address:
        return app(S, audit, response)
    left, right = code.right.left.right, code.right.right
    body = (App(chosen(left, address[1:], response, audit), App(right, audit))
            if address[0] == 0 else
            App(App(left, audit), chosen(right, address[1:], response, audit)))
    return app(S, audit, body)


def completed(compiled, phase=0, bit=0, carrier=S, *, marked=False, audit=S):
    response = App(PI, carrier)
    for _ in range(len(compiled.program.appendants[phase]) if bit else 0):
        response = App(response, audit)
    address = route(len(compiled.action_terms), 2 * phase + bit)
    dispatch = chosen(compiled.actions, address, response, audit)
    halt = app(S, audit, App(App(B, S), audit)) if marked else App(HALT, audit)
    return app(halt, dispatch, app(S, audit, audit), App(S, audit))


def pending(compiled, child):
    environment = App(S, app(S, compiled.act, App(S, S)))
    return app(environment, S, child)


@lru_cache(maxsize=None)
def small_terms(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for count in range(1, leaves)
                 for left in small_terms(count) for right in small_terms(leaves - count))


def instantiate(pattern, values):
    if pattern == '_':
        return next(values)
    if pattern == 'S':
        return S
    return App(instantiate(pattern[0], values), instantiate(pattern[1], values))


class MarkerObserverTests(unittest.TestCase):
    def assert_oracle(self, term):
        table = original_table()
        selected, _ = bounded(priority_table(), term)
        actual, _ = bounded(table, term)
        expected = (priority_table().answer(selected.control)
                    and structural_marker(selected.cursor.focus))
        self.assertEqual(table.answer(actual.control), expected)
        self.assertEqual(actual.cursor.path, selected.cursor.path)
        self.assertIs(actual.cursor.root, term)
        self.assertIs(observer.step(table, actual), actual)
        return actual

    def test_fresh_shape_and_exact_commit_occurrence(self):
        compiled = compile_program(ORIGINAL)
        table = original_table()
        for phase in range(2):
            for bit in (0, 1):
                for audit in (S, App(S, S), app(S, S, S, S)):
                    fresh = completed(compiled, phase, bit, audit=audit)
                    # The completed response is not itself a fresh halt field.
                    self.assertFalse(structural_marker(fresh))
                    self.assertTrue(structural_marker(at(fresh, (0, 0, 0))))
                    for source, address in ((fresh, (0, 0, 0)),
                                            (pending(compiled, fresh), (1, 0, 0, 0))):
                        state = self.assert_oracle(source)
                        self.assertTrue(table.answer(state.control))
                        self.assertEqual(state.cursor.path, address)
                        # Exactly the selected redex becomes S a (HALT_TAG a).
                        rewritten = contract_at(source, address)
                        self.assertFalse(structural_marker(at(rewritten, address)))
                        self.assertEqual(prefix(at(rewritten, address)),
                                         prefix(app(S, audit, App(App(B, S), audit))))
                    marked = completed(compiled, phase, bit, marked=True, audit=audit)
                    self.assertFalse(table.answer(self.assert_oracle(marked).control))
                    live = completed(compiled, phase, bit, App(LIVE[0], S), audit=audit)
                    self.assertFalse(table.answer(self.assert_oracle(live).control))
                    # A fresh Local under an unregistered right parent is not admitted.
                    self.assertFalse(table.answer(self.assert_oracle(App(S, fresh)).control))

    def test_no_euler_fallback_or_any_occurrence_scan(self):
        for payload in (S, App(S, S), app(S, S, S, S)):
            term = App(HALT, payload)
            self.assertTrue(structural_marker(term))
            selected = select_cursor(term, selector_table())
            self.assertEqual(selected.path, ())
            self.assertFalse(observer.accepts(term, original_table()))
            self.assertFalse(observer.accepts(App(S, term), original_table()))

    def test_all_86_original_samples_and_no_tree_mutation(self):
        fixture = json.loads((ROOT / 'fixtures/queue_101_path.json').read_text())
        term = encode(ORIGINAL, '101')
        observed = []
        for index in range(len(fixture['steps']) + 1):
            before = prefix(term)
            actual = self.assert_oracle(term)
            if original_table().answer(actual.control):
                observed.append(index)
            self.assertEqual(prefix(term), before)
            if index < len(fixture['steps']):
                term = contract_at(term, tuple(map(int, fixture['steps'][index]['path'])))
        self.assertEqual(index + 1, 86)
        self.assertEqual(observed, [])

    def test_empty_and_nonempty_native_signal_timing_is_not_checkpoint_timing(self):
        # Reader/source semantics are test oracles only; the observer never imports them.
        from s_only.queue_fixture import decode
        cases = (
            ('', 20, [19], [(0, ''), (20, '')]),
            ('0', 21, [20], [(0, '0'), (21, '')]),
            ('1', 87, [55, 86], [(0, '1'), (22, '1'), (87, '')]),
            ('00', 81, [51, 80], [(0, '00'), (20, '0'), (81, '')]),
            ('10', 85, [], [(0, '10'), (22, '01'), (85, '1')]),
            ('11', 85, [], [(0, '11'), (22, '11'), (85, '1')]),
        )
        for word, last, expected_markers, expected_checkpoints in cases:
            term = encode(ORIGINAL, word)
            markers, checkpoints = [], []
            for index in range(last + 1):
                state, _ = bounded(original_table(), term)
                self.assertIs(state.cursor.root, term)
                if original_table().answer(state.control):
                    markers.append(index)
                    self.assertTrue(structural_marker(state.cursor.focus))
                checkpoint = decode(term)
                if checkpoint is not None:
                    checkpoints.append((index, checkpoint['data']))
                if index != last:
                    selected = select_cursor(term, selector_table())
                    term = contract_at(term, selected.path)
            with self.subTest(word=word):
                self.assertEqual(markers, expected_markers)
                self.assertEqual(checkpoints, expected_checkpoints)

    def test_626_small_malformed_trees_and_pattern_shaped_mutations(self):
        checked = 0
        for leaves in range(1, 9):
            for term in small_terms(leaves):
                self.assert_oracle(term)
                checked += 1
        self.assertEqual(checked, 626)
        p = PatternFamily(ORIGINAL)
        patterns = ((p.base_pattern(), p.pending_pattern()) + p.local_patterns('fresh')
                    + p.local_patterns('marked') + tuple(row[1] for row in p.fuel_rows()))
        holes = (S, App(S, S), app(S, S, S, S))
        for pattern in patterns:
            for offset in range(3):
                candidate = instantiate(pattern, cycle(holes[offset:] + holes[:offset]))
                for term in (candidate, App(candidate, S), App(S, candidate)):
                    self.assert_oracle(term)

    def test_runtime_isolation_root_reset_and_immutable_finite_state(self):
        table = original_table()
        compiled = compile_program(ORIGINAL)
        positive = completed(compiled)
        negative = App(HALT, S)
        self.assertEqual([item.name for item in fields(table)], ['states', 'start'])
        self.assertEqual([item.name for item in fields(Configuration)], ['control', 'cursor'])
        self.assertEqual([item.name for item in fields(Cursor)], ['focus', 'parents'])
        self.assertEqual(len(table.states), 257308)
        self.assertEqual({entry.command for row in table.states for entry in row},
                         {'stay', 'L', 'R', 'U', 'true', 'false'})
        with self.assertRaises(FrozenInstanceError):
            table.start = 0
        with self.assertRaises(TypeError):
            observer.execute(positive, None)
        with self.assertRaises(TypeError):
            observer.accepts(positive)
        def forbidden(*args, **kwargs):
            raise AssertionError('runtime consulted a forbidden helper')
        targets = (
            's_only.marker_observer.observer_table', 's_only.cts.step',
            's_only.cts_reader.CompiledReader.decode', 's_only.queue_fixture.decode',
            's_only.encoding.compile_program', 's_only.probes.compile_pattern',
            's_only.probes.compile_rows', 's_only.terms.nodes', 's_only.terms.prefix',
            's_only.program_selector_parts.patterns.PatternFamily',
            's_only.root_selector.select_cursor', 's_only.root_selector._euler',
            's_only.reduction.root_arguments', 's_only.reduction.contract_at',
            's_only.terms.App.__eq__', 's_only.terms.App.__hash__',
        )
        with ExitStack() as stack:
            for target in targets:
                stack.enter_context(patch(target, forbidden))
            # Deliberate reordering and repetition, no previous cursor is supplied.
            for source, expected in ((positive, True), (negative, False),
                                     (S, False), (positive, True), (negative, False)):
                result = observer.execute(source, table)
                self.assertEqual(result.answer, expected)
                self.assertIs(result.cursor.root, source)

    def test_table_rejects_mutation_dynamic_targets_and_nonuniform_terminals(self):
        def row(command, target=None):
            return (Command(command, target),) * 6
        bad = (
            (row('Rdx', 0),), (row('stay', True),), (row('stay', 1),),
            (row('true', 0),), (row('normal'),),
            ((Command('true'),) + (Command('false'),) * 5,),
            ([Command('false')] * 6,),
        )
        for states in bad:
            with self.assertRaises(ValueError):
                observer.ObserverTable(states, 0)
        with self.assertRaises(ValueError):
            observer.ObserverTable((row('false'),), True)
        table = observer.ObserverTable((row('false'),), 0)
        for control in (True, -1, 1):
            with self.assertRaises(ValueError):
                table.answer(control)
        with self.assertRaises(ValueError):
            table.transition(0, 'leaf', 'root')

    def test_compile_budgets_and_resource_failures(self):
        for name, invalid in (('max_states', (0, -1, True, 1.5)),
                              ('max_appendant_bits', (-1, True, 1.5)),
                              ('max_phases', (0, -1, True, 1.5))):
            for value in invalid:
                with self.assertRaises(ValueError):
                    observer.observer_table(ORIGINAL, **{name: value})
        with self.assertRaises(TypeError):
            observer.observer_table(('1', ''))
        for settings in ({'max_states': 1}, {'max_appendant_bits': 0}, {'max_phases': 1}):
            with patch('s_only.program_selector_parts.patterns.PatternFamily',
                       side_effect=AssertionError('syntax expanded before cap rejection')):
                with self.assertRaises(CompilationLimit):
                    observer.observer_table(ORIGINAL, **settings)
        count = len(original_table().states)
        self.assertEqual(len(observer.observer_table(ORIGINAL, max_states=count).states), count)
        with self.assertRaises(CompilationLimit):
            observer.observer_table(ORIGINAL, max_states=count - 1)
        with patch('s_only.program_selector_parts.patterns.PatternFamily', side_effect=RecursionError):
            with self.assertRaisesRegex(CompilationLimit, 'recursion'):
                observer.observer_table(ORIGINAL)

    def test_positive_period_static_graphs_and_unbalanced_routes(self):
        for words in (('01',), ('', '1', ''), ('1', '', '0', '', '')):
            program = Program(words)
            compiled = compile_program(program)
            table = observer.observer_table(program, max_appendant_bits=None,
                                            max_phases=None)
            for phase in range(len(words)):
                for bit in (0, 1):
                    fresh = completed(compiled, phase, bit)
                    state, _ = bounded(table, fresh)
                    self.assertTrue(table.answer(state.control), (words, phase, bit))
                    self.assertEqual(state.cursor.path, (0, 0, 0))
                    marked = completed(compiled, phase, bit, marked=True)
                    state, _ = bounded(table, marked)
                    self.assertFalse(table.answer(state.control))
            self.assertFalse(observer.accepts(encode(program, '1'), table))


if __name__ == '__main__':
    unittest.main()
