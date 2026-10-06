"""Independent integration review of program-static controllers and readers.

Only finite bounded experiments are asserted.  The source oracle, budgets,
paths and retained samples live in this review driver, never in the selector.
Synthetic reader fixtures establish syntax acceptance, not reachability.
"""
from contextlib import ExitStack
from functools import lru_cache
import time
import unittest
from unittest.mock import patch

from s_only import cts, cts_reader, encoding, program_selector, root_selector
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.selector_parts.graph import Command
from s_only.terms import App, S, nodes


def app(*terms):
    result = terms[0]
    for term in terms[1:]:
        result = App(result, term)
    return result


# Mathematical constructors transcribed independently of both implementations.
B = app(S, S)
PI = app(S, B)
C0 = app(S, B, B)
VALUES = (app(S, C0), app(S, app(S, C0)))
LIVE = tuple(app(B, tag) for tag in VALUES)
HALT_TAG = app(B, S)
HALT = app(B, HALT_TAG)


def literal_word(word):
    result = S
    for bit in word:
        result = app(LIVE[int(bit)], result)
    return result


def dispatch_spec(appendants):
    forest = []
    for phase, word in enumerate(appendants):
        for bit in (0, 1):
            action = PI
            for symbol in reversed(word if bit else ''):
                action = app(S, app(S, action), LIVE[int(symbol)])
            forest.append((app(B, action), (phase, bit), None, None))
    while len(forest) > 1:
        following = []
        for index in range(0, len(forest), 2):
            if index + 1 == len(forest):
                following.append(forest[index])
            else:
                left, right = forest[index:index + 2]
                following.append((app(B, app(S, left[0], right[0])), None, left, right))
        forest = following
    return forest[0]


def route(spec, target, response, audit):
    if spec[1] is not None:
        return app(S, audit(), response) if spec[1] == target else None
    chosen = route(spec[2], target, response, audit)
    if chosen is not None:
        return app(S, audit(), app(chosen, app(spec[3][0], audit())))
    chosen = route(spec[3], target, response, audit)
    if chosen is not None:
        return app(S, audit(), app(app(spec[2][0], audit()), chosen))
    return None


def synthetic_checkpoint(appendants, word, horizon, *, bit=1, audit=lambda: S,
                         wrong_phase=False, continuation_pair=(S, S)):
    spec = dispatch_spec(appendants)
    phase = ((horizon if wrong_phase else horizon - 1) % len(appendants))

    def environment(payload):
        return app(S, app(S, app(S, HALT, spec[0]), app(S, payload)))

    # Deliberately unrelated emitted labels remain legal ActionParser syntax.
    queue = literal_word(word)
    queue = app(S, queue, app(VALUES[0], audit()))  # a transparent tombstone
    outer, inner = continuation_pair
    accumulator = app(outer, app(environment(queue), app(B, environment(audit())), inner), audit())
    response = app(PI, accumulator)
    for _ in appendants[phase] if bit else '':
        response = app(response, audit())
    selected = route(spec, (phase, bit), response, audit)
    numeral = C0
    for _ in range(horizon + 1):
        numeral = app(B, numeral)
    terminal = app(numeral, numeral, environment(audit()))
    halt = app(HALT, audit()) if word else app(S, audit(), app(HALT_TAG, audit()))
    return app(halt, selected, app(S, audit(), audit()), app(terminal, audit()))


def redex_arguments(term):
    if (isinstance(term, App) and isinstance(term.left, App)
            and isinstance(term.left.left, App) and term.left.left.left is S):
        return term.left.left.right, term.left.right, term.right
    return None


def first_redex(term):
    pending = [(term, ())]
    while pending:
        current, address = pending.pop()
        if redex_arguments(current) is not None:
            return address
        if isinstance(current, App):
            pending.extend(((current.right, address + (1,)),
                            (current.left, address + (0,))))
    return None


def independent_contract(term, address):
    parents = []
    for side in address:
        parents.append((term, side))
        term = term.left if side == 0 else term.right
    x, y, z = redex_arguments(term)
    result = app(app(x, z), app(y, z))
    for parent, side in reversed(parents):
        result = App(result, parent.right) if side == 0 else App(parent.left, result)
    return result


def equal_tree(left, right):
    pending, checked = [(left, right)], set()
    while pending:
        left, right = pending.pop()
        if left is right:
            continue
        if not isinstance(left, App) or not isinstance(right, App):
            return False
        pair = id(left), id(right)
        if pair not in checked:
            checked.add(pair)
            pending.extend(((left.left, right.left), (left.right, right.right)))
    return True


def bounded_selection(table, term, *, max_ticks=2_000_000, seconds=15):
    state = Configuration(table.start, Cursor.at(term))
    deadline = time.monotonic() + seconds
    for ticks in range(max_ticks + 1):
        if table.status(state.control) in ('normal', 'Rdx'):
            return state
        if ticks % 1024 == 0 and time.monotonic() > deadline:
            raise AssertionError('review wall-time allowance exceeded')
        state = program_selector.step(table, state)
    raise AssertionError('review microtick allowance exceeded')


@lru_cache(maxsize=None)
def small_trees(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for cut in range(1, leaves)
                 for left in small_trees(cut) for right in small_trees(leaves - cut))


class ReaderIndependentReviewTests(unittest.TestCase):
    def test_unbalanced_repeated_code_routes_retain_their_phase_labels(self):
        # Ten identical leaf codes still have ten distinct structural labels.
        appendants = ('',) * 5
        program = cts.Program(appendants)
        reader = cts_reader.compile_reader(program)
        for phase in range(5):
            for bit in (0, 1):
                term = synthetic_checkpoint(appendants, '101', phase + 1, bit=bit)
                self.assertEqual(reader.decode(term),
                                 {'horizon': phase + 1, 'phase': (phase + 1) % 5,
                                  'data': '101'})
                self.assertIsNone(reader.decode(synthetic_checkpoint(
                    appendants, '101', phase + 1, bit=bit, wrong_phase=True)))

    def test_every_audit_subtree_is_opaque_even_when_exponentially_shared(self):
        appendants = ('010', '11', '', '0010', '1')
        reader = cts_reader.compile_reader(cts.Program(appendants))
        # This DAG is finite but its unfolded tree has over 2**1200 nodes.
        # Entering it is forbidden, stronger than merely checking a fast run.
        huge = S
        for _ in range(1200):
            huge = App(huge, huge)
        opaque = set()

        def audit():
            value = App(huge, S)
            opaque.add(id(value))
            return value

        terms = [synthetic_checkpoint(appendants, word, horizon, audit=audit)
                 for horizon in range(1, 6) for word in ('', '10')]
        get = App.__getattribute__

        def guarded(term, name):
            if id(term) in opaque and name in ('left', 'right'):
                raise AssertionError('reader entered an opaque audit subtree')
            return get(term, name)

        with patch.object(App, '__getattribute__', guarded), \
             patch.object(App, '__eq__', side_effect=AssertionError('recursive equality')), \
             patch.object(App, '__hash__', side_effect=AssertionError('term hashing')):
            for index, term in enumerate(terms):
                horizon, word = index // 2 + 1, '' if index % 2 == 0 else '10'
                self.assertEqual(reader.decode(term),
                                 {'horizon': horizon, 'phase': horizon % 5, 'data': word})

    def test_repeated_continuation_compares_deep_equal_copies_and_rejects_change(self):
        left, right = S, S
        for _ in range(1600):
            left, right = App(left, S), App(right, S)
        reader = cts_reader.compile_reader(cts.Program(('01', '10', '')))
        term = synthetic_checkpoint(('01', '10', ''), '101', 1,
                                    continuation_pair=(left, right))
        self.assertEqual(reader.decode(term)['data'], '101')
        malformed = synthetic_checkpoint(('01', '10', ''), '101', 1,
                                         continuation_pair=(left, App(right, S)))
        self.assertIsNone(reader.decode(malformed))


class ReviewDriverBoundaryTests(unittest.TestCase):
    def test_large_program_reports_explicit_construction_limits(self):
        program = cts.Program(('1' * 1600, ''))
        with self.assertRaisesRegex(program_selector.CompilationLimit, 'appendant bits'):
            program_selector.selector_table(program, max_states=10)
        with patch('s_only.program_selector_parts.patterns.PatternFamily',
                   side_effect=AssertionError('expanded before tiny state budget')):
            with self.assertRaisesRegex(program_selector.CompilationLimit, 'states'):
                program_selector.selector_table(program, max_states=10,
                                                max_appendant_bits=None)

    def test_report_microtick_boundary_and_readonly_selection(self):
        from tools import program_selector_report as runner
        table = root_selector.SelectorTable((
            (Command('stay', 1),) * 6,
            (Command('Rdx', 2),) * 6,
            (Command('contracted'),) * 6,
        ), 0)
        term = app(S, S, S, S)
        selected, ticks = runner._select(table, term, 1, time.monotonic() + 5)
        self.assertEqual(ticks, 1)
        self.assertEqual(table.status(selected.control), 'Rdx')
        self.assertIs(selected.cursor.focus, term)
        looping = root_selector.SelectorTable(((Command('stay', 0),) * 6,), 0)
        with self.assertRaisesRegex(runner.ExperimentLimit, 'microtick'):
            runner._select(looping, term, 1, time.monotonic() + 5)
        with self.assertRaisesRegex(runner.ExperimentLimit, 'wall-clock'):
            runner._select(looping, term, 10, time.monotonic() - 1)


class SelectorIntegrationReviewTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = cts.Program(('01', '10'))
        cls.table = program_selector.selector_table(cls.program, max_states=600_000,
                                                    max_appendant_bits=128)

    @classmethod
    def tearDownClass(cls):
        del cls.table
        program_selector.selector_table.cache_clear()

    def test_graph_is_immutable_local_and_has_only_finite_primitive_targets(self):
        table = self.table
        self.assertEqual(tuple(type(table).__dataclass_fields__), ('states', 'start'))
        self.assertEqual(tuple(Configuration.__dataclass_fields__), ('control', 'cursor'))
        self.assertEqual(tuple(Cursor.__dataclass_fields__), ('focus', 'parents'))
        self.assertIs(type(table.states), tuple)
        self.assertEqual(len(OBSERVATIONS), 6)
        # Numerically equal float keys must not bypass validation via the cache.
        with self.assertRaises(ValueError):
            program_selector.selector_table(self.program, max_states=600_000.0,
                                            max_appendant_bits=128)
        with self.assertRaises(ValueError):
            program_selector.selector_table(self.program, max_states=600_000,
                                            max_appendant_bits=128.0)
        for row in table.states:
            self.assertIs(type(row), tuple)
            self.assertEqual(len(row), 6)
            for instruction in row:
                self.assertIs(type(instruction), Command)
                self.assertIn(instruction.command,
                              ('stay', 'L', 'R', 'U', 'Rdx', 'normal', 'contracted'))
                if instruction.next_state is not None:
                    self.assertIs(type(instruction.next_state), int)
                    self.assertTrue(0 <= instruction.next_state < len(table.states))
                if instruction.command == 'Rdx':
                    self.assertEqual(table.status(instruction.next_state), 'contracted')

    def test_small_unrelated_trees_normality_and_exactly_one_contraction(self):
        count = 0
        for leaves in range(1, 8):
            for term in small_trees(leaves):
                state = bounded_selection(self.table, term)
                self.assertIs(state.cursor.root, term)
                if first_redex(term) is None:
                    self.assertEqual(self.table.status(state.control), 'normal')
                    self.assertIs(program_selector.step(self.table, state), state)
                else:
                    self.assertEqual(self.table.status(state.control), 'Rdx')
                    self.assertIsNotNone(redex_arguments(state.cursor.focus))
                    result = program_selector.step(self.table, state)
                    self.assertEqual(self.table.status(result.control), 'contracted')
                    self.assertIs(program_selector.step(self.table, result), result)
                    self.assertTrue(equal_tree(program_selector.erase(result.cursor),
                                               independent_contract(term, state.cursor.path)))
                count += 1
        self.assertEqual(count, 197)

    def test_multibit_both_phases_against_independent_stopping_cts(self):
        # Both phases delete 1 and append two bits.
        # No empty state is reached, so this is ordinary stopping CTS semantics.
        term = encoding.encode(self.program, '110')
        reader = cts_reader.compile_reader(self.program)
        expected = [{'horizon': 0, 'phase': 0, 'data': '110'}]
        word, phase = '110', 0
        for horizon in range(1, 3):
            self.assertTrue(word)
            word = word[1:] + (self.program.appendants[phase] if word[0] == '1' else '')
            phase = (phase + 1) % 2
            expected.append({'horizon': horizon, 'phase': phase, 'data': word})
        samples, observed = {}, {}
        deadline = time.monotonic() + 90
        blocked = AssertionError('runtime consulted source semantics or checkpoint lookup')
        with patch('s_only.cts.step', side_effect=blocked), \
             patch('s_only.cts.Machine.tick', side_effect=blocked), \
             patch('s_only.queue_fixture.decode', side_effect=blocked):
            for contraction in range(151):
                self.assertLess(time.monotonic(), deadline)
                self.assertLess(nodes(term), 5_000_000)
                found = reader.decode(term)
                if found is not None:
                    self.assertLessEqual(found['horizon'], 2)
                    self.assertEqual(found, expected[found['horizon']])
                    observed[found['horizon']] = contraction
                    samples[found['horizon']] = term
                    if found['horizon'] == 2:
                        break
                state = bounded_selection(self.table, term)
                self.assertEqual(self.table.status(state.control), 'Rdx')
                self.assertIs(state.cursor.root, term)
                self.assertLess(nodes(term) + nodes(redex_arguments(state.cursor.focus)[2]) - 1,
                                5_000_000, 'next contraction exceeds expanded-node allowance')
                expected_term = independent_contract(term, state.cursor.path)
                result = program_selector.step(self.table, state)
                term = program_selector.erase(result.cursor)
                self.assertTrue(equal_tree(term, expected_term))
            else:
                self.fail('review 150-contraction allowance exceeded')
        self.assertEqual(set(observed), {0, 1, 2})
        # Unordered fresh invocations cannot depend on a saved CTS phase/index.
        selected = {horizon: bounded_selection(self.table, sample).cursor.path
                    for horizon, sample in samples.items()}
        blocked_names = (
            's_only.program_selector.selector_table',
            's_only.root_selector.selector_table',
            's_only.program_selector_parts.patterns.PatternFamily',
            's_only.encoding.compile_program', 's_only.cts.step',
            's_only.cts_reader.CompiledReader.decode', 's_only.queue_fixture.decode',
            's_only.selector_parts.graph.GraphBuilder.__init__',
            's_only.reduction.select_path', 's_only.reduction.contract_at',
            's_only.terms.prefix', 's_only.terms.nodes',
            'builtins.open', 'io.open', 'hashlib.sha256',
        )
        with ExitStack() as stack:
            for name in blocked_names:
                stack.enter_context(patch(name, side_effect=blocked))
            stack.enter_context(patch.object(App, '__eq__', side_effect=blocked))
            stack.enter_context(patch.object(App, '__hash__', side_effect=blocked))
            stack.enter_context(patch.object(Cursor, 'path', property(lambda _: (_ for _ in ()).throw(blocked))))
            stack.enter_context(patch.object(Cursor, 'root', property(lambda _: (_ for _ in ()).throw(blocked))))
            order = (2, 0, 1, 2, 0)
            outputs = [program_selector.execute(samples[index], self.table) for index in order]
        for index, output in zip(order, outputs):
            self.assertEqual(output.cursor.path, selected[index])
            self.assertTrue(equal_tree(program_selector.erase(output.cursor),
                                       independent_contract(samples[index], selected[index])))


if __name__ == '__main__':
    unittest.main()
