"""Independent syntax fixtures, current-tree readout and bounded legacy checks.

Fabricated F17 shells test the interface, never claimed UT19 S reachability.
"""
from contextlib import ExitStack
from dataclasses import replace
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from s_only import cts, cts_reader, encoding, s_event_readout as reader, ut19
from s_only.reduction import contract_at
from s_only.terms import App, S

ROOT = Path(__file__).resolve().parents[1]


def app(*items):
    out = items[0]
    for item in items[1:]:
        out = App(out, item)
    return out


# Direct mathematical transcription; independent of the new reader's code.
b = app(S, S)
pi = app(S, b)
c0 = app(pi, b)
values = (app(S, c0), app(S, app(S, c0)))
live = tuple(app(b, item) for item in values)
h = app(b, S)
halt = app(b, h)


def word(bits):
    result = S
    for bit in bits:
        result = app(live[int(bit)], result)
    return result


def tombstone(bit, predecessor, audit=S):
    return app(S, predecessor, app(values[bit], audit))


def spec(program):
    forest = []
    for phase, bits in enumerate(program.appendants):
        for bit in (0, 1):
            action = pi
            for value in reversed(bits if bit else ""):
                action = app(S, app(S, action), live[int(value)])
            forest.append((app(b, action), None, None, (phase, bit)))
    while len(forest) > 1:
        new = []
        for index in range(0, len(forest), 2):
            if index + 1 == len(forest):
                new.append(forest[index])
            else:
                left, right = forest[index:index + 2]
                new.append((app(b, app(S, left[0], right[0])), left, right, None))
        forest = new
    return forest[0]


def environment(tree, queue):
    return app(S, app(S, app(S, halt, tree[0]), app(S, queue)))


def base(tree, queue, outer=S, inner=S, seed=S, beta=S):
    return app(outer, app(environment(tree, queue), app(b, environment(tree, seed)), inner), beta)


def route(tree, label, response, audit=S):
    pending = [(tree, ())]
    while pending:
        item, path = pending.pop()
        if item[3] == label:
            out = app(S, audit, response)
            for parent, side in reversed(path):
                dormant = app(parent[2 if side == 0 else 1][0], audit)
                out = app(S, audit, app(out, dormant) if side == 0 else app(dormant, out))
            return out
        if item[3] is None:
            pending.extend(((item[2], path + ((item, 1),)), (item[1], path + ((item, 0),))))
    raise AssertionError("label not found")


def local(program, tree, accumulator, audit, label, *, marked=False,
          histories=None, opaque=S, continuation=S):
    count = len(program.appendants[label[0]]) if label[1] else 0
    action = app(pi, accumulator, *([opaque] * count if histories is None else histories))
    halt_field = app(S, opaque, app(h, audit)) if marked else app(halt, audit)
    return app(halt_field, route(tree, label, action, opaque),
               app(S, opaque, opaque), app(continuation, opaque))


def hot(symbols):
    return "".join("0" * (value - 1) + "1" + "0" * (19 - value) for value in symbols)


def small_event(value=0):
    return (18, 10) + (16,) * (4 ** (value + 1)) + (18, 10, 10, 10)


def node_count(term):
    seen, pending = set(), [term]
    while pending:
        item = pending.pop()
        if id(item) in seen:
            continue
        seen.add(id(item))
        if type(item) is App:
            pending.extend((item.left, item.right))
    return len(seen)


def raw_app(left=S, right=S):
    result = object.__new__(App)
    object.__setattr__(result, "left", left)
    object.__setattr__(result, "right", right)
    # Deliberately no cached _leaves field.
    return result


class EventTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = ut19.compile_cts()
        cls.tree = spec(cls.program)
        cls.bits = hot(small_event())[17:]
        cls.tail = cls.bits[1:]
        cls.carrier = base(cls.tree, word(cls.tail))
        # The mutable accumulator deliberately does NOT contain the answer.
        cls.shell = local(cls.program, cls.tree, base(cls.tree, word("111")),
                          cls.carrier, (17, 1))

    def test_recorded_event_tails_restore_plus_one_and_minus_one(self):
        data = json.loads((ROOT / "results/ut19_source.json").read_text())
        checked = []
        for fixture in data["fixtures"]:
            end = fixture["tag_and_cts_execution"]["end"]
            if end["outcome"] != "designated_event":
                continue
            bits = hot(end["tag_configuration"]["queue"])[17:]
            self.assertEqual(bits[:2], "10")
            self.assertEqual(len(bits), end["cts_word_bits"])
            carrier = base(self.tree, word(bits[1:]))
            shell = local(self.program, self.tree, S, carrier, (17, 1))
            result = reader.read_ut19_event(shell)
            self.assertEqual(result.values, {"+1": (1,), "-1": (0,)}[fixture["source_program"]])
            self.assertEqual(result.witness, ())
            self.assertLessEqual(result.work, reader.polynomial_work_bound(result.input_nodes))
            checked.append(fixture["source_program"])
        self.assertEqual(checked, ["+1", "-1"])

    def test_first_preorder_current_witness_and_shared_occurrences(self):
        shared = app(self.shell, self.shell)
        self.assertEqual(reader.find_ut19_event(shared), (0,))
        first = reader.read_ut19_event(app(S, shared))
        self.assertEqual(first.witness, (1, 0))
        self.assertEqual(first.values, (0,))
        # A fresh call must not retain the previous address.
        self.assertEqual(reader.read_ut19_event(self.shell).witness, ())
        self.assertIsNone(reader.find_ut19_event(S))
        with self.assertRaisesRegex(ValueError, "no completed"):
            reader.read_ut19_event(S)

    def test_exact_pattern_matches_independent_fixed_pattern(self):
        from tools.ut19_event_language_report import build_event_pattern
        from s_only.pattern_automaton import compile_pattern, evaluate
        _, pattern = build_event_pattern()
        automaton = compile_pattern(pattern)
        for term in (self.shell, app(S, self.shell), S,
                     local(self.program, self.tree, S, self.carrier, (16, 1)),
                     local(self.program, self.tree, S, self.carrier, (17, 0))):
            self.assertEqual(reader.find_ut19_event(term) is not None,
                             automaton.accepts(evaluate(automaton, term)))

    def test_histories_and_freshness_are_exact(self):
        for count in (0, 18, 20):
            term = local(self.program, self.tree, S, self.carrier, (17, 1), histories=[S] * count)
            self.assertIsNone(reader.find_ut19_event(term))
        marked = local(self.program, self.tree, S, self.carrier, (17, 1), marked=True)
        self.assertIsNone(reader.find_ut19_event(marked))

    def test_frozen_audit_not_working_accumulator_is_read(self):
        self.assertEqual(reader.read_s_event_result(self.shell), (0,))
        wrong_audit = local(self.program, self.tree, self.carrier, S, (17, 1))
        self.assertEqual(reader.find_ut19_event(wrong_audit), ())
        with self.assertRaises(ValueError):
            reader.read_s_event_result(wrong_audit)
        malformed_reset = local(self.program, self.tree, self.carrier,
                                base(self.tree, word("011")), (17, 1))
        with self.assertRaises(ValueError):
            reader.read_s_event_result(malformed_reset)

    def test_exact_resource_boundaries(self):
        result = reader.read_ut19_event(self.shell)
        limits = reader.SReadoutLimits(
            max_input_nodes=result.input_nodes, max_word_bits=len(self.bits),
            max_queue_symbols=(len(self.bits) + 17) // 19,
            max_counters=1, max_output_bits=1, max_work=result.work)
        self.assertEqual(reader.read_ut19_event(self.shell, limits=limits), result)
        for name in reader.SReadoutLimits.__dataclass_fields__:
            with self.subTest(name=name), self.assertRaises(reader.ResourceLimit):
                reader.read_ut19_event(self.shell, limits=replace(limits, **{name: getattr(limits, name) - 1}))
        adequate = reader.limits_for_input_nodes(result.input_nodes)
        self.assertEqual(reader.read_s_event_result(self.shell, limits=adequate), (0,))

    def test_no_runtime_evaluator_compiler_clock_or_private_queue(self):
        forbidden = (
            "s_only.cts.step", "s_only.cts.Machine", "s_only.ut19.source_step",
            "s_only.ut19.initial_source", "s_only.ut19.encode_source",
            "s_only.alternating_tag.step", "s_only.alternating_tag.evaluate",
            "s_only.alternating_tag.encode_word", "s_only.alternating_tag.decode_boundary",
            "s_only.ut19.compile_cts", "s_only.encoding.compile_program", "s_only.encoding.encode",
            "s_only.encoding.encode_word", "s_only.cts_reader.compile_reader",
            "s_only.cts_reader.CompiledReader._queue", "s_only.reduction.contract_at",
            "s_only.reduction.select_path", "time.monotonic", "time.perf_counter",
            "builtins.open", "io.open", "s_only.terms.prefix",
            "s_only.s_event_readout._compile_reference_grammar")
        with ExitStack() as stack:
            for name in forbidden:
                stack.enter_context(patch(name, side_effect=AssertionError(name)))
            stack.enter_context(patch.object(App, "__eq__", side_effect=AssertionError("term equality")))
            stack.enter_context(patch.object(App, "__hash__", side_effect=AssertionError("term hashing")))
            self.assertEqual(reader.read_s_event_result(self.shell), (0,))


class CarrierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = cts.Program(("1", ""))
        cls.tree = spec(cls.program)
        cls.reader = reader.compile_carrier_reader(cls.program)
        cls.reference = cts_reader.compile_reader(cls.program)

    def test_differential_all_carrier_subtrees_of_85_step_fixture(self):
        fixture = json.loads((ROOT / "fixtures/queue_101_path.json").read_text())
        term = encoding.encode(self.program, "101")
        checked, accepted = 0, 0
        for record in [None, *fixture["steps"]]:
            if record is not None:
                term = contract_at(term, tuple(map(int, record["path"])))
            seen, pending = set(), [term]
            while pending:
                node = pending.pop()
                if id(node) in seen:
                    continue
                seen.add(id(node))
                if type(node) is App:
                    pending.extend((node.left, node.right))
                try:
                    expected = self.reference._queue(node)
                except ValueError:
                    with self.assertRaises(ValueError):
                        self.reader.read_carrier(node)
                else:
                    self.assertEqual(self.reader.read_carrier(node), expected)
                    accepted += 1
                checked += 1
        self.assertGreater(checked, 3000)
        self.assertGreater(accepted, 100)

    def test_live_tombstone_nested_local_and_opaque_fields(self):
        opaque = S
        for _ in range(1300):
            opaque = app(opaque, opaque)
        payload = app(live[0], tombstone(1, word("01"), opaque))
        inner = local(self.program, self.tree,
                      base(self.tree, payload, seed=opaque, beta=opaque), opaque,
                      (0, 1), marked=True, opaque=opaque)
        carrier = app(live[1], inner)
        self.assertEqual(self.reader.read_carrier(carrier), "0101")
        # Opaque means semantically ignored, not exempt from syntax validation.
        object.__setattr__(opaque, "right", "bad")
        with self.assertRaises(ValueError):
            self.reader.read_carrier(carrier)

    def test_repeated_base_continuations_equal_and_unequal(self):
        a, bcopy = S, S
        for _ in range(1800):
            a, bcopy = app(a, a), app(bcopy, bcopy)
        equal = base(self.tree, word("101"), outer=a, inner=bcopy)
        cap = self.reader.limits_for_input_nodes(node_count(equal))
        self.assertEqual(self.reader.read_carrier(equal, limits=cap), "101")
        unequal = base(self.tree, word("101"), outer=a, inner=app(bcopy, S))
        with self.assertRaises(ValueError):
            self.reader.read_carrier(unequal)
        with self.assertRaises(reader.ResourceLimit):
            self.reader.read_carrier(equal, limits=replace(cap, max_work=20))

    def test_deep_linear_carrier_and_local_chains_are_iterative(self):
        carrier = base(self.tree, word("1"))
        for _ in range(2100):
            carrier = local(self.program, self.tree, app(live[0], carrier), S, (1, 0))
        cap = self.reader.limits_for_input_nodes(node_count(carrier))
        self.assertEqual(self.reader.read_carrier(carrier, limits=cap), "1" + "0" * 2100)

    def test_base_boundary_does_not_fall_through(self):
        self.assertEqual(self.reader.read_carrier(base(self.tree, S)), "")
        bad = base(self.tree, base(self.tree, word("01")))
        with self.assertRaises(ValueError):
            self.reader.read_carrier(bad)
        with self.assertRaises(ValueError):
            self.reader.read_carrier(word("01"))  # No whole-carrier Base.

    def test_code_and_cell_mutations_and_word_limits(self):
        carrier = base(self.tree, word("101"))
        self.assertEqual(self.reader.read_carrier(carrier, limits=reader.SReadoutLimits(max_word_bits=3)), "101")
        with self.assertRaises(reader.ResourceLimit):
            self.reader.read_carrier(carrier, limits=reader.SReadoutLimits(max_word_bits=2))
        other = reader.compile_carrier_reader(cts.Program(("0", "")))
        with self.assertRaises(ValueError):
            other.read_carrier(carrier)
        for bad in (S, app(S, S), base(self.tree, app(S, S))):
            with self.assertRaises(ValueError):
                self.reader.read_carrier(bad)


class ValidationTests(unittest.TestCase):
    def test_hostile_types_and_subclasses_are_rejected_without_methods(self):
        class Hostile:
            def __getattribute__(self, name):
                raise AssertionError("hostile attribute")
            def __eq__(self, other):
                raise AssertionError("hostile equality")
            def __hash__(self):
                raise AssertionError("hostile hash")
        class SubApp(App):
            pass
        class SubAtom(type(S)):
            pass
        for bad in (Hostile(), "S", None, [], {}, True, SubApp(S, S), SubAtom(), raw_app(Hostile(), S)):
            with self.subTest(kind=type(bad).__name__), self.assertRaises(ValueError):
                reader.find_ut19_event(bad)

    def test_cycles_missing_fields_and_post_match_invalid_siblings(self):
        cycle = raw_app()
        object.__setattr__(cycle, "right", cycle)
        mutual = raw_app()
        other = raw_app(mutual, S)
        object.__setattr__(mutual, "left", other)
        for bad in (cycle, mutual, object.__new__(App)):
            with self.assertRaises(ValueError):
                reader.find_ut19_event(bad)
        # Even a match on the left cannot hide an invalid right-hand subtree.
        program = ut19.compile_cts()
        tree = spec(program)
        shell = local(program, tree, S, S, (17, 1))
        with self.assertRaises(ValueError):
            reader.find_ut19_event(raw_app(shell, object()))
        with self.assertRaises(ValueError):
            reader.find_ut19_event(raw_app(shell, cycle))

    def test_cached_size_is_ignored_and_s_atoms_need_not_be_singleton(self):
        fresh_s = type(S)()
        bad_size = raw_app(fresh_s, fresh_s)
        object.__setattr__(bad_size, "_leaves", object())
        self.assertIsNone(reader.find_ut19_event(bad_size))
        deep = S
        for _ in range(2300):
            deep = raw_app(deep, deep)
        self.assertIsNone(reader.find_ut19_event(deep))

    def test_limits_are_plain_exact_revalidated_and_zero_is_real(self):
        for name in reader.SReadoutLimits.__dataclass_fields__:
            for bad in (-1, True, 1.0, "1", None):
                with self.assertRaises(ValueError):
                    reader.SReadoutLimits(**{name: bad})
        class SubLimits(reader.SReadoutLimits):
            pass
        with self.assertRaises(ValueError):
            SubLimits()
        for limits in (None, {}, object.__new__(SubLimits)):
            with self.assertRaises(ValueError):
                reader.find_ut19_event(S, limits=limits)
        forged = reader.SReadoutLimits()
        object.__setattr__(forged, "max_work", True)
        with self.assertRaises(ValueError):
            reader.find_ut19_event(S, limits=forged)
        for name in ("max_input_nodes", "max_work"):
            with self.assertRaises(reader.ResourceLimit):
                reader.find_ut19_event(S, limits=reader.SReadoutLimits(**{name: 0}))
        self.assertIsNone(reader.find_ut19_event(S, limits=reader.limits_for_input_nodes(1)))


if __name__ == "__main__":
    unittest.main()
