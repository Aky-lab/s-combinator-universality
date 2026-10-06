"""Independent syntax fixtures and finite native samples for the CTS reader.

Synthetic checkpoint acceptance establishes grammar behavior, not native
reachability.  The source evaluator occurs only in explicit comparison tests.
"""
from contextlib import ExitStack
from itertools import product
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from s_only.cts import Configuration, Program, step
from s_only import cts_reader, encoding, queue_fixture
from s_only.reduction import contract_at
from s_only.terms import App, S, prefix


ROOT = Path(__file__).resolve().parents[1]


def app(*terms):
    out = terms[0]
    for child in terms[1:]:
        out = App(out, child)
    return out


# Independently transcribed mathematical constructors, not reader internals.
B = app(S, S)
C0 = app(S, B, B)
PI = app(S, B)
VALUES = (app(S, C0), app(S, app(S, C0)))
LIVE = tuple(app(B, value) for value in VALUES)
HALT_TAG = app(B, S)
HALT = app(B, HALT_TAG)


def word(bits):
    result = S
    for bit in bits:
        result = app(LIVE[int(bit)], result)
    return result


def tombstone(bit, predecessor, audit=S):
    return app(S, predecessor, app(VALUES[int(bit)], audit))


def appender(bits):
    result = PI
    for bit in reversed(bits):
        result = app(S, app(S, result), LIVE[int(bit)])
    return result


def specification(program):
    forest = [(app(B, appender(bits if bit else "")), None, None, (phase, bit))
              for phase, bits in enumerate(program.appendants) for bit in (0, 1)]
    while len(forest) > 1:
        new = []
        for offset in range(0, len(forest), 2):
            if offset + 1 == len(forest):
                new.append(forest[offset])
            else:
                left, right = forest[offset:offset + 2]
                new.append((app(B, app(S, left[0], right[0])), left, right, None))
        forest = new
    return forest[0]


def environment(spec, payload):
    return app(S, app(S, app(S, HALT, spec[0]), app(S, payload)))


def numeral(index):
    result = C0
    for _ in range(index):
        result = app(B, result)
    return result


def terminal(spec, horizon, *, right_index=None, payload=S):
    right_index = horizon + 1 if right_index is None else right_index
    return app(numeral(horizon + 1), numeral(right_index), environment(spec, payload))


def base(spec, queue, *, outer=S, inner=S, seed=S, beta=S):
    alpha = app(environment(spec, queue), app(B, environment(spec, seed)), inner)
    return app(outer, alpha, beta)


def selected_route(spec, target, response, audit=S, *, independent_audits=None):
    """Build a completed route with an iterative independent tree traversal."""
    def next_audit():
        return audit if independent_audits is None else next(independent_audits)

    stack = [(spec, ())]
    while stack:
        current, path = stack.pop()
        _code, left, right, label = current
        if label == target:
            result = app(S, next_audit(), response)
            for parent, direction in reversed(path):
                if direction == 0:
                    result = app(S, next_audit(), app(result, app(parent[2][0], next_audit())))
                else:
                    result = app(S, next_audit(), app(app(parent[1][0], next_audit()), result))
            return result
        if label is None:
            stack.extend(((right, path + ((current, 1),)),
                          (left, path + ((current, 0),))))
    raise ValueError("missing label")


def shell(program, spec, accumulator, continuation, phase, *, bit=0,
          marked=False, audit=S, histories=None, halt=None, seed=S,
          seed_audit=None, continuation_audit=None, route=None):
    if histories is None:
        histories = [audit] * (len(program.appendants[phase]) if bit else 0)
    action = app(PI, accumulator, *histories)
    if halt is None:
        halt = (app(S, audit, app(HALT_TAG, audit)) if marked else app(HALT, audit))
    if route is None:
        route = selected_route(spec, (phase, bit), action, audit)
    return app(halt, route, app(S, seed, audit if seed_audit is None else seed_audit),
               app(continuation, audit if continuation_audit is None else continuation_audit))


def checkpoint(program, bits, horizon, *, phase=None, marked=None, **kwargs):
    spec = specification(program)
    return shell(program, spec, base(spec, word(bits)), terminal(spec, horizon),
                 (horizon - 1) % len(program.appendants) if phase is None else phase,
                 marked=not bits if marked is None else marked, **kwargs)


class InitialReaderTests(unittest.TestCase):
    def test_all_words_through_five_bits_and_varied_periods(self):
        programs = [Program(("",)), Program(("1", "")), Program(("0", "10")),
                    Program(("10", "1")), Program(("", "", "")),
                    Program(("01", "10", "", "1", "00"))]
        for program in programs:
            reader = cts_reader.compile_reader(program)
            for length in range(6):
                for bits in product("01", repeat=length):
                    data = "".join(bits)
                    with self.subTest(program=program, data=data):
                        self.assertEqual(reader.decode(encoding.encode(program, data)),
                                         {"horizon": 0, "phase": 0, "data": data})
            self.assertEqual(prefix(reader.actions), prefix(specification(program)[0]))

    def test_static_program_identity_and_convenience_api(self):
        program = Program(("0", "10", ""))
        term = encoding.encode(program, "101")
        self.assertEqual(cts_reader.decode(program, term),
                         {"horizon": 0, "phase": 0, "data": "101"})
        self.assertIsNone(cts_reader.decode(Program(("1", "10", "")), term))
        for bad in (None, (), ("",), [""], "0"):
            with self.assertRaises(TypeError):
                cts_reader.compile_reader(bad)
        with self.assertRaises(ValueError):
            Program(())

    def test_literal_initial_word_excludes_tombstones(self):
        program = Program(("10", ""))
        spec = specification(program)
        for payload in (tombstone(1, S), app(LIVE[0], tombstone(1, S)), app(S, S)):
            self.assertIsNone(cts_reader.decode(program, app(C0, C0, environment(spec, payload))))

    def test_deep_initial_word_and_code_avoid_recursive_equality(self):
        program = Program(("01" * 900, "", "1"))
        data = "10" * 1600
        reader, term = cts_reader.compile_reader(program), encoding.encode(program, data)
        with patch.object(App, "__eq__", side_effect=AssertionError("recursive equality")), \
             patch.object(App, "__hash__", side_effect=AssertionError("term hashing")):
            self.assertEqual(reader.decode(term), {"horizon": 0, "phase": 0, "data": data})


class RecordedPathReaderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = Program(("1", ""))
        cls.reader = cts_reader.compile_reader(cls.program)
        fixture = json.loads((ROOT / "fixtures/queue_101_path.json").read_text())
        cls.samples = [encoding.encode(cls.program, "101")]
        for record in fixture["steps"]:
            cls.samples.append(contract_at(cls.samples[-1], tuple(map(int, record["path"]))))

    def test_all_86_acceptance_decisions_match_fixed_reader(self):
        self.assertEqual(len(self.samples), 86)
        accepted = {}
        for index, term in enumerate(self.samples):
            found = self.reader.decode(term)
            self.assertEqual(found, queue_fixture.decode(term), index)
            if found is not None:
                accepted[index] = found
        self.assertEqual(accepted, {
            0: {"horizon": 0, "phase": 0, "data": "101"},
            22: {"horizon": 1, "phase": 1, "data": "011"},
            85: {"horizon": 2, "phase": 0, "data": "11"},
        })

    def test_decoder_isolated_from_source_history_files_hashes_and_reduction(self):
        forbidden = ["s_only.cts.step", "s_only.cts.Machine.tick",
                     "s_only.queue_fixture.source_config", "s_only.queue_fixture.decode",
                     "s_only.encoding.compile_program", "s_only.encoding.encode",
                     "s_only.encoding.encode_word", "s_only.reduction.contract_at",
                     "s_only.reduction.select_path", "builtins.open", "io.open",
                     "pathlib.Path.read_text", "pathlib.Path.read_bytes",
                     "hashlib.sha256", "s_only.terms.prefix"]
        expected = {0: (0, "101"), 22: (1, "011"), 85: (2, "11")}
        with ExitStack() as stack:
            for name in forbidden:
                stack.enter_context(patch(name, side_effect=AssertionError(name)))
            stack.enter_context(patch.object(App, "__eq__", side_effect=AssertionError("equality")))
            stack.enter_context(patch.object(App, "__hash__", side_effect=AssertionError("hash")))
            for index in [*reversed(range(86)), 55, 85, 0, 22, 22]:
                found = self.reader.decode(self.samples[index])
                if index in expected:
                    horizon, data = expected[index]
                    self.assertEqual(found, {"horizon": horizon, "phase": horizon % 2, "data": data})
                else:
                    self.assertIsNone(found)


class SyntheticReaderTests(unittest.TestCase):
    def test_arbitrary_data_horizons_and_non_power_of_two_periods(self):
        for period in (1, 2, 3, 5, 7, 8, 9):
            program = Program(tuple(("01", "", "110")[i % 3] for i in range(period)))
            reader = cts_reader.compile_reader(program)
            for horizon in (1, 2, 3, 7, 18, 42):
                for data in ("", "0", "10110"):
                    self.assertEqual(reader.decode(checkpoint(program, data, horizon)),
                                     {"horizon": horizon, "phase": horizon % period, "data": data})

    def test_all_labels_and_variable_depth_dispatcher_routes(self):
        program = Program(("010", "1", "", "10101", "00"))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        depths = {}
        pending = [(spec, 0)]
        while pending:
            node, depth = pending.pop()
            if node[3] is None:
                pending.extend(((node[1], depth + 1), (node[2], depth + 1)))
            else:
                depths[node[3]] = depth
        self.assertEqual([depths[(p, b)] for p in range(5) for b in (0, 1)], [4] * 8 + [2] * 2)
        for phase in range(5):
            for bit in (0, 1):
                suffix = program.appendants[phase] if bit else ""
                acc = base(spec, word("10"))
                for emitted in suffix:
                    acc = app(LIVE[int(emitted)], acc)
                term = shell(program, spec, acc, terminal(spec, phase + 1), phase, bit=bit)
                self.assertEqual(reader.decode(term),
                                 {"horizon": phase + 1, "phase": (phase + 1) % 5,
                                  "data": "10" + suffix})

    def test_action_arity_is_checked_but_accumulator_labels_are_permissive(self):
        program = Program(("010",))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        # Pinned ActionParser validates PI and three retained histories. It
        # deliberately does not assert how this accumulator was constructed.
        for emitted in ("", "010", "001", "110", "01", "0100"):
            acc = base(spec, word("11"))
            for bit in emitted:
                acc = app(LIVE[int(bit)], acc)
            term = shell(program, spec, acc, terminal(spec, 1), 0, bit=1)
            self.assertEqual(reader.decode(term)["data"], "11" + emitted)
        acc = base(spec, word("11"))
        for bit in "111":
            acc = tombstone(bit, acc, word("111"))
        self.assertEqual(reader.decode(shell(program, spec, acc, terminal(spec, 1), 0, bit=1))["data"], "11")
        for count in (0, 1, 2, 4, 5):
            self.assertIsNone(reader.decode(shell(program, spec, acc, terminal(spec, 1),
                                                  0, bit=1, histories=[S] * count)))

    def test_permissive_action_grammar_differs_from_fixed_reader_off_path(self):
        program = Program(("1", ""))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        # Phase 0 / bit 1 normally appends 1. This off-path synthetic response
        # instead exposes a 0, while retaining the correct one-history spine.
        acc = app(LIVE[0], base(spec, word("1")))
        term = shell(program, spec, acc, terminal(spec, 1), 0, bit=1)
        self.assertEqual(reader.decode(term), {"horizon": 1, "phase": 1, "data": "10"})
        self.assertIsNone(queue_fixture.decode(term))

    def test_independent_opaque_audits_and_matching_base_continuations(self):
        program = Program(("10", "1", ""))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        deep_audit = S
        for _ in range(2500):
            deep_audit = app(deep_audit, S)
        deep_copy = S
        for _ in range(2500):
            deep_copy = app(deep_copy, S)
        audits = [S, app(S, S), word("111"), deep_audit, encoding.encode(program, "010")]
        for offset, audit in enumerate(audits):
            # The continuation itself repeats in the Base production; it is
            # not one of the independently quantified audit arguments.
            acc = base(spec, word("01"), outer=audit,
                       inner=deep_copy if audit is deep_audit else audit,
                       seed=audits[(offset + 2) % 5], beta=audits[(offset + 3) % 5])
            term = shell(program, spec, acc, terminal(spec, 3, payload=deep_audit), 2,
                         audit=audit, seed=deep_audit, seed_audit=audits[(offset + 2) % 5],
                         continuation_audit=audits[(offset + 4) % 5])
            with patch.object(App, "__eq__", side_effect=AssertionError("opaque equality")):
                self.assertEqual(reader.decode(term), {"horizon": 3, "phase": 0, "data": "01"})

    def test_independent_marked_fields_and_history_arguments(self):
        program = Program(("01", ""))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        marked = app(S, word("101"), app(HALT_TAG, app(S, S)))
        empty = shell(program, spec, base(spec, S), terminal(spec, 2), 1,
                      halt=marked, seed=word("1"), continuation_audit=word("01"))
        self.assertEqual(reader.decode(empty), {"horizon": 2, "phase": 0, "data": ""})
        acc = app(LIVE[1], app(LIVE[0], base(spec, word("1"))))
        term = shell(program, spec, acc, terminal(spec, 1), 0, bit=1,
                     histories=[word("111"), S], audit=word("000"))
        self.assertEqual(reader.decode(term)["data"], "101")

    def test_each_route_audit_is_independent_of_every_other_audit(self):
        program = Program(("0", "10", "", "1", "01"))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        audits = [S]
        for _ in range(20):
            audits.append(app(S, audits[-1]))
        for phase in range(5):
            acc = base(spec, word("01"))
            response = app(PI, acc)
            route = selected_route(spec, (phase, 0), response,
                                   independent_audits=iter(audits))
            term = shell(program, spec, acc, terminal(spec, phase + 1), phase,
                         route=route, audit=word("111"), seed=word("000"))
            self.assertEqual(reader.decode(term),
                             {"horizon": phase + 1, "phase": (phase + 1) % 5, "data": "01"})

    def test_failed_alternatives_never_enter_nested_local_or_marked_audits(self):
        program = Program(("01", ""))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        huge, opaque = S, set()
        for _ in range(1200):
            huge = App(huge, huge)

        def audit():
            result = App(huge, S)
            opaque.add(id(result))
            return result

        acc = base(spec, tombstone(1, S, audit()), seed=audit(), beta=audit())
        # Carrier classification attempts Base before Local. A failed Base
        # match must not enter this nested Local's seed or continuation audits.
        inner = shell(program, spec, acc, S, 0, bit=1,
                      histories=[audit(), audit()], marked=True, seed=audit(),
                      audit=audit(), seed_audit=audit(), continuation_audit=audit(),
                      halt=app(S, audit(), app(HALT_TAG, audit())))
        term = shell(program, spec, inner, terminal(spec, 2, payload=audit()), 1,
                     marked=True, seed=audit(), audit=audit(), seed_audit=audit(),
                     continuation_audit=audit(),
                     halt=app(S, audit(), app(HALT_TAG, audit())))
        get = App.__getattribute__

        def guarded(item, name):
            if id(item) in opaque and name in ("left", "right"):
                raise AssertionError("opaque audit was traversed")
            return get(item, name)

        with patch.object(App, "__getattribute__", guarded):
            self.assertEqual(reader.decode(term), {"horizon": 2, "phase": 0, "data": ""})

    def test_canonical_predecessor_and_nested_local_accumulator(self):
        program = Program(("0", "1", ""))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        payload = app(LIVE[0], tombstone(1, word("01"), word("111111")))
        inner = shell(program, spec, base(spec, payload), S, 0)
        outer = shell(program, spec, app(LIVE[1], inner), terminal(spec, 3), 2)
        self.assertEqual(reader.decode(outer), {"horizon": 3, "phase": 0, "data": "0101"})

    def test_last_local_controls_phase_data_and_status_not_shell_count(self):
        program = Program(("", "1", "0"))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        term = checkpoint(program, "01", 7)
        for _ in range(12):
            term = shell(program, spec, base(spec, S), term, 2, marked=True)
        self.assertEqual(reader.decode(term), {"horizon": 7, "phase": 1, "data": "01"})

    def test_deep_numerals_local_chains_and_carriers_are_iterative(self):
        program = Program(("", "", ""))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        horizon = 2400
        acc = base(spec, word("1"))
        for _ in range(2200):
            acc = tombstone(0, app(LIVE[0], acc), S)
        term = shell(program, spec, acc, terminal(spec, horizon), (horizon - 1) % 3)
        for _ in range(2100):
            term = shell(program, spec, base(spec, S), term, 0, marked=True)
        with patch.object(App, "__eq__", side_effect=AssertionError("recursive equality")):
            self.assertEqual(reader.decode(term), {"horizon": horizon, "phase": 0, "data": "1" + "0" * 2200})

    def test_empty_word_totalization_is_explicitly_distinct_from_ordinary_stop(self):
        program = Program(("", "", ""))
        reader = cts_reader.compile_reader(program)
        with self.assertRaises(StopIteration):
            step(program, Configuration("", 0))
        # These are syntax fixtures for the paper's totalized empty trajectory,
        # not evidence of native reachability or steps by the stopping machine.
        for horizon in range(1, 8):
            self.assertEqual(reader.decode(checkpoint(program, "", horizon)),
                             {"horizon": horizon, "phase": horizon % 3, "data": ""})

    def test_deep_action_history_spine_is_iterative(self):
        program = Program(("01" * 1200,))
        spec, reader = specification(program), cts_reader.compile_reader(program)
        acc = base(spec, word("10"))
        term = shell(program, spec, acc, terminal(spec, 1), 0, bit=1)
        with patch.object(App, "__eq__", side_effect=AssertionError("recursive equality")):
            self.assertEqual(reader.decode(term), {"horizon": 1, "phase": 0, "data": "10"})


class RejectionReaderTests(unittest.TestCase):
    def setUp(self):
        self.program = Program(("0", "10", ""))
        self.spec = specification(self.program)
        self.reader = cts_reader.compile_reader(self.program)

    def test_no_completed_shell_or_wrong_terminal(self):
        for horizon in (0, 1, 2, 7):
            self.assertIsNone(self.reader.decode(terminal(self.spec, horizon)))
        acc = base(self.spec, word("1"))
        for ending in (terminal(self.spec, 0), terminal(self.spec, 2, right_index=2),
                       app(numeral(1), numeral(3), environment(self.spec, S)),
                       app(S, numeral(2), app(numeral(3), numeral(3)), environment(self.spec, S))):
            self.assertIsNone(self.reader.decode(shell(self.program, self.spec, acc, ending, 1)))

    def test_unequal_base_continuations_reject(self):
        acc = base(self.spec, word("01"), outer=S, inner=app(S, S))
        term = shell(self.program, self.spec, acc, terminal(self.spec, 1), 0)
        self.assertIsNone(self.reader.decode(term))

    def test_wrong_phase_or_empty_status(self):
        for bits, marked in (("", False), ("0", True)):
            self.assertIsNone(self.reader.decode(checkpoint(self.program, bits, 2, marked=marked)))
        for phase in (0, 2):
            self.assertIsNone(self.reader.decode(checkpoint(self.program, "1", 2, phase=phase)))

    def test_invalid_roots_and_small_finite_trees_reject_safely(self):
        for value in (None, "S", 3, True, [], {}):
            self.assertIsNone(self.reader.decode(value))
        trees = {1: [S]}
        checked = 0
        for size in range(1, 10):
            if size > 1:
                trees[size] = [App(left, right) for n in range(1, size)
                               for left in trees[n] for right in trees[size - n]]
            for term in trees[size]:
                self.assertIsNone(self.reader.decode(term))
                checked += 1
        self.assertEqual(checked, 2056)

    def test_wrong_public_fields_reject(self):
        valid = checkpoint(self.program, "01", 1)
        malformed = [valid.left, App(valid.left, S), App(S, valid.right),
                     app(C0, C0, app(S, app(S, S, app(S, word("1"))))),
                     app(C0, C0, app(S, app(S, self.reader.act, S)))]
        for term in malformed:
            self.assertIsNone(self.reader.decode(term))
        bad_payload = base(self.spec, app(S, S))
        self.assertIsNone(self.reader.decode(shell(self.program, self.spec, bad_payload,
                                                  terminal(self.spec, 1), 0)))

    def test_dormant_code_and_route_arity_are_exact(self):
        valid = checkpoint(self.program, "01", 1)
        earlier = valid.left.left
        route = earlier.right
        # Target phase zero selects left at the root. Corrupt dormant code only.
        wrong = App(route.right.left, App(S, route.right.right.right))
        route = App(route.left, wrong)
        term = App(App(App(earlier.left, route), valid.left.right), valid.right)
        self.assertIsNone(self.reader.decode(term))
        for wrong_route in (S, app(S, S), app(S, S, S, S), app(S, S, app(S, S))):
            term = shell(self.program, self.spec, base(self.spec, word("01")),
                         terminal(self.spec, 1), 0, route=wrong_route)
            self.assertIsNone(self.reader.decode(term))


if __name__ == "__main__":
    unittest.main()
