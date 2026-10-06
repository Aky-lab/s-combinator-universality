"""Finite replication checks for the pinned two-phase queue example.

The tuple constructors below transcribe the mathematical formulas in Sections
3, 4.2/4.3 and Appendix E of the pinned paper. The tuple reducer implements only
S x y z -> x z (y z). Neither calls production constructors or reduction code.
The recorded addresses are input DATA, not a controller implementation. Passing
these tests establishes this finite path; it cannot establish address selection
by a finite controller or the all-input universality theorem.
"""

from copy import deepcopy
from dataclasses import FrozenInstanceError
from functools import lru_cache
from itertools import product
import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from s_only import queue_fixture as queue
from s_only.reduction import contract_at
from s_only.terms import App, S, format_term, nodes, prefix
from s_only.traces import verify_path_certificate


FIXTURE = Path(__file__).resolve().parents[1] / "fixtures" / "queue_101_path.json"
ATOM = "S"


def app(*terms):
    out = terms[0]
    for child in terms[1:]:
        out = (out, child)
    return out


B = app(ATOM, ATOM)
C0 = app(ATOM, B, B)
PI = app(ATOM, B)
VALUES = (app(ATOM, C0), app(ATOM, app(ATOM, C0)))
LIVE = tuple(app(B, value) for value in VALUES)
HALT_TAG = app(B, ATOM)
HALT = app(B, HALT_TAG)
EMPTY = app(B, PI)
ONE = app(B, app(ATOM, app(ATOM, PI), LIVE[1]))
LEFT = app(B, app(ATOM, EMPTY, ONE))
RIGHT = app(B, app(ATOM, EMPTY, EMPTY))
ACTIONS = app(B, app(ATOM, LEFT, RIGHT))
ACT = app(ATOM, HALT, ACTIONS)


def word(bits):
    out = ATOM
    for bit in bits:
        out = app(LIVE[bit], out)
    return out


def environment(carrier):
    return app(ATOM, app(ATOM, ACT, app(ATOM, carrier)))


def generator(bits=(1, 0, 1)):
    return app(C0, C0, environment(word(bits)))


def numeral(index):
    out = C0
    for _ in range(index):
        out = app(B, out)
    return out


def terminal(horizon, right_index=None):
    left = numeral(horizon + 1)
    right = left if right_index is None else numeral(right_index)
    return app(left, right, environment(word((1, 0, 1))))


def base(carrier, audit=ATOM):
    # Base_Q(R) = (K ((E_Q (b E_seed)) K)) R. The retained R is opaque.
    continuation = app(ATOM, ATOM, ATOM)
    active = environment(carrier)
    dormant = environment(word((1, 0, 1)))
    alpha = app(active, app(B, dormant), continuation)
    return app(continuation, alpha, audit)


def route(phase, bit, action, audit=ATOM):
    # Chosen(A,Y) = S A Y; the unselected child is a dormant compiled call.
    leaf = app(ATOM, audit, action)
    leaves = (EMPTY, ONE) if phase == 0 else (EMPTY, EMPTY)
    if bit == 0:
        inner = app(ATOM, audit, app(leaf, app(leaves[1], audit)))
    else:
        inner = app(ATOM, audit, app(app(leaves[0], audit), leaf))
    if phase == 0:
        return app(ATOM, audit, app(inner, app(RIGHT, audit)))
    return app(ATOM, audit, app(app(LEFT, audit), inner))


def shell(accumulator, continuation, phase, bit=0, marked=False, audit=ATOM):
    # bit=0 appends nothing. (phase, bit)=(0,1) requires one outer live 1.
    action = app(PI, accumulator)
    if (phase, bit) == (0, 1):
        action = app(action, audit)
    halt = (app(ATOM, audit, app(HALT_TAG, audit)) if marked
            else app(HALT, audit))
    return app(halt, route(phase, bit, action, audit),
               app(ATOM, audit, audit), app(continuation, audit))


def checkpoint(bits, horizon, *, marked=None, phase=None, audit=ATOM):
    return shell(base(word(bits), audit), terminal(horizon),
                 (horizon - 1) % 2 if phase is None else phase,
                 marked=not bits if marked is None else marked, audit=audit)


def reference_contract(tree, path):
    """Rebuild one tuple occurrence with the literal S equation."""
    if path:
        if tree == ATOM or path[0] not in (0, 1):
            raise ValueError("invalid reference address")
        if path[0] == 0:
            return reference_contract(tree[0], path[1:]), tree[1]
        return tree[0], reference_contract(tree[1], path[1:])
    if (tree == ATOM or tree[0] == ATOM or tree[0][0] == ATOM
            or tree[0][0][0] != ATOM):
        raise ValueError("not a reference S redex")
    x, y, z = tree[0][0][1], tree[0][1], tree[1]
    return ((x, z), (y, z))


def reference_prefix(tree):
    output, stack = [], [tree]
    while stack:
        current = stack.pop()
        if current == ATOM:
            output.append(ATOM)
        else:
            output.append("A")
            stack.extend([current[1], current[0]])
    return "".join(output)


def production_tree(tree):
    if tree == ATOM:
        return S
    return App(production_tree(tree[0]), production_tree(tree[1]))


@lru_cache(maxsize=None)
def small_trees(leaves):
    if leaves == 1:
        return (ATOM,)
    return tuple((left, right)
                 for split in range(1, leaves)
                 for left in small_trees(split)
                 for right in small_trees(leaves - split))


class QueueConstructorTests(unittest.TestCase):
    def test_named_constructors_match_the_paper(self):
        expected = {
            "B": B, "C0": C0, "PI": PI, "HALT_TAG": HALT_TAG,
            "HALT": HALT, "EMPTY_ACTION": EMPTY, "ONE_ACTION": ONE,
            "LEFT_BRANCH": LEFT, "RIGHT_BRANCH": RIGHT,
            "ACTIONS": ACTIONS, "ACT": ACT,
        }
        for name, tree in expected.items():
            with self.subTest(name=name):
                self.assertEqual(prefix(getattr(queue, name)), reference_prefix(tree))
        self.assertEqual(tuple(prefix(term) for term in queue.VALUES),
                         tuple(reference_prefix(tree) for tree in VALUES))
        self.assertEqual(tuple(prefix(term) for term in queue.LIVE),
                         tuple(reference_prefix(tree) for tree in LIVE))

    def test_input_words_through_five_bits(self):
        for length in range(6):
            for bits in product((0, 1), repeat=length):
                with self.subTest(bits=bits):
                    self.assertEqual(prefix(queue.encode_word(bits)), reference_prefix(word(bits)))
                    encoded = queue.encode(bits)
                    self.assertEqual(prefix(encoded), reference_prefix(generator(bits)))
                    self.assertEqual(queue.decode(encoded), {
                        "horizon": 0, "phase": 0, "data": "".join(map(str, bits)),
                    })

    def test_initial_word_order_and_one_shot_iterators(self):
        self.assertEqual(queue.encode_word((1, 0)), App(queue.LIVE[0], App(queue.LIVE[1], S)))
        self.assertEqual(queue.encode(iter((1, 0, 1))), queue.encode())
        self.assertEqual(queue.encode([1, 0, 1]), queue.encode())
        self.assertEqual(nodes(queue.encode()), 171)

    def test_non_boolean_integer_bits_rejected(self):
        for bad in (-1, 2, True, False, 0.0, 1.0, "0", None):
            with self.subTest(bit=bad):
                with self.assertRaises(ValueError):
                    queue.encode((1, bad, 0))
        with self.assertRaises(ValueError):
            queue.apply()

    def test_source_reference_is_separate_and_totalizes_empty_word(self):
        words = ("101", "011", "11", "11", "1", "1", "", "", "")
        with patch.object(queue, "encode", side_effect=AssertionError("encoder consulted")), \
             patch.object(queue, "decode", side_effect=AssertionError("decoder consulted")):
            for horizon, expected in enumerate(words):
                self.assertEqual(queue.source_config(horizon), {
                    "horizon": horizon, "phase": horizon % 2, "data": expected,
                })
        for bad in (-1, True, False, 1.0, "2", None):
            with self.subTest(horizon=bad):
                with self.assertRaises(ValueError):
                    queue.source_config(bad)


class QueueRecordedPathTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads(FIXTURE.read_text())
        cls.actual = [queue.encode()]
        cls.reference = [generator()]
        for record in cls.fixture["steps"]:
            path = tuple(int(direction) for direction in record["path"])
            cls.actual.append(contract_at(cls.actual[-1], path))
            cls.reference.append(reference_contract(cls.reference[-1], path))

    def test_fixture_is_only_a_finite_prescribed_path(self):
        self.assertEqual(set(self.fixture), {"schema", "initial_prefix", "steps"})
        self.assertEqual(self.fixture["schema"], "s-only-path-v1")
        self.assertEqual(len(self.fixture["steps"]), 85)
        self.assertEqual(self.fixture["initial_prefix"], reference_prefix(generator()))
        for record in self.fixture["steps"]:
            self.assertEqual(set(record), {"path", "nodes", "after_sha256"})
            self.assertTrue(set(record["path"]) <= {"0", "1"})

    def test_all_85_native_rewrites_sizes_and_digests(self):
        for index, (actual, expected, record) in enumerate(zip(
                self.actual[1:], self.reference[1:], self.fixture["steps"]), 1):
            with self.subTest(contraction=index):
                serial = reference_prefix(expected)
                self.assertEqual(prefix(actual), serial)
                self.assertEqual(nodes(actual), len(serial))
                self.assertEqual(record["nodes"], len(serial))
                self.assertEqual(record["after_sha256"],
                                 hashlib.sha256(serial.encode("ascii")).hexdigest())
        self.assertEqual([nodes(self.actual[index]) for index in (0, 22, 85)],
                         [171, 17057, 339285])

    def test_acceptance_is_exactly_zero_22_85(self):
        accepted = {index: queue.decode(term) for index, term in enumerate(self.actual)
                    if queue.decode(term) is not None}
        self.assertEqual(accepted, {
            0: {"horizon": 0, "phase": 0, "data": "101"},
            22: {"horizon": 1, "phase": 1, "data": "011"},
            85: {"horizon": 2, "phase": 0, "data": "11"},
        })

    def test_decoder_does_not_consult_source_or_execution_history(self):
        # Replay samples in reverse and then out of order, with no source oracle,
        # constructor, reducer, file read, or selector available to the decoder.
        expected = {0: (0, "101"), 22: (1, "011"), 85: (2, "11")}
        with patch.object(queue, "source_config", side_effect=AssertionError("source consulted")), \
             patch.object(queue, "encode", side_effect=AssertionError("encoder consulted")), \
             patch("s_only.reduction.contract_at", side_effect=AssertionError("reducer consulted")), \
             patch("s_only.reduction.select_path", side_effect=AssertionError("selector consulted")), \
             patch("builtins.open", side_effect=AssertionError("file consulted")):
            for index in list(reversed(range(86))) + [22, 0, 85, 55, 22, 85]:
                with self.subTest(contraction=index):
                    result = queue.decode(self.actual[index])
                    if index not in expected:
                        self.assertIsNone(result)
                    else:
                        horizon, data = expected[index]
                        self.assertEqual(result, {"horizon": horizon, "phase": horizon % 2,
                                                  "data": data})

    def test_completed_horizon_two_job_at_55_is_not_a_checkpoint(self):
        # Both innermost responses already contain 11. Only the second one has
        # terminal C3 C3: step 55 still has Exit(2,1,E) = (S C2 (C3 C3)) E.
        for index, count in ((55, 2), (85, 3)):
            current = self.actual[index]
            for _ in range(count):
                local = queue._local(current)
                current = local.continuation
            self.assertEqual(queue._queue(local.accumulator), (1, 1))
            self.assertEqual(local.phase, 1)
            self.assertFalse(local.marked)
            expected = (app(ATOM, numeral(2), app(numeral(3), numeral(3)),
                            environment(word((1, 0, 1)))) if index == 55 else terminal(2))
            self.assertEqual(prefix(current), reference_prefix(expected))
        self.assertIsNone(queue.decode(self.actual[55]))
        self.assertEqual(queue.decode(self.actual[85])["data"], "11")

    def test_old_samples_remain_immutable(self):
        # The first contraction duplicates its C0 argument, not the surrounding
        # freshly constructed application nodes.
        first = self.actual[1]
        self.assertIs(first.left.left.right, first.left.right.right)
        # A consumed cell likewise has two occurrences of its predecessor.
        # Rewriting the canonical copy must leave the audit occurrence alone.
        predecessor = queue.encode_word((0, 1))
        consumed = contract_at(App(queue.LIVE[1], predecessor), ())
        self.assertIs(consumed.left.right, consumed.right.right)
        rewritten = contract_at(consumed, (0, 1))
        self.assertIs(rewritten.right.right, predecessor)
        self.assertNotEqual(prefix(rewritten.left.right), prefix(predecessor))
        self.assertEqual(queue._word(consumed), (0, 1))
        self.assertEqual(queue._word(rewritten), (0,))
        for index in (0, 1, 22, 55, 85):
            self.assertEqual(prefix(self.actual[index]), reference_prefix(self.reference[index]))
        with self.assertRaises(FrozenInstanceError):
            first.left = S

    def test_prefix_verifier_replays_all_85_without_object_kernel(self):
        expected = format_term(self.actual[-1])
        with patch("s_only.reduction.contract_at", side_effect=AssertionError("object reducer used")), \
             patch("s_only.reduction.select_path", side_effect=AssertionError("selector used")), \
             patch("s_only.terms.prefix", side_effect=AssertionError("object serializer used")):
            self.assertEqual(verify_path_certificate(self.fixture), expected)


class QueueStructuralGrammarTests(unittest.TestCase):
    def test_every_closed_tree_through_nine_leaves_is_rejected(self):
        checked = 0
        for size in range(1, 10):
            for tree in small_trees(size):
                self.assertIsNone(queue.decode(production_tree(tree)))
                checked += 1
        self.assertEqual(checked, 2056)

    def test_synthetic_checkpoints_read_literal_data_not_expected_source(self):
        # These grammar-valid trees are deliberately not recorded path states.
        # Acceptance off the path does not certify source reachability.
        for horizon in (1, 2, 3, 7, 18, 42):
            for bits in ((), (0,), (0, 1, 0, 0), (1, 1, 0)):
                with self.subTest(horizon=horizon, bits=bits):
                    term = production_tree(checkpoint(bits, horizon))
                    with patch.object(queue, "source_config", side_effect=AssertionError("oracle used")):
                        self.assertEqual(queue.decode(term), {
                            "horizon": horizon, "phase": horizon % 2,
                            "data": "".join(map(str, bits)),
                        })

    def test_audit_fields_are_opaque_and_can_be_unrelated(self):
        for audit in (ATOM, app(ATOM, ATOM), app(ATOM, ATOM, ATOM, ATOM), generator((0,))):
            term = production_tree(checkpoint((0, 1), 3, audit=audit))
            self.assertEqual(queue.decode(term), {"horizon": 3, "phase": 1, "data": "01"})

    def test_tombstone_uses_canonical_predecessor_not_audit_copy(self):
        predecessor = word((0, 1))
        for audit in (ATOM, word((1, 1, 1, 1)), generator((0,))):
            consumed = app(ATOM, predecessor, app(VALUES[1], audit))
            accumulator = base(app(LIVE[0], consumed), audit)
            term = production_tree(shell(accumulator, terminal(2), 1))
            self.assertEqual(queue.decode(term), {"horizon": 2, "phase": 0, "data": "010"})

    def test_generator_rejects_consumed_or_malformed_seed_word(self):
        consumed = app(ATOM, ATOM, app(VALUES[1], ATOM))
        for carrier in (consumed, app(ATOM, ATOM), app(LIVE[0], consumed)):
            term = production_tree(app(C0, C0, environment(carrier)))
            self.assertIsNone(queue.decode(term))

    def test_positive_checkpoint_requires_nonempty_shell_chain(self):
        for horizon in (0, 1, 2, 7):
            self.assertIsNone(queue.decode(production_tree(terminal(horizon))))

    def test_status_must_match_empty_queue_and_phase_must_match_horizon(self):
        for bits, marked in (((), False), ((0,), True)):
            self.assertIsNone(queue.decode(production_tree(checkpoint(bits, 2, marked=marked))))
        self.assertIsNone(queue.decode(production_tree(checkpoint((1,), 2, phase=0))))

    def test_terminal_rejects_small_or_unequal_numerals(self):
        for ending in (terminal(0), terminal(2, right_index=2),
                       app(C0, numeral(3), environment(word((1, 0, 1))))):
            term = shell(base(word((0,))), ending, phase=1)
            self.assertIsNone(queue.decode(production_tree(term)))

    def test_innermost_completed_local_controls_result(self):
        inner = checkpoint((0, 1), 2)
        # A historical outer response has different data, phase and status.
        outer = shell(base(ATOM), inner, phase=0, marked=True)
        self.assertEqual(queue.decode(production_tree(outer)),
                         {"horizon": 2, "phase": 0, "data": "01"})

    def test_missing_shell_fields_and_wrong_environment_are_rejected(self):
        valid = checkpoint((0, 1), 2)
        malformed = [
            valid[0], (valid[0], ATOM), (ATOM, valid[1]),
            app(C0, C0, app(ATOM, app(ATOM, ATOM, app(ATOM, word((1,)))))),
            app(C0, C0, app(ATOM, app(ATOM, ACT, ATOM))),
        ]
        for tree in malformed:
            with self.subTest(prefix=reference_prefix(tree)):
                self.assertIsNone(queue.decode(production_tree(tree)))

    def test_wrong_dormant_dispatcher_branch_is_rejected(self):
        # Corrupt only the compiled part of the dormant root right branch.
        valid = production_tree(checkpoint((0, 1), 1))
        earlier = valid.left.left
        completed_route = earlier.right
        broken_branch = App(completed_route.right.left, App(S, S))
        broken_route = App(completed_route.left, broken_branch)
        broken = App(App(App(earlier.left, broken_route), valid.left.right), valid.right)
        self.assertIsNone(queue.decode(broken))

    def test_append_one_requires_the_literal_appended_bit(self):
        for bit in (0, 1):
            accumulated = app(LIVE[bit], base(word((0,))))
            term = production_tree(shell(accumulated, terminal(1), 0, bit=1))
            if bit == 1:
                self.assertEqual(queue.decode(term), {"horizon": 1, "phase": 1, "data": "01"})
            else:
                self.assertIsNone(queue.decode(term))


class PrescribedPathCertificateTests(unittest.TestCase):
    def setUp(self):
        # A single root contraction from S S S S to (S S)(S S).
        serial = "AASSASS"
        self.valid = {
            "schema": "s-only-path-v1", "initial_prefix": "AAASSSS",
            "steps": [{"path": "", "nodes": 7,
                       "after_sha256": hashlib.sha256(serial.encode("ascii")).hexdigest()}],
        }

    def test_native_path_makes_no_strategy_or_terminal_claim(self):
        self.assertEqual(verify_path_certificate(self.valid), "((S S) (S S))")
        # A zero-step certificate is valid even if its initial term is reducible.
        self.valid["steps"] = []
        self.assertEqual(verify_path_certificate(self.valid), "(((S S) S) S)")

    def test_bad_schema_and_record_shape_rejected(self):
        for key in self.valid:
            changed = deepcopy(self.valid)
            del changed[key]
            with self.assertRaises(ValueError):
                verify_path_certificate(changed)
        for key, value in (("schema", "s-only-trace-v1"), ("steps", {}), ("extra", 1)):
            changed = deepcopy(self.valid)
            changed[key] = value
            with self.assertRaises(ValueError):
                verify_path_certificate(changed)
        for key in self.valid["steps"][0]:
            changed = deepcopy(self.valid)
            del changed["steps"][0][key]
            with self.assertRaises(ValueError):
                verify_path_certificate(changed)
        changed = deepcopy(self.valid)
        changed["steps"][0]["extra"] = 1
        with self.assertRaises(ValueError):
            verify_path_certificate(changed)

    def test_tampered_path_size_digest_and_initial_tree_rejected(self):
        for key, value in (("path", "0"), ("path", "L"), ("path", 0),
                           ("path", "111"), ("nodes", True), ("nodes", 9),
                           ("after_sha256", "0" * 64)):
            with self.subTest(field=key, value=value):
                changed = deepcopy(self.valid)
                changed["steps"][0][key] = value
                with self.assertRaises(ValueError):
                    verify_path_certificate(changed)
        for serial in ("", "A", "AS", "SS", "K", None):
            changed = deepcopy(self.valid)
            changed["initial_prefix"] = serial
            with self.assertRaises(ValueError):
                verify_path_certificate(changed)


if __name__ == "__main__":
    unittest.main()
