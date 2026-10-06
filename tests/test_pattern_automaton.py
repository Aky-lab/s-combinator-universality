"""Independent small syntax oracles and adversarial resource/type checks."""
from contextlib import ExitStack
from dataclasses import FrozenInstanceError, replace
from functools import lru_cache
import random
import unittest
from unittest.mock import patch

from s_only.pattern_automaton import (
    Descriptor, PatternAutomaton, ResourceLimit, compile_pattern, evaluate,
)
from s_only.probes import HOLE, LITERAL_S
from s_only.terms import App, S


@lru_cache(None)
def patterns(leaves):
    if leaves == 1:
        return (HOLE, LITERAL_S)
    return tuple((left, right)
                 for split in range(1, leaves)
                 for left in patterns(split) for right in patterns(leaves - split))


@lru_cache(None)
def trees(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right)
                 for split in range(1, leaves)
                 for left in trees(split) for right in trees(leaves - split))


def direct_match(pattern, tree):
    # Deliberately recursive, with no automaton code. Used only on small trees.
    if pattern == HOLE:
        return True
    if pattern == LITERAL_S:
        return tree is S
    return (type(tree) is App and direct_match(pattern[0], tree.left)
            and direct_match(pattern[1], tree.right))


def direct_occurs(pattern, tree):
    return (direct_match(pattern, tree) or
            (type(tree) is App and (direct_occurs(pattern, tree.left)
                                   or direct_occurs(pattern, tree.right))))


def decoded_patterns(automaton):
    out = []
    for node in automaton.nodes:
        out.append((out[node.left], out[node.right]) if node.kind == "pair" else node.kind)
    return out


class PoisonStr(str):
    def __eq__(self, other):
        raise AssertionError("custom equality must not run")

    def __hash__(self):
        raise AssertionError("custom hash must not run")


class PoisonInt(int):
    def __lt__(self, other):
        raise AssertionError("custom order must not run")

    def __eq__(self, other):
        raise AssertionError("custom equality must not run")

    def __hash__(self):
        raise AssertionError("custom hash must not run")


class PoisonTuple(tuple):
    def __len__(self):
        raise AssertionError("custom length must not run")

    def __iter__(self):
        raise AssertionError("custom iteration must not run")


class PoisonObject:
    def __eq__(self, other):
        raise AssertionError("custom equality must not run")

    def __hash__(self):
        raise AssertionError("custom hash must not run")


class PoisonMeta(type):
    def __eq__(self, other):
        raise AssertionError("metaclass equality must not run")


class PoisonMetaObject(metaclass=PoisonMeta):
    pass


class PatternAutomatonTests(unittest.TestCase):
    def test_all_small_patterns_trees_and_every_match_bit(self):
        examples = tuple(tree for size in range(1, 7) for tree in trees(size))
        checked = 0
        for size in range(1, 6):
            for pattern in patterns(size):
                automaton = compile_pattern(pattern)
                subpatterns = decoded_patterns(automaton)
                self.assertEqual(subpatterns[-1], pattern)
                self.assertEqual(len(set(subpatterns)), len(subpatterns))
                for tree in examples:
                    state = evaluate(automaton, tree)
                    for index, subpattern in enumerate(subpatterns):
                        self.assertEqual(bool((state >> index) & 1),
                                         direct_match(subpattern, tree))
                    self.assertEqual(automaton.matches_root(state), direct_match(pattern, tree))
                    self.assertEqual(automaton.accepts(state), direct_occurs(pattern, tree))
                    checked += 1
        self.assertEqual(checked, 550 * 65)

    def test_holes_are_independent_even_when_shared(self):
        automaton = compile_pattern((HOLE, HOLE))
        tree = App(S, App(S, S))
        self.assertTrue(automaton.matches_root(evaluate(automaton, tree)))
        shared = (HOLE, HOLE)
        automaton = compile_pattern((shared, shared))
        self.assertTrue(automaton.matches_root(evaluate(
            automaton, App(App(S, S), App(App(S, S), S)))))

    def test_hole_atom_positive_negative_and_descendant_only(self):
        for pattern in (HOLE, LITERAL_S):
            automaton = compile_pattern(pattern)
            self.assertTrue(automaton.accepts(evaluate(automaton, S)))
            self.assertTrue(automaton.accepts(evaluate(automaton, App(S, S))))
        atom = compile_pattern(LITERAL_S)
        self.assertFalse(atom.matches_root(evaluate(atom, App(S, S))))
        automaton = compile_pattern((LITERAL_S, (LITERAL_S, LITERAL_S)))
        positive = App(S, App(S, S))
        outer = App(positive, S)
        self.assertTrue(automaton.matches_root(evaluate(automaton, positive)))
        self.assertTrue(automaton.accepts(evaluate(automaton, outer)))
        self.assertFalse(automaton.matches_root(evaluate(automaton, outer)))
        self.assertFalse(automaton.accepts(evaluate(automaton, App(App(S, S), S))))

    def test_equal_distinct_pattern_objects_are_canonically_interned(self):
        one, two = tuple([LITERAL_S, HOLE]), tuple([LITERAL_S, HOLE])
        self.assertIsNot(one, two)
        distinct = compile_pattern((one, two), max_descriptors=4, max_pattern_nodes=5)
        shared = compile_pattern((one, one), max_descriptors=4, max_pattern_nodes=4)
        self.assertEqual(distinct, shared)
        self.assertEqual(len(distinct.nodes), 4)
        self.assertEqual(distinct.nodes[-1].left, distinct.nodes[-1].right)

    def test_deep_shared_and_unshared_dags_need_no_recursion_or_term_hash(self):
        depth = 1200
        pattern, term = LITERAL_S, S
        for _ in range(depth):
            pattern, term = (pattern, pattern), App(term, term)
        with patch.object(App, "__hash__", side_effect=AssertionError("term hash")), \
             patch.object(App, "__eq__", side_effect=AssertionError("term equality")):
            automaton = compile_pattern(pattern, max_descriptors=depth + 1,
                                        max_pattern_nodes=depth + 1)
            state = evaluate(automaton, term, max_term_nodes=depth + 1, max_seconds=30)
        self.assertEqual(len(automaton.nodes), depth + 1)
        self.assertEqual(automaton.state_count_bound, 1 << (depth + 2))
        self.assertTrue(automaton.matches_root(state))
        self.assertTrue(automaton.accepts(state))
        with self.assertRaises(ResourceLimit):
            evaluate(automaton, term, max_term_nodes=depth)
        # Distinct tuples with equal deep contents must not trigger tuple hash.
        left = right = LITERAL_S
        for _ in range(depth):
            left, right = (left, HOLE), (right, HOLE)
        automaton = compile_pattern((left, right), max_seconds=30)
        self.assertEqual(len(automaton.nodes), depth + 3)
        self.assertEqual(automaton.nodes[-1].left, automaton.nodes[-1].right)
        spine = S
        for _ in range(depth):
            spine = App(spine, S)
        self.assertTrue(automaton.matches_root(evaluate(
            automaton, App(spine, spine), max_seconds=30)))

    def test_all_bit_vectors_are_states_even_if_unreachable(self):
        automaton = compile_pattern((HOLE, LITERAL_S))
        self.assertEqual(automaton.state_count_bound, 16)
        for left in range(16):
            for right in range(16):
                state = automaton.transition("application", left, right)
                # Descriptor order is _, S, pair; fourth bit is found.
                root = bool(left & 1 and right & 2)
                expected = 1 | (int(root) << 2) | (int(root or (left | right) & 8 != 0) << 3)
                self.assertEqual(state, expected)
                self.assertLess(state, 16)
        self.assertEqual(automaton.transition("S"), 3)

    def test_transition_uses_only_fixed_code_and_bounded_local_inputs(self):
        automaton = compile_pattern((HOLE, LITERAL_S))
        queries = [("S", None, None)] + [("application", a, b)
                                        for a in range(16) for b in range(16)]
        expected = {query: automaton.transition(*query) for query in queries}
        random.Random(917).shuffle(queries)
        with ExitStack() as stack:
            for target in ("builtins.open", "builtins.hash", "builtins.id",
                           "s_only.pattern_automaton.compile_pattern",
                           "s_only.pattern_automaton.evaluate",
                           "s_only.pattern_automaton.monotonic"):
                stack.enter_context(patch(target, side_effect=AssertionError(target)))
            stack.enter_context(patch.object(App, "__getattribute__",
                                            side_effect=AssertionError("input term read")))
            for query in queries + queries[::-1]:
                self.assertEqual(automaton.transition(*query), expected[query])

    def test_malformed_patterns_are_rejected_before_custom_hooks(self):
        invalid = (None, 1, True, "?", [], (), (HOLE,), (HOLE, HOLE, HOLE),
                   PoisonStr(HOLE), PoisonTuple((HOLE, HOLE)), PoisonObject())
        for value in invalid:
            with self.subTest(value_type=type(value)):
                with self.assertRaises(ValueError):
                    compile_pattern(value)
                with self.assertRaises(ValueError):
                    compile_pattern((HOLE, value))

    def test_malformed_states_and_observations_are_rejected_before_hooks(self):
        automaton = compile_pattern((HOLE, LITERAL_S))
        for state in (-1, 16, 1 << 10000, True, False, 1.0, None, [],
                      PoisonInt(0), PoisonObject()):
            with self.subTest(state_type=type(state)):
                for operation in (automaton.accepts, automaton.matches_root):
                    with self.assertRaises(ValueError):
                        operation(state)
                for children in ((state, 0), (0, state)):
                    with self.assertRaises(ValueError):
                        automaton.transition("application", *children)
        for kind in (None, 1, [], PoisonStr("S"), PoisonObject(), "App"):
            with self.assertRaises(ValueError):
                automaton.transition(kind)
        for children in ((0, None), (None, 0), (PoisonObject(), PoisonObject())):
            with self.assertRaises(ValueError):
                automaton.transition("S", *children)

    def test_metadata_validation_and_immutability(self):
        automaton = compile_pattern((HOLE, LITERAL_S))
        for root in (-1, 0, 3, True, PoisonInt(2), PoisonObject()):
            with self.assertRaises(ValueError):
                PatternAutomaton(automaton.nodes, root)
        for nodes in ([], (), PoisonTuple(automaton.nodes), (PoisonObject(),)):
            with self.assertRaises(ValueError):
                PatternAutomaton(nodes, 0)
        for index, node in enumerate(automaton.nodes):
            for kind in ("?", None, [], PoisonStr(node.kind), PoisonObject()):
                nodes = list(automaton.nodes)
                nodes[index] = replace(node, kind=kind)
                with self.assertRaises(ValueError):
                    PatternAutomaton(tuple(nodes), automaton.root)
            for field in ("left", "right"):
                for value in (-1, index, 999, True, 1.0, PoisonInt(0), PoisonObject()):
                    nodes = list(automaton.nodes)
                    nodes[index] = replace(node, **{field: value})
                    with self.assertRaises(ValueError):
                        PatternAutomaton(tuple(nodes), automaton.root)
        with self.assertRaises(ValueError):
            PatternAutomaton((Descriptor(HOLE), Descriptor(HOLE)), 1)
        with self.assertRaises(ValueError):
            PatternAutomaton((Descriptor(HOLE), Descriptor(LITERAL_S)), 1)
        with self.assertRaises(FrozenInstanceError):
            automaton.root = 0
        with self.assertRaises(FrozenInstanceError):
            automaton.nodes[0].kind = LITERAL_S

    def test_invalid_term_nodes_cycles_and_size_field_are_not_trusted(self):
        automaton = compile_pattern(HOLE)
        class AppSubclass(App):
            def __getattribute__(self, name):
                raise AssertionError("subclass access")
        invalid_subclass = object.__new__(AppSubclass)
        for invalid in (None, "S", (), PoisonObject(), PoisonMetaObject(), invalid_subclass):
            with self.assertRaises(ValueError):
                evaluate(automaton, invalid)
            malformed = App(S, S)
            object.__setattr__(malformed, "right", invalid)
            with self.assertRaises(ValueError):
                evaluate(automaton, malformed)
        cyclic = App(S, S)
        object.__setattr__(cyclic, "right", cyclic)
        with self.assertRaises(ValueError):
            evaluate(automaton, cyclic)
        valid = App(S, S)
        object.__setattr__(valid, "_leaves", PoisonObject())
        self.assertTrue(automaton.accepts(evaluate(automaton, valid)))

    def test_explicit_caps_exact_boundaries_and_invalid_caps(self):
        pattern = (HOLE, LITERAL_S)
        automaton = compile_pattern(pattern, max_descriptors=3, max_pattern_nodes=3)
        evaluate(automaton, App(S, S), max_term_nodes=2)
        for kwargs in ({"max_descriptors": 2}, {"max_pattern_nodes": 2},
                       {"max_seconds": 0}):
            with self.assertRaises(ResourceLimit):
                compile_pattern(pattern, **kwargs)
        for kwargs in ({"max_term_nodes": 1}, {"max_seconds": 0}):
            with self.assertRaises(ResourceLimit):
                evaluate(automaton, App(S, S), **kwargs)
        for value in (-1, True, 1.0, None, PoisonInt(3), PoisonObject()):
            for field in ("max_descriptors", "max_pattern_nodes"):
                with self.assertRaises(ValueError):
                    compile_pattern(pattern, **{field: value})
            with self.assertRaises(ValueError):
                evaluate(automaton, S, max_term_nodes=value)
        for value in (-1, True, None, float("inf"), float("nan"),
                      PoisonInt(3), PoisonObject(), PoisonMetaObject(), 1 << 10000):
            with self.assertRaises(ValueError):
                compile_pattern(pattern, max_seconds=value)
            with self.assertRaises(ValueError):
                evaluate(automaton, S, max_seconds=value)
        # Deterministic cooperative deadline expiry, not wall-time flakiness.
        with patch("s_only.pattern_automaton.monotonic", side_effect=(0.0, 1.0)):
            with self.assertRaises(ResourceLimit):
                compile_pattern(pattern, max_seconds=0.5)
        with patch("s_only.pattern_automaton.monotonic", side_effect=(0.0, 1.0)):
            with self.assertRaises(ResourceLimit):
                evaluate(automaton, S, max_seconds=0.5)


if __name__ == "__main__":
    unittest.main()
