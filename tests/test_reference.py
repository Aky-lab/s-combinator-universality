"""Independent, exhaustive finite checks for the S-only reduction kernel.

The oracle uses only nested built-in tuples and the string ``'S'``.  In
particular it never invokes production redex matching, traversal, contraction,
or strategy selection to calculate an expected result.  Finite checks validate
an implementation; they do not establish termination or universality.
"""

from copy import deepcopy
from functools import lru_cache
import hashlib
import json
import unittest
from unittest.mock import patch

from s_only.terms import App, S, format_term, leaves, parse
from s_only.reduction import contract_at, redex_paths, select_path, reduce
from s_only.traces import certificate, verify_certificate


ATOM = "S"


@lru_cache(maxsize=None)
def reference_trees(size):
    """All closed ordered binary S trees with exactly ``size`` leaves."""
    if size == 1:
        return (ATOM,)
    if size < 1:
        return ()
    return tuple(
        (left, right)
        for split in range(1, size)
        for left in reference_trees(split)
        for right in reference_trees(size - split)
    )


def reference_format(tree):
    if tree == ATOM:
        return ATOM
    return "(" + reference_format(tree[0]) + " " + reference_format(tree[1]) + ")"


def reference_leaves(tree):
    if tree == ATOM:
        return 1
    return reference_leaves(tree[0]) + reference_leaves(tree[1])


def reference_paths(tree, path=()):
    """All existing positions in independent root-left-right order."""
    yield path
    if tree != ATOM:
        yield from reference_paths(tree[0], path + (0,))
        yield from reference_paths(tree[1], path + (1,))


def reference_subterm(tree, path):
    for direction in path:
        if direction not in (0, 1) or tree == ATOM:
            raise ValueError("invalid reference path")
        tree = tree[direction]
    return tree


def reference_arguments(tree):
    """Return x, y, z exactly when tree is (((S x) y) z)."""
    if tree == ATOM:
        return None
    left, z = tree
    if left == ATOM:
        return None
    leftleft, y = left
    if leftleft == ATOM:
        return None
    head, x = leftleft
    if head != ATOM:
        return None
    return x, y, z


def reference_redex_paths(tree):
    return tuple(
        path for path in reference_paths(tree)
        if reference_arguments(reference_subterm(tree, path)) is not None
    )


def reference_contract(tree, path):
    """Independent rewrite with tuple rebuilding and literal S equation."""
    if path:
        direction, tail = path[0], path[1:]
        if direction not in (0, 1) or tree == ATOM:
            raise ValueError("invalid reference path")
        if direction == 0:
            return (reference_contract(tree[0], tail), tree[1])
        return (tree[0], reference_contract(tree[1], tail))
    arguments = reference_arguments(tree)
    if arguments is None:
        raise ValueError("not an S redex")
    x, y, z = arguments
    return ((x, z), (y, z))


def reference_select(tree, strategy):
    if strategy == "normal":
        return next(iter(reference_redex_paths(tree)), None)
    if strategy == "applicative":
        def postorder(current, path):
            if current == ATOM:
                return
            yield from postorder(current[0], path + (0,))
            yield from postorder(current[1], path + (1,))
            if reference_arguments(current) is not None:
                yield path
        return next(postorder(tree, ()), None)
    if strategy == "head":
        path = ()
        while tree != ATOM:
            if reference_arguments(tree) is not None:
                return path
            tree = tree[0]
            path += (0,)
        return None
    raise ValueError("unknown reference strategy")


def reference_reduce(tree, strategy, max_steps, max_nodes):
    """Bounded simulation whose budgets count expanded tree occurrences."""
    path_history = []
    if 2 * reference_leaves(tree) - 1 > max_nodes:
        return tree, tuple(path_history), "node_limit"
    while True:
        path = reference_select(tree, strategy)
        if path is None:
            status = "normal_form" if not reference_redex_paths(tree) else "head_normal_form"
            return tree, tuple(path_history), status
        if len(path_history) >= max_steps:
            return tree, tuple(path_history), "step_limit"
        after = reference_contract(tree, path)
        if 2 * reference_leaves(after) - 1 > max_nodes:
            return tree, tuple(path_history), "node_limit"
        tree = after
        path_history.append(path)


def reference_prefix(tree):
    if tree == ATOM:
        return ATOM
    return "A" + reference_prefix(tree[0]) + reference_prefix(tree[1])


def reference_certificate(tree, strategy, max_steps, max_nodes):
    final, paths, status = reference_reduce(tree, strategy, max_steps, max_nodes)
    current = tree
    records = []
    for path in paths:
        current = reference_contract(current, path)
        serial = reference_prefix(current)
        records.append({
            "path": "".join(str(direction) for direction in path),
            "after_sha256": hashlib.sha256(serial.encode("ascii")).hexdigest(),
            "nodes": 2 * reference_leaves(current) - 1,
        })
    return {
        "schema": "s-only-trace-v1",
        "initial_prefix": reference_prefix(tree),
        "final_prefix": reference_prefix(final),
        "strategy": strategy,
        "max_steps": max_steps,
        "max_nodes": max_nodes,
        "status": status,
        "steps": records,
    }


def production_tree(tree):
    """Construct without the production parser, keeping tests decoupled."""
    if tree == ATOM:
        return S
    return App(production_tree(tree[0]), production_tree(tree[1]))


def tuple_tree(term):
    """Read production syntax only, without reduction helpers."""
    if term == S:
        return ATOM
    if not isinstance(term, App):
        raise TypeError("unexpected production term type")
    return (tuple_tree(term.left), tuple_tree(term.right))


class IndependentReferenceTests(unittest.TestCase):
    def all_small_trees(self):
        for size in range(1, 9):
            yield from reference_trees(size)

    def test_exhaustive_generator_has_catalan_counts(self):
        self.assertEqual(
            [len(reference_trees(n)) for n in range(1, 9)],
            [1, 1, 2, 5, 14, 42, 132, 429],
        )
        trees = list(self.all_small_trees())
        self.assertEqual(len(trees), 626)
        self.assertEqual(len(set(trees)), 626)

    def test_parser_and_formatter_round_trip_all_trees_through_eight_leaves(self):
        for tree in self.all_small_trees():
            source = reference_format(tree)
            with self.subTest(term=source):
                actual = production_tree(tree)
                self.assertEqual(tuple_tree(parse(source)), tree)
                self.assertEqual(tuple_tree(parse(format_term(actual))), tree)
                self.assertEqual(leaves(actual), reference_leaves(tree))

    def test_all_redexes_and_every_subterm_path_through_eight_leaves(self):
        checked_redexes = 0
        for tree in self.all_small_trees():
            source = reference_format(tree)
            actual = production_tree(tree)
            expected_paths = reference_redex_paths(tree)
            with self.subTest(term=source):
                self.assertEqual(tuple(redex_paths(actual)), expected_paths)
            for path in reference_paths(tree):
                with self.subTest(term=source, path=path):
                    if path not in expected_paths:
                        with self.assertRaises(ValueError):
                            contract_at(actual, path)
                        continue
                    checked_redexes += 1
                    expected = reference_contract(tree, path)
                    rewritten = contract_at(actual, path)
                    self.assertEqual(tuple_tree(rewritten), expected)
                    # Rewriting must leave the input tree unchanged.
                    self.assertEqual(tuple_tree(actual), tree)
                    z = reference_arguments(reference_subterm(tree, path))[2]
                    self.assertEqual(
                        leaves(rewritten) - leaves(actual),
                        reference_leaves(z) - 1,
                    )
        self.assertGreater(checked_redexes, 0)

    def test_all_strategy_selections_through_eight_leaves(self):
        for tree in self.all_small_trees():
            term = production_tree(tree)
            for strategy in ("normal", "applicative", "head"):
                with self.subTest(term=reference_format(tree), strategy=strategy):
                    self.assertEqual(select_path(term, strategy), reference_select(tree, strategy))

    def test_reference_rule_duplicates_third_argument(self):
        x, y, z = ATOM, (ATOM, ATOM), ((ATOM, ATOM), ATOM)
        redex = (((ATOM, x), y), z)
        expected = ((x, z), (y, z))
        self.assertEqual(tuple_tree(contract_at(production_tree(redex), ())), expected)

    def test_overapplication_contracts_left_child(self):
        # S S S S S is not itself an exact redex: its left child is.
        tree = ((((ATOM, ATOM), ATOM), ATOM), ATOM)
        self.assertEqual(reference_redex_paths(tree), ((0,),))
        term = production_tree(tree)
        self.assertEqual(tuple(redex_paths(term)), ((0,),))
        self.assertEqual(tuple_tree(contract_at(term, (0,))), reference_contract(tree, (0,)))

    def test_head_normal_form_can_contain_an_argument_redex(self):
        redex = (((ATOM, ATOM), ATOM), ATOM)
        tree = (ATOM, redex)
        term = production_tree(tree)
        self.assertIsNone(select_path(term, "head"))
        self.assertEqual(select_path(term, "normal"), (1,))
        self.assertEqual(select_path(term, "applicative"), (1,))

    def test_normal_and_applicative_choose_different_nested_redexes(self):
        nested = (((ATOM, ATOM), ATOM), ATOM)
        tree = (((ATOM, nested), ATOM), ATOM)
        term = production_tree(tree)
        self.assertEqual(select_path(term, "normal"), ())
        self.assertEqual(select_path(term, "applicative"), (0, 0, 1))
        self.assertEqual(select_path(term, "head"), ())

    def test_parser_application_is_left_associative(self):
        self.assertEqual(tuple_tree(parse("S S S")), ((ATOM, ATOM), ATOM))
        self.assertEqual(tuple_tree(parse("S (S S)")), (ATOM, (ATOM, ATOM)))
        self.assertEqual(tuple_tree(parse(" \t(S\nS) \r\n S ")), ((ATOM, ATOM), ATOM))

    def test_parser_rejects_non_s_syntax(self):
        for source in ("", " ", "()", "(", ")", "(S", "S)", "(S))", "K", "x", "S + S", "[S]", "S1"):
            with self.subTest(source=source):
                with self.assertRaises(ValueError):
                    parse(source)

    def test_invalid_and_out_of_tree_paths_rejected(self):
        term = production_tree((((ATOM, ATOM), ATOM), ATOM))
        for path in ((2,), (-1,), (True,), (False,), (0.0,), ("0",), (1, 0), (0, 0, 0, 0), (0, 2)):
            with self.subTest(path=path):
                with self.assertRaises(ValueError):
                    contract_at(term, path)

    def test_unknown_strategy_rejected_even_without_redex(self):
        for term in (S, production_tree((((ATOM, ATOM), ATOM), ATOM))):
            with self.assertRaises(ValueError):
                select_path(term, "not-a-strategy")


class IndependentBoundedReductionTests(unittest.TestCase):
    def test_all_bounded_reductions_through_eight_leaves(self):
        for size in range(1, 9):
            for tree in reference_trees(size):
                for strategy in ("normal", "applicative", "head"):
                    with self.subTest(term=reference_format(tree), strategy=strategy):
                        expected, expected_paths, expected_status = reference_reduce(
                            tree, strategy, max_steps=9, max_nodes=255,
                        )
                        initial = production_tree(tree)
                        result = reduce(initial, strategy, max_steps=9, max_nodes=255)
                        self.assertEqual(tuple_tree(result.initial), tree)
                        self.assertEqual(tuple_tree(result.final), expected)
                        self.assertEqual(tuple(result.paths), expected_paths)
                        self.assertEqual(result.status, expected_status)
                        self.assertEqual(result.strategy, strategy)
                        self.assertEqual(result.max_steps, 9)
                        self.assertEqual(result.max_nodes, 255)

    def test_budget_stops_before_growth_and_preserves_input(self):
        # S S S (S S): five leaves initially, six after one contraction.
        tree = (((ATOM, ATOM), ATOM), (ATOM, ATOM))
        initial = production_tree(tree)
        stopped = reduce(initial, "normal", max_steps=10, max_nodes=9)
        self.assertEqual(stopped.status, "node_limit")
        self.assertEqual(tuple(stopped.paths), ())
        self.assertEqual(tuple_tree(stopped.final), tree)
        allowed = reduce(initial, "normal", max_steps=1, max_nodes=11)
        self.assertEqual(tuple(allowed.paths), ((),))
        self.assertEqual(tuple_tree(allowed.final), reference_contract(tree, ()))

    def test_initial_oversize_is_reported_without_reduction(self):
        initial = App(S, S)
        result = reduce(initial, "normal", max_steps=10, max_nodes=2)
        self.assertEqual(result.status, "node_limit")
        self.assertEqual(result.final, initial)
        self.assertEqual(tuple(result.paths), ())

    def test_zero_steps_distinguishes_terminal_from_budget_exhausted(self):
        for strategy in ("normal", "applicative", "head"):
            with self.subTest(strategy=strategy):
                terminal = reduce(S, strategy, max_steps=0, max_nodes=1)
                expected_status = "normal_form"
                self.assertEqual(terminal.status, expected_status)
                active = production_tree((((ATOM, ATOM), ATOM), ATOM))
                limited = reduce(active, strategy, max_steps=0, max_nodes=7)
                self.assertEqual(limited.status, "step_limit")
                self.assertEqual(tuple(limited.paths), ())

    def test_terminal_result_on_the_last_permitted_step(self):
        initial = production_tree((((ATOM, ATOM), ATOM), ATOM))
        result = reduce(initial, "normal", max_steps=1, max_nodes=7)
        self.assertEqual(result.status, "normal_form")
        self.assertEqual(tuple(result.paths), ((),))
        self.assertEqual(tuple_tree(result.final), ((ATOM, ATOM), (ATOM, ATOM)))


    def test_invalid_reduction_budgets_are_rejected(self):
        for steps in (-1, 1.5, True, False, None):
            with self.subTest(max_steps=steps):
                with self.assertRaises(ValueError):
                    reduce(S, "normal", max_steps=steps)
        for budget in (-1, 0, 1.5, True, False, None):
            with self.subTest(max_nodes=budget):
                with self.assertRaises(ValueError):
                    reduce(S, "normal", max_nodes=budget)
        with self.assertRaises(ValueError):
            reduce(S, "unknown", 0, 1)


class IndependentCertificateTests(unittest.TestCase):
    def test_generated_certificates_and_independent_replay_all_small_trees(self):
        for size in range(1, 9):
            for tree in reference_trees(size):
                for strategy in ("normal", "applicative", "head"):
                    with self.subTest(term=reference_format(tree), strategy=strategy):
                        expected = reference_certificate(tree, strategy, 9, 255)
                        result = reduce(production_tree(tree), strategy, 9, 255)
                        emitted = certificate(result)
                        self.assertEqual(emitted, expected)
                        expected_final, _, _ = reference_reduce(tree, strategy, 9, 255)
                        # Pass through JSON: tuples/objects cannot leak into a
                        # purportedly portable certificate unnoticed.
                        loaded = json.loads(json.dumps(emitted))
                        self.assertEqual(verify_certificate(loaded), reference_format(expected_final))
                        # Also verify a certificate built without any production
                        # reduction or serialization function.
                        self.assertEqual(verify_certificate(expected), reference_format(expected_final))

    def test_certificate_verifier_is_independent_of_production_kernel(self):
        tree = (((ATOM, (ATOM, ATOM)), ATOM), ATOM)
        payload = reference_certificate(tree, "normal", 9, 255)
        final, _, _ = reference_reduce(tree, "normal", 9, 255)
        with patch("s_only.reduction.contract_at", side_effect=AssertionError("production contraction used")), \
             patch("s_only.reduction.select_path", side_effect=AssertionError("production selector used")), \
             patch("s_only.reduction.redex_paths", side_effect=AssertionError("production traversal used")), \
             patch("s_only.terms.parse", side_effect=AssertionError("production parser used")), \
             patch("s_only.terms.prefix", side_effect=AssertionError("production serializer used")), \
             patch("s_only.terms.format_term", side_effect=AssertionError("production formatter used")):
            self.assertEqual(verify_certificate(payload), reference_format(final))

    def test_valid_node_limit_certificates_cover_initial_and_next_step_limits(self):
        cases = (
            ((ATOM, ATOM), 10, 2),
            ((((ATOM, ATOM), ATOM), (ATOM, ATOM)), 10, 9),
        )
        for tree, max_steps, max_nodes in cases:
            with self.subTest(term=reference_format(tree), max_nodes=max_nodes):
                payload = reference_certificate(tree, "normal", max_steps, max_nodes)
                self.assertEqual(payload["status"], "node_limit")
                self.assertEqual(payload["steps"], [])
                self.assertEqual(verify_certificate(payload), reference_format(tree))
                result = reduce(production_tree(tree), "normal", max_steps, max_nodes)
                self.assertEqual(certificate(result), payload)

    def test_certificate_rejects_tampered_fields(self):
        inner = (((ATOM, ATOM), ATOM), ATOM)
        tree = (((ATOM, inner), ATOM), ATOM)
        original = reference_certificate(tree, "normal", 3, 255)
        self.assertTrue(original["steps"])
        mutations = [
            ("schema", "other-schema"),
            ("initial_prefix", "K"),
            ("initial_prefix", original["initial_prefix"] + "S"),
            ("final_prefix", "S"),
            ("strategy", "applicative"),
            ("strategy", "unknown"),
            ("status", "divergent"),
            ("max_steps", -1),
            ("max_steps", True),
            ("max_steps", 0),
            ("max_nodes", 0),
            ("max_nodes", True),
            ("max_nodes", 1),
            ("steps", {}),
        ]
        for key, value in mutations:
            with self.subTest(field=key, value=value):
                changed = deepcopy(original)
                changed[key] = value
                with self.assertRaises(ValueError):
                    verify_certificate(changed)
        for key, value in (("path", "001"), ("path", "2"),
                           ("after_sha256", "0" * 64), ("nodes", -1),
                           ("nodes", True)):
            with self.subTest(record_field=key, value=value):
                changed = deepcopy(original)
                changed["steps"][0][key] = value
                with self.assertRaises(ValueError):
                    verify_certificate(changed)

    def test_certificate_rejects_missing_and_extra_fields(self):
        original = reference_certificate((((ATOM, ATOM), ATOM), ATOM), "normal", 1, 7)
        for key in tuple(original):
            with self.subTest(missing=key):
                changed = deepcopy(original)
                del changed[key]
                with self.assertRaises(ValueError):
                    verify_certificate(changed)
        changed = deepcopy(original)
        changed["unexpected"] = 1
        with self.assertRaises(ValueError):
            verify_certificate(changed)
        for key in tuple(original["steps"][0]):
            with self.subTest(missing_record_field=key):
                changed = deepcopy(original)
                del changed["steps"][0][key]
                with self.assertRaises(ValueError):
                    verify_certificate(changed)
        changed = deepcopy(original)
        changed["steps"][0]["unexpected"] = 1
        with self.assertRaises(ValueError):
            verify_certificate(changed)

    def test_certificate_rejects_premature_stopping(self):
        tree = (((ATOM, ATOM), ATOM), ATOM)
        changed = reference_certificate(tree, "normal", 0, 100)
        changed["max_steps"] = 10
        # The tree really is reducible and there is ample budget. Calling it
        # step-limited, node-limited, or terminal cannot justify the stop.
        for status in ("step_limit", "node_limit", "normal_form", "head_normal_form"):
            with self.subTest(status=status):
                changed["status"] = status
                with self.assertRaises(ValueError):
                    verify_certificate(changed)

    def test_certificate_cannot_relabel_head_normal_form_as_full_normal_form(self):
        inner = (((ATOM, ATOM), ATOM), ATOM)
        tree = (ATOM, inner)
        valid = reference_certificate(tree, "head", 10, 100)
        self.assertEqual(valid["status"], "head_normal_form")
        self.assertEqual(verify_certificate(valid), reference_format(tree))
        changed = deepcopy(valid)
        changed["status"] = "normal_form"
        with self.assertRaises(ValueError):
            verify_certificate(changed)

    def test_certificate_rejects_malformed_prefix_trees(self):
        valid = reference_certificate(ATOM, "normal", 0, 1)
        for serial in ("", "A", "AS", "ASSA", "SS", "B", "(S)", "S S", None, 1):
            with self.subTest(serial=serial):
                changed = deepcopy(valid)
                changed["initial_prefix"] = serial
                changed["final_prefix"] = serial
                with self.assertRaises(ValueError):
                    verify_certificate(changed)


if __name__ == "__main__":
    unittest.main()
