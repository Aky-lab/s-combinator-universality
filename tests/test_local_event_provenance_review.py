"""Independent small-AST checks for the local provenance review.

No production reducer, parser, selector, or encoder is imported.  These are
finite scaffold/negative-control checks, not an all-input reachability proof.
"""
from dataclasses import dataclass
import unittest


S = object()


@dataclass(frozen=True, eq=False)
class Node:
    left: object
    right: object


def app(head, *args):
    for arg in args:
        head = Node(head, arg)
    return head


def equal(left, right):
    pending = [(left, right)]
    while pending:
        a, b = pending.pop()
        if a is b:
            continue
        if not isinstance(a, Node) or not isinstance(b, Node):
            return False
        pending.extend(((a.left, b.left), (a.right, b.right)))
    return True


def spine(term):
    args = []
    while isinstance(term, Node):
        args.append(term.right)
        term = term.left
    return tuple(reversed(args))


b = app(S, S)
h = app(b, S)
H = app(b, h)
pi = app(S, b)
c0 = app(pi, b)
values = (app(S, c0), app(S, app(S, c0)))
lives = tuple(app(b, value) for value in values)


def signature(term, arity=6):
    args = spine(term)
    return len(args) == arity and args[0] is S and equal(args[1], h)


def lookup(term, path):
    for edge in path:
        term = term.right if edge else term.left
    return term


def replace(term, path, target):
    parents = []
    for edge in path:
        parents.append((term, edge))
        term = term.right if edge else term.left
    for node, edge in reversed(parents):
        target = Node(node.left, target) if edge else Node(target, node.right)
    return target


def reduce_at(term, path):
    redex = lookup(term, path)
    args = spine(redex)
    assert len(args) == 3
    a, z, x = args
    return replace(term, path, app(a, x, app(z, x)))


def distinct_nodes(term):
    seen, pending = set(), [term]
    while pending:
        node = pending.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        yield node
        if isinstance(node, Node):
            pending.extend((node.left, node.right))


def numeral(n):
    term = c0
    for _ in range(n):
        term = app(b, term)
    return term


def word(bits):
    term = S
    for bit in bits:
        term = app(lives[int(bit)], term)
    return term


def routine(bits):
    term = pi
    for bit in reversed(bits):
        term = app(S, app(S, term), lives[int(bit)])
    return term


def compile_tree(tree):
    code = routine(tree) if isinstance(tree, str) else app(
        S, compile_tree(tree[0]), compile_tree(tree[1]))
    return app(b, code)


def environment(tree, bits=""):
    return app(S, app(S, app(S, H, compile_tree(tree)), app(S, word(bits))))


def clock_exit(stage, wrappers, env):
    term = app(numeral(stage + 1), numeral(stage + 1))
    for _ in range(wrappers):
        term = app(S, numeral(stage), term)
    return app(term, env)


def base(env, continuation):
    alpha = app(env, app(b, env), continuation)
    return app(continuation, alpha, app(env, continuation, alpha))


def shell(snapshot, dispatch, continuation, marked=False):
    halt = app(S, snapshot, app(h, snapshot)) if marked else app(H, snapshot)
    return app(halt, dispatch, app(S, S, snapshot), app(continuation, snapshot))


def completed(snapshot, continuation, bit=None):
    accumulator = snapshot if bit is None else app(lives[bit], snapshot)
    action = app(pi, accumulator)
    if bit is not None:
        action = app(action, app(snapshot, accumulator))
    return shell(snapshot, app(S, snapshot, action), continuation)


class LocalEventProvenanceReviewTests(unittest.TestCase):
    def assert_step_origins(self, before, path, birth=None):
        """Check copied roots, every rebuilt ancestor, and all new nodes."""
        after = reduce_at(before, path)
        old_ids = {id(node) for node in distinct_nodes(before) if signature(node)}
        allowed = set(old_ids)
        inherited = []
        for length in range(len(path) + 1):
            address = path[:length]
            old, new = lookup(before, address), lookup(after, address)
            if signature(new) and signature(old):
                self.assertIs(lookup(new, (0, 0, 0, 1)),
                              lookup(old, (0, 0, 0, 1)))
                allowed.add(id(new))
                inherited.append(address)
        if birth is not None:
            self.assertTrue(signature(lookup(after, birth)))
            self.assertFalse(signature(lookup(before, birth)))
            allowed.add(id(lookup(after, birth)))
        for node in distinct_nodes(after):
            if signature(node):
                self.assertIn(id(node), allowed)
        return after

    def test_all_seven_fuel_residuals_and_outer_contexts(self):
        env = environment(("01", ""), "10")
        for wrappers in (0, 2):
            continuation = clock_exit(2, wrappers, env)
            snapshot = base(env, continuation)
            for fuel, paths in ((0, ((0,), (0,), (), (0,), ())),
                                (2, ((0,), ()))):
                endpoint = app(numeral(fuel), env, continuation)
                # Test plain, pending, fresh-continuation and marked-continuation
                # contexts. The latter two contain the dangerous K A ancestor.
                contexts = (
                    (endpoint, ()),
                    (app(env, continuation, endpoint), (1,)),
                    (completed(snapshot, endpoint), (1, 0)),
                    (shell(snapshot, app(S, snapshot, app(pi, snapshot)),
                           endpoint, marked=True), (1, 0)),
                )
                for initial, prefix in contexts:
                    term = initial
                    for path in paths:
                        term = self.assert_step_origins(term, prefix + path)
                        self.assertFalse(signature(lookup(term, prefix), 5))
                if fuel == 0:
                    for path in paths:
                        endpoint = reduce_at(endpoint, path)
                    self.assertTrue(equal(endpoint, base(env, continuation)))
                else:
                    for path in paths:
                        endpoint = reduce_at(endpoint, path)
                    # The easily omitted second positive-FUEL form is S D B X.
                    self.assertEqual(len(spine(endpoint)), 3)
                    self.assertIs(spine(endpoint)[0], env.right)

    def test_clock_expansion_and_launch(self):
        env = environment(("", "1"), "01")
        for stage in range(4):
            term = app(numeral(stage), numeral(stage), env)
            for wrappers in range(stage + 1):
                term = self.assert_step_origins(term, (0,) + (1,) * wrappers)
                self.assertFalse(signature(term, 5))
            self.assertTrue(equal(term, clock_exit(stage, stage, env)))
            if stage:
                launched = self.assert_step_origins(term, ())
                self.assertTrue(equal(launched,
                    app(numeral(stage), env, clock_exit(stage, stage - 1, env))))

    def test_frame_birth_route_and_all_appender_intermediates(self):
        tree = (("", "01"), ("1", "0" * 17 + "10"))
        env = environment(tree, "10")
        continuation = clock_exit(2, 0, env)
        raw = base(env, continuation)
        # Include already genuine nested Locals in every copied snapshot.
        snapshot = completed(completed(raw, continuation), continuation, 1)
        for route, bits in (((0, 0), ""), ((0, 1), "01"),
                            ((1, 0), "1"), ((1, 1), "0" * 17 + "10")):
            frame = app(env, continuation, snapshot)
            # The active frame is the K child of a genuine outer K A context.
            term = completed(raw, frame)
            prefix = (1, 0)
            for path in ((), (0,)):
                term = self.assert_step_origins(term, prefix + path)
                self.assertFalse(signature(lookup(term, prefix), 5))
            term = self.assert_step_origins(term, prefix + (0, 0), birth=prefix)
            active = prefix + (0, 0, 1)
            for turn in route:
                term = self.assert_step_origins(term, active)
                term = self.assert_step_origins(term, active + (1,))
                active += (1, turn)
            term = self.assert_step_origins(term, active)
            action = active + (1,)
            for index in range(len(bits)):
                for half in range(2):
                    term = self.assert_step_origins(term, action + (0,) * index)
                    args = spine(lookup(term, action))
                    done = index == len(bits) - 1 and half == 1
                    self.assertEqual(bool(args and equal(args[0], b)), done)
            args = spine(lookup(term, action))
            self.assertEqual(len(args), len(bits) + 2)
            self.assertTrue(equal(args[0], b))
            self.assertIs(lookup(term, prefix + (0, 0, 0, 1)), snapshot)

    def test_c4_inside_nested_local_preserves_both_audits(self):
        env = environment(("", "1"))
        continuation = clock_exit(1, 0, env)
        raw = base(env, continuation)
        inner = completed(raw, continuation, 1)
        outer = completed(inner, continuation, 0)
        accumulator = (0, 0, 1, 1, 0, 1)
        # The first logical cell is inside the old current Local, below the
        # outer Local's appended zero wrapper.
        selected = accumulator + (1,) + accumulator
        changed = self.assert_step_origins(outer, selected)
        self.assertIs(lookup(changed, (0, 0, 0, 1)), inner)
        current_inner = lookup(changed, accumulator + (1,))
        self.assertIs(lookup(current_inner, (0, 0, 0, 1)), raw)
        # A fresh empty Local is copied into a new tombstone audit by C4.
        empty_local = completed(raw, continuation)
        copied = self.assert_step_origins(app(lives[0], empty_local), ())
        self.assertIs(copied.left.right, empty_local)
        self.assertIs(copied.right.right, empty_local)

    def test_commit_removes_only_the_selected_fresh_signature(self):
        env = environment(("", "1"))
        continuation = clock_exit(1, 0, env)
        raw = base(env, continuation)
        inner = completed(raw, continuation)
        outer = completed(inner, continuation)
        changed = self.assert_step_origins(outer, (0, 0, 0))
        self.assertFalse(signature(changed))
        self.assertEqual(len(spine(changed)), 5)
        self.assertIs(spine(changed)[0], inner)
        self.assertTrue(signature(inner))

    def test_generic_s_rewrite_can_manufacture_h6_across_k_a(self):
        # This is deliberately NOT a generated endpoint. It is the negative
        # control showing that K's classification is logically indispensable.
        dispatch = app(S, S, app(pi, S))
        continuation_audit = app(S, S)
        endpoint = app(S, app(H, S), app(S, S), dispatch)
        before = app(endpoint, continuation_audit)
        self.assertFalse(any(signature(node) for node in distinct_nodes(before)))
        after = reduce_at(before, (0,))
        self.assertTrue(signature(after.left, 5))
        self.assertTrue(signature(after))
        self.assertTrue(equal(after, app(H, S, dispatch,
                                        app(S, S, dispatch), continuation_audit)))


if __name__ == "__main__":
    unittest.main()
