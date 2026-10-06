"""Focused checks for docs/local-event-provenance.md.

These inspect the existing 85-step fixture and literal context identities.
They do not execute upstream code, certify an all-input trajectory, or run
the large UT19 controller. Identity tracking is a testing convenience, not
part of the proposed current-tree observer.
"""
import json
from pathlib import Path
import unittest

from s_only.cts import Program
from s_only.cts_reader import compile_reader, _Miss
from s_only.encoding import B, C0, HALT, LIVE, VALUES, compile_program
from s_only.program_selector_parts.patterns import PatternFamily
from s_only.reduction import at, contract_at
from s_only.terms import App, S
from s_only.ut19 import compile_cts


def app(*items):
    result = items[0]
    for item in items[1:]:
        result = App(result, item)
    return result


def h6(term):
    args = []
    while isinstance(term, App):
        args.append(term.right)
        term = term.left
    args.reverse()
    return len(args) == 6 and args[0] is S and args[1] == App(B, S)


def unique_nodes(term):
    seen = set()
    stack = [(term, ())]
    while stack:
        node, path = stack.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        yield node, path
        if isinstance(node, App):
            stack.extend(((node.right, path + (1,)), (node.left, path + (0,))))


def instantiate(pattern):
    """Give every independent pattern hole the closed term S."""
    if isinstance(pattern, str):
        return S
    return App(instantiate(pattern[0]), instantiate(pattern[1]))


def matches(pattern, term):
    stack = [(pattern, term)]
    while stack:
        p, t = stack.pop()
        if p == '_':
            continue
        if p == 'S':
            if t is not S:
                return False
        elif not isinstance(t, App):
            return False
        else:
            stack.extend(((p[0], t.left), (p[1], t.right)))
    return True


class LocalEventProvenanceTests(unittest.TestCase):
    def test_existing_fixture_h6_births_and_frozen_audits(self):
        program = Program(('1', ''))
        compiled = compile_program(program)
        reader = compile_reader(program)
        term = compiled.encode('101')
        fixture = Path(__file__).resolve().parents[1] / 'fixtures/queue_101_path.json'
        steps = json.loads(fixture.read_text())['steps']
        # Retain objects to rule out Python id recycling during the check.
        retained, origins, birth_labels = {}, {}, {}
        previous, mutation_path = None, None
        births = 0
        for sample in range(len(steps) + 1):
            for node, path in unique_nodes(term):
                retained[id(node)] = node
                if not h6(node):
                    continue
                if id(node) not in origins:
                    self.assertIsNotNone(previous)
                    self.assertEqual(mutation_path[:len(path)], path)
                    old = at(previous, path)
                    audit = at(node, (0, 0, 0, 1))
                    if h6(old):
                        origin, frozen = origins[id(old)]
                        self.assertIs(audit, frozen)
                    else:
                        # FRAME's third contraction at LL is the sole birth.
                        self.assertEqual(mutation_path[len(path):], (0, 0))
                        self.assertEqual(old.left.left.left, compiled.act)
                        self.assertIs(old.left.left.right, audit)
                        self.assertIs(old.left.right.right, audit)
                        self.assertIs(old.right.right, audit)
                        self.assertIs(node.left.left.right.right, audit)
                        births += 1
                        origin, frozen = births, audit
                    origins[id(node)] = origin, frozen
                origin, frozen = origins[id(node)]
                self.assertIs(at(node, (0, 0, 0, 1)), frozen)
                try:
                    reader._local(node)
                    label, _ = reader._route(node.left.left.right)
                except _Miss:
                    continue
                if origin in birth_labels:
                    self.assertEqual(label, birth_labels[origin])
                else:
                    birth_labels[origin] = label
            if sample < len(steps):
                previous = term
                mutation_path = tuple(map(int, steps[sample]['path']))
                term = contract_at(term, mutation_path)
        self.assertGreater(births, 0)
        self.assertEqual(set(birth_labels.values()), {(0, 1), (1, 0)})

    def test_accumulator_contraction_does_not_touch_halt_audit(self):
        # A one-leaf completed dispatcher, with one retained history.
        payload = app(LIVE[1], S)
        response = app(app(S, B), payload, app(payload, payload))
        dispatcher = app(S, payload, response)
        local = app(HALT, payload, dispatcher, app(S, S, payload), app(S, payload))
        # LLR, then leaf response R, then L^1 R to the accumulator.
        address = (0, 0, 1, 1, 0, 1)
        changed = contract_at(local, address)
        self.assertIs(at(changed, (0, 0, 0, 1)), payload)
        self.assertNotEqual(at(changed, address), payload)
        self.assertTrue(h6(changed))

    def test_permissive_tombstone_audit_can_hide_fabricated_f17(self):
        program = compile_cts()
        family = PatternFamily(program, required_period=None)
        route_pattern, route, _ = next(row for row in family.dispatch_records()
                                       if row[2] == (17, 1))
        self.assertEqual(route, (0, 1, 0, 0, 0, 1, 1))
        pattern = family.local_pattern('fresh', route_pattern)
        counterfeit = instantiate(pattern)
        self.assertTrue(matches(pattern, counterfeit))
        self.assertTrue(h6(counterfeit))
        queue = app(S, S, app(VALUES[0], counterfeit))
        # Exact mutable Base: original seed is empty; only its active queue differs.
        environment = app(S, app(S, family.compiled.act, app(S, S)))
        c1 = app(B, C0)
        continuation = app(c1, c1, environment)
        alpha = app(environment, app(B, environment), continuation)
        beta = app(environment, continuation, alpha)
        active_environment = app(S, app(S, family.compiled.act, app(S, queue)))
        active_alpha = app(active_environment, app(B, environment), continuation)
        base = app(continuation, active_alpha, beta)
        self.assertEqual(compile_reader(program)._queue(base), '')
        self.assertTrue(any(matches(pattern, node) for node, _ in unique_nodes(base)))


if __name__ == '__main__':
    unittest.main()
