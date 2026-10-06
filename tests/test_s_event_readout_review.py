"""Independent adversarial review of the bounded current-S-tree interface.

Synthetic carriers/events below establish syntax only, never reachability.
Fixture constructors are reused, but assertions, mutation cases, canonical
comparison oracle and work checks are independent of the reader implementation.
"""
import random
import unittest

from s_only import cts, cts_reader, s_event_readout as reader, ut19
from s_only.terms import App, S
import test_s_event_readout as fixture


def snapshot(term):
    budget = reader._Budget(10**12)
    graph, _ = reader._snapshot(term, 100_000, budget)
    return graph, budget.used


def canonical(graph):
    """Intern shapes without using term equality or pairwise graph equality."""
    interned, labels = {}, []
    for left, right in graph.nodes:
        key = None if left < 0 else (labels[left], labels[right])
        if key not in interned:
            interned[key] = len(interned)
        labels.append(interned[key])
    return labels


def replace_at(term, path, value):
    frames = []
    for side in path:
        if type(term) is not App:
            break
        frames.append((term, side))
        term = term.right if side else term.left
    for parent, side in reversed(frames):
        value = fixture.raw_app(parent.left, value) if side else fixture.raw_app(value, parent.right)
    return value


def clone(term):
    graph, _ = snapshot(term)
    nodes = []
    for left, right in graph.nodes:
        nodes.append(type(S)() if left < 0 else App(nodes[left], nodes[right]))
    return nodes[graph.root]


class BoundedReadoutReview(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = ut19.compile_cts()
        cls.tree = fixture.spec(cls.program)
        cls.tail = fixture.hot(fixture.small_event())[18:]
        cls.carrier = fixture.base(cls.tree, fixture.word(cls.tail))
        cls.good = fixture.local(cls.program, cls.tree, S, cls.carrier, (17, 1))
        cls.small_program = cts.Program(("1", "", "101"))
        cls.small_tree = fixture.spec(cls.small_program)
        cls.small = reader.compile_carrier_reader(cls.small_program)

    def test_snapshot_aliases_distinct_atoms_and_captured_edges(self):
        a, b = type(S)(), type(S)()
        shared = fixture.raw_app(a, b)
        term = fixture.raw_app(shared, shared)
        graph, work = snapshot(term)
        self.assertEqual(graph.nodes, ((-1, -1), (-1, -1), (0, 1), (2, 2)))
        self.assertEqual(work, 7)
        self.assertLessEqual(work, 3 * len(graph.nodes))
        object.__setattr__(shared, "left", shared)
        self.assertEqual(graph.nodes[-2], (0, 1))
        with self.assertRaises(ValueError):
            reader.find_ut19_event(term)
        # Post-snapshot recognizers use integer edges, not live input objects.
        original = clone(self.good)
        graph, _ = snapshot(original)
        object.__setattr__(original, "right", object())
        self.assertEqual(reader._witness(graph, reader._Budget(10**8))[0], ())

    def test_every_entry_rejects_missing_children_and_hidden_cycles(self):
        left_missing, right_missing = object.__new__(App), object.__new__(App)
        object.__setattr__(left_missing, "right", S)
        object.__setattr__(right_missing, "left", S)
        cyclic = fixture.raw_app()
        object.__setattr__(cyclic, "left", cyclic)
        shared_bad = fixture.raw_app(S, object())
        malformed = [left_missing, right_missing, cyclic, shared_bad,
                     fixture.raw_app(self.good, left_missing),
                     fixture.raw_app(self.good, cyclic),
                     fixture.raw_app(shared_bad, shared_bad)]
        entries = [reader.find_ut19_event, reader.read_ut19_event,
                   reader.read_s_event_result, self.small.read_carrier]
        for term in malformed:
            for entry in entries:
                with self.subTest(entry=entry.__name__), self.assertRaises(ValueError):
                    entry(term)
        incomplete = object.__new__(reader.SReadoutLimits)
        for entry in entries:
            with self.assertRaisesRegex(ValueError, "incomplete limits"):
                entry(S, limits=incomplete)

    def test_preorder_chooses_malformed_first_payload_instead_of_convenient_later_one(self):
        bad = fixture.local(self.program, self.tree, self.good, S, (17, 1))
        self.assertEqual(reader.find_ut19_event(bad), ())
        with self.assertRaises(ValueError):
            reader.read_ut19_event(bad)
        wrapped = fixture.raw_app(bad, self.good)
        self.assertEqual(reader.find_ut19_event(wrapped), (0,))
        with self.assertRaises(ValueError):
            reader.read_ut19_event(wrapped)
        opaque = fixture.local(self.program, self.tree, S, self.good, (16, 0))
        self.assertEqual(reader.find_ut19_event(opaque), (0, 0, 0, 1))
        self.assertEqual(reader.read_s_event_result(opaque), (0,))

    def test_all_ut19_labels_are_distinguished_despite_repeated_action_code(self):
        negative = S
        for phase in range(len(self.program.appendants)):
            for bit in (0, 1):
                label = phase, bit
                if label == (17, 1):
                    continue
                term = fixture.local(self.program, self.tree, S, S, label)
                negative = fixture.raw_app(negative, term)
        # One DAG shares the fixed program code across all 75 negatives.
        self.assertIsNone(reader.find_ut19_event(negative))
        positive = fixture.local(self.program, self.tree, S, S, (17, 1))
        self.assertEqual(reader.find_ut19_event(fixture.raw_app(negative, positive)), (1,))

    def test_cross_arena_equal_integer_indices_are_not_identity(self):
        term = S
        collision = None
        for index in range(1, 40):
            term = fixture.raw_app(term, S)
            graph, _ = snapshot(term)
            budget = reader._Budget(10**8)
            parser = reader._Parser(self.small, graph, budget, 1000)
            same = parser.same(index, index, code=True)
            if not same:
                collision = index
                self.assertLessEqual(budget.used, 2 * len(graph.nodes) * self.small.code_size + 1)
                break
        self.assertIsNotNone(collision)
        good = fixture.base(self.small_tree, fixture.word("101"))
        self.assertEqual(self.small.read_carrier(clone(good)), "101")

    def test_random_dag_equality_matches_canonical_shape_and_charges_duplicate_pops(self):
        rng = random.Random(74151)
        for trial in range(20):
            nodes = [type(S)(), type(S)()]
            for _ in range(22):
                nodes.append(fixture.raw_app(rng.choice(nodes), rng.choice(nodes)))
            # Retain every independently built subtree in the reachable input.
            term = S
            for node in nodes:
                term = fixture.raw_app(term, node)
            graph, _ = snapshot(term)
            labels = canonical(graph)
            count = len(graph.nodes)
            for _ in range(40):
                a, b = rng.randrange(count), rng.randrange(count)
                budget = reader._Budget(2 * count**2 + 1)
                parser = reader._Parser(self.small, graph, budget, count)
                self.assertEqual(parser.same(a, b), labels[a] == labels[b])
                self.assertLessEqual(budget.used, 2 * count**2 + 1)

    def test_differing_sharing_patterns_compare_as_trees_with_polynomial_charge(self):
        def layered(width, depth):
            current = [type(S)() for _ in range(width)]
            for _ in range(depth):
                current = [App(current[i], current[(i + 1) % width])
                           for i in range(width)]
            return current[0]
        left, right = layered(5, 50), layered(7, 50)
        graph, _ = snapshot(fixture.raw_app(left, right))
        a, b = graph.nodes[graph.root]
        budget = reader._Budget(2 * len(graph.nodes)**2 + 1)
        parser = reader._Parser(self.small, graph, budget, len(graph.nodes))
        self.assertTrue(parser.same(a, b))
        self.assertGreater(budget.used, len(graph.nodes))
        self.assertLessEqual(budget.used, 2 * len(graph.nodes)**2 + 1)
        term = fixture.base(self.small_tree, fixture.word("101"), outer=left, inner=right)
        limits = self.small.limits_for_input_nodes(fixture.node_count(term))
        self.assertEqual(self.small.read_carrier(term, limits=limits), "101")

    def test_differential_irregular_dispatch_mutations_and_sufficient_derived_caps(self):
        rng = random.Random(151)
        checked = 0
        for words in (("",), ("0", "", "0"), ("01", "1", "", "01", "0")):
            program = cts.Program(words)
            tree = fixture.spec(program)
            bounded = reader.compile_carrier_reader(program)
            reference = cts_reader.compile_reader(program)
            opaque = App(S, App(S, S))
            base = fixture.base(tree, fixture.word("010"), seed=opaque, beta=clone(opaque))
            cases = [base, fixture.base(tree, S), fixture.base(tree, base), S]
            for phase in range(len(words)):
                for bit in (0, 1):
                    term = fixture.local(program, tree, base, opaque, (phase, bit),
                                         marked=bool(bit), opaque=clone(opaque), continuation=clone(opaque))
                    term = fixture.raw_app(fixture.live[1], fixture.tombstone(0, term, clone(opaque)))
                    cases.append(term)
                    for _ in range(12):
                        path = tuple(rng.randrange(2) for _ in range(rng.randrange(1, 12)))
                        replacement = rng.choice((S, opaque, base, fixture.word("11")))
                        cases.append(replace_at(term, path, replacement))
            for term in cases:
                graph, work = snapshot(term)
                self.assertLessEqual(work, 3 * len(graph.nodes))
                cap = bounded.limits_for_input_nodes(len(graph.nodes))
                try:
                    expected = reference._queue(term)
                except ValueError:
                    with self.assertRaises(ValueError):
                        bounded.read_carrier(term, limits=cap)
                else:
                    self.assertEqual(bounded.read_carrier(term, limits=cap), expected)
                    self.assertLessEqual(len(expected), len(graph.nodes))
                checked += 1
        self.assertGreater(checked, 240)

    def test_budget_at_reservation_boundary_and_huge_cap_semantics(self):
        result = reader.read_ut19_event(self.good)
        reservation = 1024 * (len(self.tail) + 2)
        for cap in (result.work - reservation, result.work - 1):
            with self.assertRaises(reader.ResourceLimit):
                reader.read_ut19_event(self.good, limits=reader.SReadoutLimits(max_work=cap))
        self.assertEqual(reader.read_ut19_event(self.good,
                         limits=reader.SReadoutLimits(max_work=result.work)), result)
        # Large plain integer caps remain legal. Their bit cost is additional
        # to charged work, so an N+C-only bit-cost theorem needs qualification.
        huge = 1 << 200_000
        limits = reader.SReadoutLimits(huge, huge, huge, huge, huge, huge)
        self.assertIsNone(reader.find_ut19_event(S, limits=limits))


if __name__ == "__main__":
    unittest.main()
