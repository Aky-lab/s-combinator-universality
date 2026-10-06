"""Independent complete transition checks on small finite state covers."""
import unittest

from s_only.pattern_automaton import Descriptor, PatternAutomaton, compile_pattern, evaluate
from s_only.terms import App, S


class PatternAutomatonReviewTests(unittest.TestCase):
    def test_every_child_state_has_the_specified_total_transition(self):
        for pattern in ('_', 'S', ('_', 'S'), ('S', 'S'), (('S', '_'), 'S')):
            automaton = compile_pattern(pattern)
            k = len(automaton.nodes)
            for left in range(2 ** (k + 1)):
                for right in range(2 ** (k + 1)):
                    flags = [node.kind == '_' or (
                        node.kind == 'pair' and bool(left & 2 ** node.left)
                        and bool(right & 2 ** node.right)) for node in automaton.nodes]
                    any_match = flags[automaton.root] or bool((left | right) & 2 ** k)
                    expected = sum(2 ** i for i, flag in enumerate(flags) if flag)
                    expected += 2 ** k if any_match else 0
                    self.assertEqual(automaton.transition('application', left, right), expected)
            self.assertEqual(automaton.state_count_bound, 2 ** (k + 1))

    def test_value_canonicalization_preserves_shared_and_unshared_occurrences(self):
        shared = ('S', 'S')
        first = compile_pattern((shared, shared))
        second = compile_pattern((tuple(['S', 'S']), tuple(['S', 'S'])))
        self.assertEqual(first, second)
        self.assertEqual(first.nodes, (Descriptor('S'), Descriptor('pair', 0, 0),
                                       Descriptor('pair', 1, 1)))
        branch = App(S, S)
        value = App(branch, branch)
        self.assertTrue(first.matches_root(evaluate(first, value)))
        wrapped = App(S, value)
        state = evaluate(first, wrapped)
        self.assertFalse(first.matches_root(state))
        self.assertTrue(first.accepts(state))

    def test_unreachable_descriptors_cannot_inflate_a_claimed_canonical_cover(self):
        with self.assertRaisesRegex(ValueError, 'all descriptors'):
            PatternAutomaton((Descriptor('_'), Descriptor('S')), 1)


if __name__ == '__main__':
    unittest.main()
