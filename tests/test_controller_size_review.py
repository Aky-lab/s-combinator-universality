"""Independent operation-sequence checks of sparse index accounting."""
import random
import unittest

from s_only.controller_size import CountingGraphBuilder
from s_only.selector_parts.graph import GraphBuilder
from s_only.succinct_selector import SuccinctGraphBuilder


class ControllerSizeReviewTests(unittest.TestCase):
    def test_mixed_sequences_preserve_every_returned_index(self):
        rng = random.Random(804013)
        patterns = ('_', 'S', ('_', '_'), ('S', '_'), ('_', 'S'),
                    (('S', '_'), ('_', 'S')))
        for _ in range(30):
            dense = GraphBuilder()
            sparse = CountingGraphBuilder(max_pattern_work=100_000, max_compile_seconds=5)
            for builder in (dense, sparse):
                builder.uniform('normal')
                builder.uniform('contracted')
            for _ in range(30):
                choice = rng.randrange(7)
                yes, no = rng.randrange(2), rng.randrange(2)
                if choice == 0:
                    pattern = rng.choice(patterns)
                    left = dense.match(pattern, yes, no)
                    right = sparse.match(pattern, yes, no)
                elif choice == 1:
                    rows = tuple((rng.choice(patterns), ()) for _ in range(rng.randrange(4)))
                    left = dense.rows(rows, yes, no)
                    right = sparse.rows(rows, yes, no)
                elif choice in (2, 3, 4):
                    rows = tuple((rng.choice(patterns[2:]), (rng.randrange(2),))
                                 for _ in range(rng.randrange(4)))
                    method = ('inverse_rows', 'descent', 'ascent')[choice - 2]
                    args = (rows, yes, no) if choice == 2 else (rows, yes)
                    left = getattr(dense, method)(*args)
                    right = getattr(sparse, method)(*args)
                elif choice == 5:
                    left, right = dense.root(yes), sparse.root(yes)
                else:
                    left, right = dense.reserve(), sparse.reserve()
                    dense.jump(left, yes)
                    sparse.jump(right, yes)
                self.assertEqual(right, left)
                self.assertEqual(sparse.state_count, len(dense.states))
            self.assertEqual(sparse.finish(0).state_count, len(dense.finish()))

    def test_shared_pattern_counts_exceed_machine_sequence_lengths(self):
        pattern = 'S'
        for _ in range(80):
            pattern = (pattern, pattern)
        sparse = CountingGraphBuilder(max_pattern_work=1000, max_compile_seconds=5)
        succinct = SuccinctGraphBuilder(max_metadata_records=1000, max_compile_seconds=5)
        for builder in (sparse, succinct):
            builder.uniform('normal')
            builder.uniform('contracted')
        a, b = sparse.match(pattern, 1, 0), succinct.match(pattern, 1, 0)
        table, counted = succinct.finish(b), sparse.finish(a)
        self.assertEqual((counted.state_count, counted.start), (table.state_count, table.start))
        self.assertEqual(counted.state_count, 7 * 2**80 - 4)
        self.assertGreater(counted.state_count, 2**63)


if __name__ == '__main__':
    unittest.main()
