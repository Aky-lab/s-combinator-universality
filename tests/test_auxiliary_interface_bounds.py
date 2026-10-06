"""Syntax-only checks for the composed encoder's allocation identities."""
import unittest
from unittest.mock import patch

from s_only import encoding, ut19
from test_universal_bp2_frontend import (
    amnesiac_compile, waterfall_compile, bp2_compile,
)


class AuxiliaryInterfaceBoundsTests(unittest.TestCase):
    def test_composed_source_allocation_without_source_execution(self):
        cases = (((('halt',),), (0,)),
                 ((('halt',),), (3,)),
                 ((('inc', 0, 0),), (0,)))  # syntactically infinite source
        for source, values in cases:
            with self.subTest(source=source, values=values):
                with patch('test_universal_bp2_frontend.source_step',
                           side_effect=AssertionError('source execution')):
                    init, triggers, action, _ = amnesiac_compile(source, values)
                    clocks, rows, halt, _ = waterfall_compile(init, triggers, action)
                    code, labels, _ = bp2_compile(clocks, rows, halt)
                k = len(values) + sum(x[0] == 'inc' for x in source)
                k += 4 * sum(x[0] == 'dec' for x in source)
                length = 168*k*k + 124*k + 19 + 4*sum(values)
                self.assertEqual((len(code), labels), (length, 8*k+3))
                program = ut19.SourceProgram(tuple(
                    ut19.Command(abs(x), 1 if x > 0 else -1) for x in code))
                limits = ut19.EncodingLimits(
                    max_commands=length, max_counters=labels,
                    max_memory_entries=200_000, max_seed_symbols=1_000_000,
                    max_seed_bits=19_000_000)
                compiled = ut19.encode_source(program, limits=limits)
                width = compiled.expanded_commands
                self.assertLessEqual(length+3, width)
                self.assertLess(width, 2*(length+3))
                ones = sum(sum(block.initial) for block in compiled.blocks)
                q = 1+4*(labels+1)+4*width*(labels+2)+3*ones
                self.assertEqual(compiled.seed_symbols, q)
                self.assertLessEqual(q, 1+4*(labels+1)+10*width*(labels+2))
                self.assertLess(q, 1+4*(labels+1)+20*(length+3)*(labels+2))
                state = compiled.cts_configuration(max_word_bits=19*q)
                self.assertEqual((len(state.word), state.word.count('1')), (19*q, q))
                stats = encoding.encoding_stats(ut19.compile_cts(), state.word)
                self.assertEqual(stats.initial_nodes, 16_529+306*q)

    def test_exact_butterfly_assignment_count(self):
        for power in range(1, 13):
            width = 1 << power
            count = 0
            stride = 1
            while stride < width:
                for _ in range(0, width, 2*stride):
                    count += stride
                stride *= 2
            self.assertEqual(count, (width//2)*power)


if __name__ == '__main__':
    unittest.main()
