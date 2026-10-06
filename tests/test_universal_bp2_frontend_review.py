"""Adversarial review checks for the written counter-machine/BP2 reduction.

The candidate's three compiler helpers are the systems under test. All step
semantics and expected boundaries below are independently implemented; no
candidate interpreter is called. These checks supplement the all-input proof
review in docs/universal-bp2-front-end-review.md, not replace it.
"""

from itertools import product
import random
import unittest
from unittest.mock import patch

import test_universal_bp2_frontend as candidate


def literal_step(code, registers, pc):
    """Precisely the numerical BP2 semantics, including zero -> 1/restart."""
    instruction = code[pc]
    position = abs(instruction) - 1
    if instruction > 0:
        registers[position] += 1
    elif registers[position] == 0:
        registers[position] = 1
        return 0
    else:
        registers[position] -= 1
    return pc + 1


def tail_action_step(registers, rules, action):
    position = abs(action) - 1
    if action > 0:
        registers[position] += 1
        return rules[position][0]
    if registers[position] == 1:
        return rules[position][2]
    registers[position] -= 1
    return rules[position][1]


def advance_to(code, registers, pc, target):
    """Find the next designated boundary or halt within a proven local bound."""
    for _ in range(3 * len(code) + 1):
        if pc == len(code):
            return pc
        pc = literal_step(code, registers, pc)
        if pc == target:
            return pc
    raise AssertionError('local BP2 pass failed to reach its next boundary')


def affine_constant(value, k):
    return (value,) + (0,) * k


def affine_add_constant(expression, value):
    return (expression[0] + value,) + expression[1:]


def symbolic_normal(counts, action, action_clocks):
    k = len(counts)
    vector = [tuple(2 * x for x in c) for c in counts]
    vector += [affine_constant(4, k)] * (3 * k + 1)
    vector[action_clocks[action]] = affine_constant(0, k)
    return vector


def row_then_elapse(vector, row, elapsed):
    return [affine_add_constant(x, change - elapsed)
            for x, change in zip(vector, row)]


class UniversalBP2FrontendReviewTests(unittest.TestCase):
    def test_all_two_callsite_chains_have_exact_syntax_step_counts(self):
        # 576 programs x 9 inputs x 2 entries = 10,368 distinct source macros.
        # Includes both zero/nonzero branches, shared registers, every target,
        # absent increment/decrement chains, and first/last selected chain cells.
        options = [('inc', i, target)
                   for i, target in product(range(2), range(3))]
        options += [('dec', i, yes, no)
                    for i, yes, no in product(range(2), range(3), range(3))]
        for left, right in product(options, repeat=2):
            program = [left, right, ('halt',)]
            for original in product((0, 1, 37), repeat=2):
                for state in (0, 1):
                    registers, rules, action, entries = candidate.amnesiac_compile(
                        program, original, state)
                    instruction = program[state]
                    kind, target_register, destination, *zero = instruction
                    expected = list(original)
                    chain_position = sum(p[0] == kind for p in program[:state])
                    if kind == 'inc':
                        expected[target_register] += 1
                        steps = chain_position + 3
                    else:
                        if expected[target_register]:
                            expected[target_register] -= 1
                        else:
                            destination = zero[0]
                        steps = 2 * chain_position + 8
                    for _ in range(steps):
                        self.assertNotEqual(action, 0)
                        action = tail_action_step(registers, rules, action)
                        self.assertGreaterEqual(min(registers), 1)
                    self.assertEqual(registers[:2], [x + 1 for x in expected])
                    self.assertTrue(all(x == 1 for x in registers[2:]))
                    self.assertEqual(action, entries[destination])

    def test_symbolic_waterfall_rows_preserve_unbounded_counter_parameters(self):
        # Affine coordinates carry independent unbounded natural parameters.
        # This checks identities rather than a collection of small input values.
        cases = 0
        for k in range(1, 5):
            actions = [0] + list(range(1, k + 1)) + list(range(-1, -k - 1, -1))
            for i in range(k):
                for successors in product(actions, repeat=3):
                    rules = [(0, 0, 0)] * k
                    rules[i] = successors
                    _, rows, halt, clocks = candidate.waterfall_compile(
                        [1] * k, rules, i + 1)
                    self.assertEqual(rows[halt], [0] * (4 * k + 1))
                    self.assertTrue(all(1 <= value <= 9
                                        for j, row in enumerate(rows) if j != halt
                                        for value in row))
                    for branch in ('increment', 'zero', 'positive'):
                        counts = []
                        for j in range(k):
                            expr = [1] + [0] * k
                            expr[j + 1] = 1
                            if j == i and branch == 'zero':
                                expr[j + 1] = 0
                            elif j == i and branch == 'positive':
                                expr[0] = 2
                            counts.append(tuple(expr))
                        old_action = i + 1 if branch == 'increment' else -i - 1
                        vector = symbolic_normal(counts, old_action, clocks)
                        elapsed = 6 if branch == 'positive' else 5
                        vector = row_then_elapse(vector, rows[clocks[old_action]], elapsed)
                        next_counts = list(counts)
                        if branch == 'increment':
                            next_counts[i] = affine_add_constant(counts[i], 1)
                            next_action = successors[0]
                        else:
                            intermediate = i if branch == 'zero' else 3 * k + 1 + i
                            self.assert_symbolic_unique_zero(vector, intermediate)
                            vector = row_then_elapse(vector, rows[intermediate], 5)
                            if branch == 'positive':
                                next_counts[i] = affine_add_constant(counts[i], -1)
                                next_action = successors[1]
                            else:
                                next_action = successors[2]
                        self.assertEqual(vector, symbolic_normal(next_counts, next_action, clocks))
                        self.assert_symbolic_unique_zero(vector, clocks[next_action])
                        cases += 1
        self.assertEqual(cases, 12_666)

    def assert_symbolic_unique_zero(self, vector, zero_index):
        for i, expression in enumerate(vector):
            if i == zero_index:
                self.assertTrue(all(x == 0 for x in expression))
            else:
                self.assertGreaterEqual(expression[0], 1)
                self.assertTrue(all(coefficient >= 0 for coefficient in expression[1:]))

    def test_exhaustive_small_bp2_stable_boundaries_and_zero_entries(self):
        # Every two-clock nonhalt row with entries <= 3 and positive diagonal.
        # Off-diagonal zeroes and diagonal 1 stress cancellation and compensation.
        cases = 0
        for halt in range(2):
            active = 1 - halt
            for initial in product(range(1, 4), repeat=2):
                if initial[0] == initial[1]:
                    continue
                for row in product(range(4), repeat=2):
                    if row[active] == 0:
                        continue
                    rows = [[0, 0], [0, 0]]
                    rows[active] = list(row)
                    self.check_bp2_boundaries(initial, rows, halt)
                    cases += 1
        self.assertEqual(cases, 144)

    def check_bp2_boundaries(self, initial, rows, halt):
        n = len(initial)
        code, count, _ = candidate.bp2_compile(list(initial), rows, halt)
        sweep = len(code) - (5 * n + 2)
        registers = [0] * count
        pc = advance_to(code, registers, 0, sweep)
        expected, marker = list(initial), 1
        visited = set()
        for _ in range(30):
            self.assertEqual(pc, sweep)
            self.assertEqual(registers, expected + [1] * n + [marker])
            state = tuple(registers)
            if state in visited:
                return  # Exact deterministic literal BP2 cycle, not timeout.
            visited.add(state)
            if marker == 2:
                pc = advance_to(code, registers, pc, sweep)
                self.assertEqual(pc, len(code))
                self.assertEqual(registers, [x - 1 for x in expected] + [1] * n + [0])
                return
            if expected.count(min(expected)) != 1:
                return  # The next Waterfall event violates the theorem's premise.
            winner = expected.index(min(expected))
            expected = [x - 1 for x in expected]
            if expected[winner] == 0:
                if winner == halt:
                    expected = [x + 2 for x in expected]
                    marker = 2
                else:
                    expected = [x + a for x, a in zip(expected, rows[winner])]
            pc = advance_to(code, registers, pc, sweep)

    def test_exact_compiler_size_is_syntax_only_even_for_infinite_sources(self):
        rng = random.Random(612_034)
        programs = [([('inc', 0, 0)], [0]),
                    ([('dec', 0, 0, 0)], [0]),
                    ([('halt',)], [0]),
                    ([('halt',), ('halt',)], [7])]
        for _ in range(40):
            d, length = rng.randrange(1, 5), rng.randrange(1, 9)
            program = []
            for _ in range(length):
                kind = rng.choice(('inc', 'dec', 'halt'))
                instruction = (kind,)
                if kind != 'halt':
                    instruction += (rng.randrange(d), rng.randrange(length))
                if kind == 'dec':
                    instruction += (rng.randrange(length),)
                program.append(instruction)
            programs.append((program, [rng.randrange(10) for _ in range(d)]))

        def forbidden(*args, **kwargs):
            raise AssertionError('compilation must not run an interpreter')

        with patch.object(candidate, 'source_step', forbidden), \
                patch.object(candidate, 'amnesiac_step', forbidden), \
                patch.object(candidate, 'waterfall_fire', forbidden), \
                patch.object(candidate, 'bp2_step', forbidden):
            for program, initial in programs:
                k = len(initial) + sum(p[0] == 'inc' for p in program)
                k += 4 * sum(p[0] == 'dec' for p in program)
                start = len(program) - 1
                values, rules, action, _ = candidate.amnesiac_compile(program, initial, start)
                clocks, rows, halt, _ = candidate.waterfall_compile(values, rules, action)
                code, count, prefix_length = candidate.bp2_compile(clocks, rows, halt)
                self.assertEqual(len(values), k)
                self.assertEqual(len(clocks), 4 * k + 1)
                self.assertEqual(count, 8 * k + 3)
                self.assertEqual(prefix_length, 4 * sum(initial) + 44 * k + 6)
                self.assertEqual(len(code), 168 * k * k + 124 * k + 19 + 4 * sum(initial))
                self.assertEqual(set(map(abs, code)), set(range(1, count + 1)))

    def test_marker_claims_need_boundary_qualification(self):
        # The complete source HALT with zero input is already a counterexample
        # to the original unqualified *intermediate-state* marker statements.
        # Section 5 now correctly restricts these claims to macro boundaries.
        values, rules, action, _ = candidate.amnesiac_compile([('halt',)], [0])
        clocks, rows, halt, _ = candidate.waterfall_compile(values, rules, action)
        code, count, initialization_end = candidate.bp2_compile(clocks, rows, halt)
        registers = [0] * count
        pc = advance_to(code, registers, 0, initialization_end)
        self.assertEqual(registers[-1], 1)
        self.assertTrue(all(x == 1 for x in registers[len(clocks):-1]))
        # No Waterfall zero test has yet been performed. Every trigger guard is
        # inactive, but Add(b_h) still temporarily raises m to 2.
        sweep = len(code) - (5 * len(clocks) + 2)
        saw_two = False
        while pc != sweep:
            pc = literal_step(code, registers, pc)
            saw_two |= registers[-1] == 2
        self.assertTrue(saw_two)
        self.assertEqual(registers[-1], 1)


if __name__ == '__main__':
    unittest.main()
