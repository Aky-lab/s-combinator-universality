"""Independent finite checks of docs/universal-bp2-front-end.md.

Only Python's standard library is used. No repository compiler/evaluator is
imported. The mathematical chain/marker ideas are attributed to ais523's CC0
pages in the document; this reference implementation is written for this repo.
"""

from itertools import product
import unittest


def source_step(program, values, state):
    values = list(values)
    instruction = program[state]
    if instruction[0] == 'halt':
        return values, state
    _, i, next_state, *zero = instruction
    if instruction[0] == 'inc':
        values[i] += 1
    elif values[i]:
        values[i] -= 1
    else:
        next_state = zero[0]
    return values, next_state


def amnesiac_compile(program, values, start=0):
    """Action 0 is halt; signed i means change counter i-1."""
    initial = [v + 1 for v in values]
    triggers = [[0, 0, 0] for _ in initial]  # increment, success, failure
    entry = [0] * len(program)
    inc, dec = {}, {}

    def fresh():
        initial.append(1)
        triggers.append([0, 0, 0])
        return len(initial)

    for q, instruction in enumerate(program):
        if instruction[0] == 'inc':
            entry[q] = inc[q] = fresh()
        elif instruction[0] == 'dec':
            dec[q] = tuple(fresh() for _ in range(4))
            entry[q] = dec[q][0]

    inc_chain = list(inc.values())
    s_chain = [row[0] for row in dec.values()]
    f_chain = [row[1] for row in dec.values()]
    first_i = inc_chain[0] if inc_chain else 0
    first_s = s_chain[0] if s_chain else 0
    first_f = f_chain[0] if f_chain else 0
    for i in range(len(values)):
        triggers[i] = [-first_i, -first_s, -first_f]
    for j, (q, counter) in enumerate(inc.items()):
        _, i, t = program[q]
        nxt = inc_chain[j + 1] if j + 1 < len(inc_chain) else 0
        triggers[counter - 1] = [i + 1, entry[t], -nxt]
    for j, (q, (s, f, u, v)) in enumerate(dec.items()):
        _, i, yes, no = program[q]
        next_s = s_chain[j + 1] if j + 1 < len(s_chain) else 0
        next_f = f_chain[j + 1] if j + 1 < len(f_chain) else 0
        triggers[s - 1] = [f, -v, -next_s]
        triggers[f - 1] = [-(i + 1), -u, -next_f]
        triggers[u - 1] = [-first_f, entry[yes], v]
        triggers[v - 1] = [-first_s, entry[no], u]
    return initial, triggers, entry[start], entry


def amnesiac_step(values, triggers, action):
    values = list(values)
    if action == 0:
        return values, 0
    i = abs(action) - 1
    if action > 0:
        values[i] += 1
        action = triggers[i][0]
    elif values[i] > 1:
        values[i] -= 1
        action = triggers[i][1]
    else:
        action = triggers[i][2]
    return values, action


def waterfall_compile(values, triggers, action):
    k = len(values)
    actions = list(range(1, k + 1)) + list(range(-1, -k - 1, -1)) + [0]
    q = {a: k + j for j, a in enumerate(actions)}
    t = [3 * k + 1 + i for i in range(k)]
    n = 4 * k + 1
    rows = [[0] * n for _ in range(n)]

    def row_at(clock, terms, base=0):
        row = [base] * n
        for target, amount in terms:
            row[target] += amount
        rows[clock] = [x + 5 for x in row]

    for i, (p, s, f) in enumerate(triggers):
        row_at(q[i + 1], [(i, 2), (q[i + 1], 4), (q[p], -4)])
        row_at(q[-i - 1], [(i, -2), (q[-i - 1], 4), (t[i], -3)])
        row_at(i, [(i, 2), (t[i], 3), (q[f], -4)])
        row_at(t[i], [(t[i], 3), (q[s], -4)], base=1)
    initial = normal_vector(values, action, q)  # zero event -> positive start
    return [x + 1 for x in initial], rows, q[0], q


def normal_vector(values, action, q):
    vector = [2 * x for x in values] + [4] * (3 * len(values) + 1)
    vector[q[action]] = 0
    return vector


def waterfall_event(values):
    minimum = min(values)
    if values.count(minimum) != 1:
        raise AssertionError('a Waterfall tie was reached')
    return values.index(minimum), [x - minimum for x in values]


def waterfall_fire(values, rows, halt):
    if min(values) <= 0:
        raise AssertionError('post-trigger clocks must be positive')
    i, zeroed = waterfall_event(values)
    if i == halt:
        return None, zeroed
    return [x + a for x, a in zip(zeroed, rows[i])], zeroed


def add_block(amounts, sign):
    return [sign * (i + 1) for i, amount in enumerate(amounts)
            for _ in range(amount)]


def initializer(amounts, marker):
    return add_block(amounts, 1) + [-marker, marker] + add_block(amounts, -1)


def bp2_compile(values, rows, halt):
    n = len(values)
    m = 2 * n + 1
    init = initializer(values + [1] * n + [0], m)
    code = list(init)
    for i in range(n):
        if i == halt:
            amounts = [2 - int(i == j) for j in range(n)] + [0] * n + [1]
        else:
            amounts = [rows[i][j] - int(i == j) for j in range(n)]
            amounts += [0] * (n + 1)
        if min(amounts) < 0:
            raise AssertionError('trigger compensation cannot be negative')
        z = n + i + 1
        code += add_block(amounts, 1) + [-z, z] + add_block(amounts, -1)
    code += [-j for j in range(1, n + 1)]
    for i in range(n):
        v, z = i + 1, n + i + 1
        code += [-z, -v, v, z]
    code += [-m, -m]
    return code, m, len(init)


def bp2_step(code, values, pc):
    command = code[pc]
    i = abs(command) - 1
    if command > 0:
        values[i] += 1
        return pc + 1
    if values[i] > 0:
        values[i] -= 1
        return pc + 1
    values[i] = 1
    return 0


def bp2_run(code, counters, initial=None, max_steps=10_000_000):
    values = [0] * counters if initial is None else list(initial)
    pc = 0
    for steps in range(max_steps):
        if pc == len(code):
            return values, steps
        pc = bp2_step(code, values, pc)
    raise AssertionError('finite fixture exceeded explicit BP2 step budget')


class UniversalBP2FrontendTests(unittest.TestCase):
    def test_naive_increment_prefix_changes_nonhalt_to_halt(self):
        # Initialized source [-1, -1], value 1: a two-step exact cycle.
        values, pc = [1], 0
        for _ in range(2):
            pc = bp2_step([-1, -1], values, pc)
        self.assertEqual((pc, values), (0, [1]))
        # The tempting all-zero compilation [+1, -1, -1] instead halts.
        result, steps = bp2_run([1, -1, -1], 1)
        self.assertEqual((result, steps), ([0], 6))
        # The guarded initializer preserves the exact source cycle.
        init = initializer([1, 0], 2)
        code = init + [-1, -1]
        values, pc, checkpoints = [0, 0], 0, []
        for _ in range(30):
            if pc == len(init):
                checkpoints.append(tuple(values))
                if len(checkpoints) == 2:
                    break
            pc = bp2_step(code, values, pc)
        self.assertEqual(checkpoints, [(1, 1), (1, 1)])

    def test_initializer_exhaustive_small_vectors(self):
        for amounts in product(range(3), repeat=3):
            code = initializer(list(amounts) + [0], 4)
            actual, _ = bp2_run(code, 4)
            self.assertEqual(actual, list(amounts) + [1])
            for working in product(range(3), repeat=3):
                for marker in (1, 2):
                    initial = list(working) + [marker]
                    actual, _ = bp2_run(code, 4, initial)
                    self.assertEqual(actual, initial)

    def test_chain_macros_shared_registers_and_both_branches(self):
        source = [('inc', 0, 1), ('dec', 0, 2, 3), ('inc', 1, 4),
                  ('dec', 1, 5, 6), ('dec', 0, 0, 6), ('inc', 0, 3),
                  ('halt',)]
        for original in product(range(3), repeat=2):
            for state in range(6):
                values, rules, action, entry = amnesiac_compile(source, original, state)
                expected, successor = source_step(source, original, state)
                for _ in range(100):
                    values, action = amnesiac_step(values, rules, action)
                    self.assertGreaterEqual(min(values), 1)
                    if action in entry and all(x == 1 for x in values[2:]):
                        break
                else:
                    self.fail('chain macro did not restore its boundary')
                self.assertEqual(action, entry[successor])
                self.assertEqual(values[:2], [x + 1 for x in expected])

    def test_waterfall_all_small_successor_and_branch_cases(self):
        targets = (0, 1, 2, -1, -2)
        for p, s, f in product(targets, repeat=3):
            rules = [(p, s, f), (f, p, s)]
            for values in product(range(1, 4), repeat=2):
                for action in (1, 2, -1, -2):
                    w, rows, halt, q = waterfall_compile(values, rules, action)
                    self.assertEqual(rows[halt], [0] * len(w))
                    self.assertTrue(all(1 <= a <= 9 for i, row in enumerate(rows)
                                        if i != halt for a in row))
                    expected_values, expected_action = amnesiac_step(values, rules, action)
                    first, first_zeroed = waterfall_event(w)
                    self.assertEqual(first, q[action])
                    self.assertEqual(first_zeroed, normal_vector(values, action, q))
                    w, _ = waterfall_fire(w, rows, halt)
                    if action < 0:
                        i = -action - 1
                        winner, _ = waterfall_event(w)
                        self.assertEqual(winner, i if values[i] == 1 else 7 + i)
                        w, _ = waterfall_fire(w, rows, halt)
                    winner, normalized = waterfall_event(w)
                    self.assertEqual(winner, q[expected_action])
                    self.assertEqual(normalized, normal_vector(expected_values, expected_action, q))

    def test_bp2_immediate_halt_output_all_positions(self):
        for n in (1, 2, 3):
            for h in range(n):
                for other in product((1, 2, 3), repeat=n - 1):
                    y = list(other)
                    y.insert(h, 0)
                    initial = [v + 1 for v in y]
                    rows = [[1] * n for _ in range(n)]
                    rows[h] = [0] * n
                    code, counters, _ = bp2_compile(initial, rows, h)
                    result, _ = bp2_run(code, counters)
                    self.assertEqual(result, [v + 1 for v in y] + [1] * n + [0])
                    self.assertEqual(set(map(abs, code)), set(range(1, counters + 1)))

    def test_bp2_nonhalt_trigger_then_halt_and_diagonal_correction(self):
        for initial, rows, halt, expected in (
            ([1, 2], [[4, 0], [0, 0]], 1, [4, 1]),
            ([2, 1], [[0, 0], [0, 4]], 0, [1, 4]),
        ):
            code, counters, _ = bp2_compile(initial, rows, halt)
            result, _ = bp2_run(code, counters)
            self.assertEqual(result, expected + [1, 1, 0])

    def test_literal_closed_nonhalting_cycle(self):
        code, counters, boundary = bp2_compile([1, 2], [[1, 1], [0, 0]], 1)
        values, pc, first = [0] * counters, 0, None
        for step in range(10_000):
            self.assertNotEqual(pc, len(code))
            if pc == boundary:
                configuration = pc, tuple(values)
                if first is None:
                    first = configuration
                elif configuration == first:
                    self.assertEqual(values, [1, 2, 1, 1, 1])
                    self.assertGreater(step, 0)
                    return
            pc = bp2_step(code, values, pc)
        self.fail('expected exact deterministic BP2 cycle was not found')

    def test_end_to_end_standard_counter_inputs_and_fixed_output(self):
        cases = [
            ([('halt',)], (0,)),
            ([('halt',)], (3,)),
            ([('inc', 0, 1), ('halt',)], (0,)),
            ([('inc', 0, 1), ('halt',)], (3,)),
            ([('dec', 0, 1, 1), ('halt',)], (0,)),
            ([('dec', 0, 1, 1), ('halt',)], (1,)),
            ([('dec', 0, 1, 1), ('halt',)], (3,)),
            ([('dec', 1, 1, 2), ('inc', 0, 0), ('halt',)], (2, 2)),
        ]
        for source, original in cases:
            with self.subTest(source=source, input=original):
                expected, state = list(original), 0
                for _ in range(100):
                    if source[state][0] == 'halt':
                        break
                    expected, state = source_step(source, expected, state)
                else:
                    self.fail('source fixture failed to halt')
                a, rules, entry, _ = amnesiac_compile(source, original)
                w, rows, halt, _ = waterfall_compile(a, rules, entry)
                code, counters, _ = bp2_compile(w, rows, halt)
                result, _ = bp2_run(code, counters)
                self.assertEqual(result[0], 2 * expected[0] + 3)
                self.assertEqual((result[0] - 3) // 2, expected[0])
                self.assertEqual(result[-1], 0)
                self.assertTrue(code)
                self.assertEqual(set(map(abs, code)), set(range(1, counters + 1)))


if __name__ == '__main__':
    unittest.main()
