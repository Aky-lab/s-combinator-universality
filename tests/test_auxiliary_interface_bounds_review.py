"""Independent boundary checks for the auxiliary-interface bound review.

Only syntax is compiled. All evaluator entry points used by the source
fixtures are disabled while compiling; no source or S trajectory is run.
"""

from contextlib import ExitStack, contextmanager
import unittest
from unittest.mock import patch

from s_only import encoding, s_event_readout, ut19
from s_only.terms import App, S
from test_universal_bp2_frontend import (
    amnesiac_compile, waterfall_compile, bp2_compile,
)


@contextmanager
def no_evaluation():
    forbidden = (
        "test_universal_bp2_frontend.source_step",
        "test_universal_bp2_frontend.amnesiac_step",
        "test_universal_bp2_frontend.waterfall_event",
        "test_universal_bp2_frontend.waterfall_fire",
        "test_universal_bp2_frontend.bp2_step",
        "test_universal_bp2_frontend.bp2_run",
        "s_only.ut19.source_step", "s_only.ut19.initial_source",
        "s_only.alternating_tag.step", "s_only.alternating_tag.evaluate",
        "s_only.cts.step", "s_only.cts.Machine",
        "s_only.reduction.contract_at", "s_only.reduction.reduce",
    )
    with ExitStack() as stack:
        for name in forbidden:
            stack.enter_context(patch(name, side_effect=AssertionError(name)))
        yield


def unfold_count(term):
    """Count occurrences from edges, independently of cached term sizes."""
    counts, pending = {}, [(term, False)]
    while pending:
        node, leaving = pending.pop()
        identity = id(node)
        if identity in counts:
            continue
        if type(node) is type(S):
            counts[identity] = 1
        elif leaving:
            counts[identity] = 1 + counts[id(node.left)] + counts[id(node.right)]
        else:
            pending.extend(((node, True), (node.right, False), (node.left, False)))
    return counts[id(term)], len(counts)


def direct_desired(program, position, expanded):
    """Read the finite memory-column specification without a source step."""
    counters = max(command.counter for command in program.commands)
    first, last = position == 1, position == counters + 2
    pairs = [(int(last), 0)]
    for command in program.commands:
        adjacent = position in (command.counter, command.counter + 1)
        if command.delta > 0:
            pairs.append((0, int(adjacent != (first != last))))
        else:
            pairs.append((int(first or last), int(adjacent)))
    pairs += [(int(first or last), int(position == counters + 1)), (0, 0)]
    pairs += [(int(first or last), 0)] * (expanded - len(pairs))
    return tuple(bit for pair in pairs for bit in pair)


def direct_subset_xor(bits):
    """Quadratic finite definition, distinct from the production butterfly."""
    return tuple(sum(bits[j] for j in range(len(bits)) if j & i == i) % 2
                 for i in range(len(bits)))


class AuxiliaryInterfaceBoundsReviewTests(unittest.TestCase):
    def test_frontend_dimensions_include_decrements_and_unused_registers(self):
        with no_evaluation():
            for registers in range(1, 5):
                for increments in range(4):
                    for decrements in range(3):
                        source = tuple([("inc", 0, 0)] * increments
                                       + [("dec", registers - 1, 0, 0)] * decrements
                                       + [("halt",)])
                        values = tuple(range(registers))
                        with self.subTest(d=registers, i=increments, j=decrements):
                            initial, triggers, action, _ = amnesiac_compile(source, values)
                            clocks, rows, halt, _ = waterfall_compile(initial, triggers, action)
                            code, labels, _ = bp2_compile(clocks, rows, halt)
                            k = registers + increments + 4 * decrements
                            n = 4 * k + 1
                            self.assertEqual(len(initial), k)
                            self.assertEqual(len(clocks), n)
                            self.assertEqual(sum(clocks), 2 * sum(values) + 18 * k + 1)
                            self.assertEqual(labels, 8 * k + 3)
                            self.assertEqual(len(code), 168 * k * k + 124 * k + 19
                                             + 4 * sum(values))
                            self.assertEqual(set(map(abs, code)), set(range(1, labels + 1)))

    def test_ut19_power_boundaries_and_seed_formula_from_subset_definition(self):
        with no_evaluation():
            for length in (1, 4, 5, 6, 12, 13, 14, 28, 29, 30):
                count = min(3, length)
                program = ut19.SourceProgram(tuple(
                    ut19.Command(1 + i % count, 1 if i % 2 else -1)
                    for i in range(length)))
                compiled = ut19.encode_source(program)
                expanded = 1
                while expanded < length + 3:
                    expanded *= 2
                self.assertEqual(compiled.expanded_commands, expanded)
                self.assertLess(expanded, 2 * (length + 3))
                ones = 0
                for position, block in enumerate(compiled.blocks, 1):
                    desired = direct_desired(program, position, expanded)
                    transformed = direct_subset_xor(desired)
                    self.assertEqual(block.desired, desired)
                    self.assertEqual(block.initial, transformed)
                    ones += sum(transformed)
                expected = 1 + 4 * (count + 1) + 4 * expanded * (count + 2) + 3 * ones
                self.assertEqual(len(compiled.queue), expected)
                self.assertLessEqual(ones, 2 * expanded * (count + 2))
                self.assertLess(expected, 1 + 4 * (count + 1)
                                + 20 * (length + 3) * (count + 2))

    def test_literal_initial_tree_count_and_one_hot_dimensions(self):
        with no_evaluation():
            fixed = ut19.compile_cts()
            self.assertEqual((len(fixed.appendants), sum(map(len, fixed.appendants)),
                              sum(word.count("1") for word in fixed.appendants)),
                             (38, 760, 40))
            for length in (1, 5, 6):
                program = ut19.SourceProgram(tuple(ut19.Command(1, 1)
                                                    for _ in range(length)))
                compiled = ut19.encode_source(program)
                q = len(compiled.queue)
                state = compiled.cts_configuration(max_word_bits=19 * q)
                self.assertEqual((len(state.word), state.word.count("1")), (19 * q, q))
                term = encoding.encode(fixed, state.word)
                occurrences, _ = unfold_count(term)
                self.assertEqual(occurrences, 16_529 + 306 * q)

    def test_binary_size_envelope_includes_worst_allowed_parameters(self):
        for bits in (*range(1, 65), 127, 256, 1024):
            # These maxima are deliberately simultaneous overestimates of an
            # explicit description, making the numerical implication stronger.
            k = 5 * bits
            s = bits * (1 << bits)
            length = 168 * k * k + 124 * k + 19 + 4 * s
            envelope = 8192 * (bits + 1) ** 2 * (1 << bits)
            self.assertLessEqual(length, envelope)
            self.assertLessEqual(8 * k + 3, 40 * bits + 3)

    def test_readout_cost_uses_current_dag_not_exponential_unfolding(self):
        # These constructors are independently spelled in the existing reader
        # fixture; the shell remains fabricated syntax, not an execution claim.
        from test_s_event_readout import base, hot, local, small_event, spec, word
        program = ut19.compile_cts()
        tree = spec(program)
        bits = hot(small_event())[17:]
        payload = base(tree, word(bits[1:]))
        diamond = S
        for _ in range(80):
            diamond = App(diamond, diamond)
        term = local(program, tree, S, payload, (17, 1), opaque=diamond)
        occurrences, nodes = unfold_count(term)
        self.assertGreater(occurrences, 1 << 80)
        self.assertLess(nodes, 10_000)
        limits = s_event_readout.limits_for_input_nodes(nodes)
        with no_evaluation(), patch("s_only.ut19.encode_source",
                                    side_effect=AssertionError("source compilation")):
            result = s_event_readout.read_ut19_event(term, limits=limits)
        self.assertEqual(result.values, (0,))
        self.assertEqual(result.input_nodes, nodes)
        self.assertLessEqual(result.work, s_event_readout.polynomial_work_bound(nodes))


if __name__ == "__main__":
    unittest.main()
