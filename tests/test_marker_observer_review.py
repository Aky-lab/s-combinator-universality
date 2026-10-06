"""Independent targeted review of the finite marker observer boundary.

The small substituted fragments test composition, rather than claiming a
second reconstruction of the priority workers. Actual compiler checks use
one program table at a time and independently assembled response trees.
"""
from contextlib import ExitStack
from dataclasses import fields
import gc
import unittest
from unittest.mock import patch

from s_only import marker_observer as observer
from s_only.cts import Program
from s_only.encoding import B, HALT, PI, compile_program
from s_only.probes import Configuration, Cursor, OBSERVATIONS
from s_only.program_selector_parts.compiler import CompilationLimit
from s_only.selector_parts.graph import Command
from s_only.terms import App, S


def app(*terms):
    result = terms[0]
    for term in terms[1:]:
        result = App(result, term)
    return result


def small_table(outcomes, directions=("L", "R", "R"), **budgets):
    """Compile actual observer composition with tiny root-guarded passes."""
    calls = []

    def fragment(name, succeeds, direction):
        def compile_fragment(builder, patterns, yes, no):
            calls.append(name)
            endpoint = builder.move(direction, yes if succeeds else no)
            wrong_origin = builder.uniform("false")
            return builder.incoming_test("root", endpoint, wrong_origin)
        return compile_fragment

    with ExitStack() as stack:
        stack.enter_context(patch(
            "s_only.program_selector_parts.patterns.PatternFamily",
            return_value=object()))
        for name, success, direction in zip(("fresh", "marked", "active"),
                                            outcomes, directions):
            module = "active" if name == "active" else "priority"
            stack.enter_context(patch(
                f"s_only.program_selector_parts.{module}.compile_{name}",
                fragment(name, success, direction)))
        table = observer.observer_table(Program(("",)), **budgets)
    return table, calls


def response(compiled, label, payload=S):
    """Assemble a completed dispatcher with labelled adjacent-pair trees.

    The test does not use generated patterns or precomputed selector routes.
    Unequal audit holes deliberately do not describe a valid source run.
    """
    audit = App(S, S)
    forest = [(App(B, action), index, None, None)
              for index, action in enumerate(compiled.action_terms)]
    while len(forest) > 1:
        following = []
        for index in range(0, len(forest) - 1, 2):
            left, right = forest[index:index + 2]
            code = App(B, app(S, left[0], right[0]))
            following.append((code, None, left, right))
        forest = following + (forest[-1:] if len(forest) % 2 else [])

    action = App(PI, S)
    phase, bit = divmod(label, 2)
    for _ in compiled.program.appendants[phase] if bit else "":
        action = App(action, App(S, S))

    def choose(node):
        if node[1] is not None:
            return app(S, audit, action) if node[1] == label else None
        left, right = node[2:]
        selected_left = choose(left)
        if selected_left is not None:
            return app(S, audit, App(selected_left, App(right[0], audit)))
        selected_right = choose(right)
        if selected_right is not None:
            return app(S, audit, App(App(left[0], audit), selected_right))
        return None

    return app(App(HALT, payload), choose(forest[0]),
               app(S, S, App(S, S)), App(S, S))


class MarkerObserverReviewTests(unittest.TestCase):
    def test_command_tokens_cannot_retain_mutable_or_custom_behavior(self):
        class MutableCommand:
            value = "false"

            def __eq__(self, other):
                return self.value == other

        class StringSubclass(str):
            pass

        for value in (MutableCommand(), StringSubclass("false"),
                      StringSubclass("stay")):
            terminal = not isinstance(value, str) or value == "false"
            with self.subTest(token=type(value).__name__), self.assertRaises(ValueError):
                observer.ObserverTable(((Command(value, None if terminal else 0),) * 6,), 0)

    def test_all_pass_outcomes_and_interpass_root_resets(self):
        marker = App(HALT, S)
        tree = App(S, marker)
        # A fresh success at L suppresses later marker-shaped successes.
        # A decline moves off-root before the next pass's root guard.
        for outcomes, expected, path in (
            ((True, True, True), False, (0,)),
            ((True, False, False), False, (0,)),
            ((False, True, True), True, (1,)),
            ((False, True, False), True, (1,)),
            ((False, False, True), True, (1,)),
            ((False, False, False), False, (1,)),
        ):
            with self.subTest(outcomes=outcomes):
                table, calls = small_table(outcomes)
                result = observer.execute(tree, table)
                self.assertIs(result.answer, expected)
                self.assertEqual(result.cursor.path, path)
                self.assertIs(result.cursor.root, tree)
                self.assertEqual(calls, ["active", "marked", "fresh"])

    def test_literal_code_is_exact_and_shape_probe_restores_both_exits(self):
        table, _ = small_table((False, False, True))
        # HALT is literal ((S S) ((S S) S)), with exactly five leaf sites.
        literal = App(App(S, S), App(App(S, S), S))
        self.assertEqual(literal, HALT)

        def replacements(term):
            if term is S:
                return [App(S, S)]
            return ([App(left, term.right) for left in replacements(term.left)]
                    + [App(term.left, right) for right in replacements(term.right)])

        payload = S
        for _ in range(1300):
            payload = App(payload, S)
        candidates = [(App(literal, payload), True), (literal, False), (S, False)]
        candidates.extend((App(code, payload), False) for code in replacements(literal))
        for candidate, expected in candidates:
            source = App(S, candidate)
            result = observer.execute(source, table)
            self.assertIs(result.answer, expected)
            self.assertEqual(result.cursor.path, (1,))
            self.assertIs(result.cursor.focus, candidate)
            self.assertIs(result.cursor.root, source)

    def test_read_only_machine_uses_no_origin_or_path_observation(self):
        table, _ = small_table((False, False, True))
        positive, negative = App(S, App(HALT, S)), App(S, S)

        def forbidden(*args, **kwargs):
            raise AssertionError("runtime accessed a nonlocal helper")

        targets = (
            "builtins.open", "pathlib.Path.read_text", "pathlib.Path.read_bytes",
            "hashlib.sha256", "s_only.encoding.compile_program",
            "s_only.cts.step", "s_only.cts.Machine.tick",
            "s_only.marker_observer.observer_table",
            "s_only.selector_parts.graph.GraphBuilder.match",
            "s_only.probes.compile_pattern", "s_only.probes.compile_rows",
            "s_only.terms.App.__eq__", "s_only.terms.App.__hash__",
        )
        with ExitStack() as stack:
            for target in targets:
                stack.enter_context(patch(target, forbidden))
            for property_name in ("root", "path"):
                stack.enter_context(patch.object(Cursor, property_name, property(forbidden)))
            for term, expected in ((positive, True), (negative, False),
                                   (positive, True), (negative, False)):
                result = observer.execute(term, table)
                self.assertIs(result.answer, expected)
        self.assertEqual([field.name for field in fields(table)], ["states", "start"])
        self.assertEqual([field.name for field in fields(Configuration)], ["control", "cursor"])

    def test_budget_validation_is_not_bypassed_by_prior_equal_values(self):
        _, _ = small_table((False, False, True), max_phases=1, max_appendant_bits=0)
        for name, value in (("max_phases", True), ("max_appendant_bits", False),
                            ("max_states", True)):
            with self.subTest(name=name), self.assertRaises(ValueError):
                small_table((False, False, True), **{name: value})
        with self.assertRaises(CompilationLimit):
            observer.observer_table(Program(("",) * 17))
        with self.assertRaises(CompilationLimit):
            observer.observer_table(Program(("1" * 129,)))

    def test_every_observation_of_terminal_states_is_absorbing(self):
        table = observer.ObserverTable(((Command("false"),) * 6,
                                       (Command("true"),) * 6), 0)
        tree = App(S, App(S, S))
        paths = ((), (0,), (1,), (1, 0), (1, 1))
        seen = set()
        for root, addresses in ((S, ((),)), (tree, paths)):
            for path in addresses:
                cursor = Cursor.at(root, path)
                seen.add((cursor.kind, cursor.incoming))
                for control in (0, 1):
                    state = Configuration(control, cursor)
                    self.assertIs(observer.step(table, state), state)
        # The first tree has no application entered from a left edge.
        for root, path in ((App(App(S, S), S), (0,)),):
            cursor = Cursor.at(root, path)
            seen.add((cursor.kind, cursor.incoming))
            for control in (0, 1):
                state = Configuration(control, cursor)
                self.assertIs(observer.step(table, state), state)
        self.assertEqual(seen, set(OBSERVATIONS))

    def test_actual_one_phase_observer_on_deep_registered_context(self):
        program = Program(("",))
        compiled = compile_program(program)
        payload = S
        for _ in range(1300):
            payload = App(S, payload)
        local = response(compiled, 0, payload)
        environment = App(S, app(S, compiled.act, App(S, S)))
        source = local
        for _ in range(1100):
            source = app(environment, S, source)
        table = observer.observer_table(program)
        self.assertEqual(len(table.states), 82125)
        for tree, expected in ((source, True), (App(HALT, payload), False),
                               (S, False), (source, True)):
            result = observer.execute(tree, table)
            self.assertIs(result.answer, expected)
            self.assertIs(result.cursor.root, tree)
            if expected:
                self.assertEqual(result.cursor.path, (1,) * 1100 + (0, 0, 0))
                self.assertIs(result.cursor.focus.right, payload)

    def test_actual_three_phase_observer_with_independent_holes_and_routes(self):
        program = Program(("", "01", "0"))
        compiled = compile_program(program)
        table = observer.observer_table(program, max_phases=None,
                                        max_appendant_bits=None)
        for label in range(6):
            term = response(compiled, label, App(S, S))
            result = observer.execute(term, table)
            self.assertIs(result.answer, True, label)
            self.assertEqual(result.cursor.path, (0, 0, 0))
            self.assertIs(result.cursor.root, term)
        del table
        gc.collect()


if __name__ == "__main__":
    unittest.main()
