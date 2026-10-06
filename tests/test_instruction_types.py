"""Instruction payloads cannot smuggle mutable comparison behavior into graphs."""
import unittest

from s_only.probes import Instruction, ProbeTable
from s_only.root_selector import SelectorTable
from s_only.selector_parts.graph import Command


class MutableName:
    def __init__(self, value):
        self.value = value

    def __eq__(self, other):
        return self.value == other


class StringSubclass(str):
    pass


class InstructionTypeTests(unittest.TestCase):
    def test_both_instruction_types_require_plain_strings(self):
        for constructor, valid in ((Instruction, 'false'), (Command, 'normal')):
            for invalid in (MutableName(valid), StringSubclass(valid), None, 0, True):
                with self.subTest(constructor=constructor, invalid=type(invalid)), \
                     self.assertRaisesRegex(ValueError, 'plain string'):
                    constructor(invalid)

    def test_rejection_does_not_invoke_custom_comparison(self):
        class Trap:
            def __eq__(self, other):
                raise AssertionError('payload equality was invoked')

        for constructor in (Instruction, Command):
            with self.assertRaisesRegex(ValueError, 'plain string'):
                constructor(Trap())

    def test_valid_terminal_graphs_keep_their_meaning(self):
        probe = ProbeTable(((Instruction('false'),) * 6,
                            (Instruction('true'),) * 6), 0)
        self.assertIs(probe.answer(0), False)
        self.assertIs(probe.answer(1), True)
        selector = SelectorTable(((Command('normal'),) * 6,
                                  (Command('contracted'),) * 6), 0)
        self.assertEqual(selector.status(0), 'normal')
        self.assertEqual(selector.status(1), 'contracted')


if __name__ == '__main__':
    unittest.main()
