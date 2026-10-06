"""Small complete source domains checked by an independent literal tag loop."""
from collections import deque
from itertools import groupby, product
import unittest

from s_only.ut19 import encode_source, parse_source


# Published one-based production table, independent of the executable constant.
ROWS = ((2, 3), (4, 4), (18, 4), (1, 1, 19), (7, 9), (8, 9),
        (10, 10), (11, 10), (18, 10), (5, 6), (6, 5, 19),
        (14, 14, 14, 14), (15,), (16, 16), (16, 17),
        (12, 13), (12, 12, 12, 12), (18,), ())


def source_outcome(commands, counters):
    pc, values, visited = 0, [0] * counters, set()
    for _ in range(100):
        if pc == len(commands):
            return True, tuple(values)
        configuration = pc, tuple(values)
        if configuration in visited:
            return False, tuple(values)
        visited.add(configuration)
        operation, label = commands[pc][0], int(commands[pc][1:]) - 1
        if operation == '+':
            values[label] += 1
            pc += 1
        elif values[label]:
            values[label] -= 1
            pc += 1
        else:
            values[label] = 1
            pc = 0
    return None, tuple(values)


class UT19FrontendReviewTests(unittest.TestCase):
    def check_closed_case(self, commands, counter_count):
        halt, values = source_outcome(commands, counter_count)
        self.assertIsNotNone(halt)
        encoded = encode_source(parse_source(' '.join(commands)))
        queue, take, visited = deque(encoded.queue), True, {}
        for step in range(60_000):
            self.assertTrue(queue)
            configuration = tuple(queue), take
            if configuration in visited:
                self.assertFalse(halt)
                self.assertLess(visited[configuration], step)
                return False
            visited[configuration] = step
            if take and queue[0] == 18:
                self.assertTrue(halt)
                runs = tuple(len(tuple(items)) for symbol, items in groupby(queue)
                             if symbol == 16)
                self.assertEqual(runs, tuple(4 ** (value + 1) for value in values))
                # At the first event the entire queue is still in Reset grammar.
                self.assertLessEqual(set(queue), {4, 10, 11, 16, 18})
                return True
            head = queue.popleft()
            queue.extend(ROWS[head - 1] if take else ())
            take = not take
            self.assertLess(len(queue), 10_000)
        self.fail('literal tag fixture exceeded its explicit microstep cap')

    def test_all_one_counter_programs_through_four_commands(self):
        outcomes = [self.check_closed_case(commands, 1)
                    for length in range(1, 5)
                    for commands in product(('+1', '-1'), repeat=length)]
        self.assertEqual((len(outcomes), sum(outcomes)), (30, 21))

    def test_two_counter_halts_and_closed_cycles_through_three_commands(self):
        outcomes, unclassified = [], []
        for length in (2, 3):
            for commands in product(('+1', '-1', '+2', '-2'), repeat=length):
                if {command[1:] for command in commands} != {'1', '2'}:
                    continue
                halt, _ = source_outcome(commands, 2)
                if halt is None:
                    unclassified.append(' '.join(commands))
                else:
                    outcomes.append(self.check_closed_case(commands, 2))
        self.assertEqual((len(outcomes), sum(outcomes)), (52, 44))
        # These source prefixes grow a different counter on every restart.
        # This test makes no tag-trajectory assertion for the four excluded cases.
        self.assertEqual(set(unclassified), {'+1 -2 -2', '-1 +2 -1',
                                             '+2 -1 -1', '-2 +1 -2'})


if __name__ == '__main__':
    unittest.main()
