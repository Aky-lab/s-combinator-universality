"""Independent regular-language oracle for current-configuration readout."""
from itertools import product
import re
import unittest

from s_only import alternating_tag as tag
from s_only import cts
from s_only.ut19_readout import read_cts_result, read_tag_result


SYMBOLS = {'a': 17, 'b': 9, 'c': 3, 'd': 10, 'e': 15}
LANGUAGE = re.compile(r'(?:(?:ab(?:ac)?)+e+)+(?:ab(?:ac)?)+(?:[bd]b(?:cc)?)+\Z')


def expected(word):
    if LANGUAGE.fullmatch(word) is None:
        raise ValueError
    result = []
    for run in re.findall('e+', word):
        count, value = len(run), -1
        while count > 1 and count % 4 == 0:
            count //= 4
            value += 1
        if count != 1 or value < 0:
            raise ValueError
        result.append(value)
    return tuple(result)


class UT19ReadoutReviewTests(unittest.TestCase):
    def compare(self, word):
        queue = tuple(SYMBOLS[letter] for letter in word)
        state = tag.Configuration(queue)
        try:
            result = expected(word)
        except ValueError:
            with self.assertRaises(ValueError):
                read_tag_result(state)
            return
        self.assertEqual(read_tag_result(state), result)
        full = ''.join(''.join(str(int(i == symbol)) for i in range(19))
                       for symbol in queue)
        current = cts.Configuration(full[17:], 17)
        self.assertEqual(read_cts_result(current), result)

    def test_mutation_closure_against_independent_regex_and_integer_division(self):
        bases = ('ab' + 'e' * 4 + 'abbb',
                 'abacab' + 'e' * 16 + 'ab' + 'e' * 4 + 'abac' + 'dbccbb')
        cases = set(bases)
        for word in bases:
            for index in range(len(word)):
                cases.add(word[:index] + word[index + 1:])
                for letter in SYMBOLS:
                    cases.add(word[:index] + letter + word[index + 1:])
            for index in range(len(word) + 1):
                for letter in SYMBOLS:
                    cases.add(word[:index] + letter + word[index:])
        for word in sorted(cases):
            with self.subTest(word=word):
                self.compare(word)
        self.assertGreater(len(cases), 300)

    def test_no_short_reset_word_is_misread_as_an_output(self):
        for length in range(7):
            for letters in product(SYMBOLS, repeat=length):
                self.compare(''.join(letters))


if __name__ == '__main__':
    unittest.main()
