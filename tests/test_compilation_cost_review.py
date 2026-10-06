"""Independent bounded review of scalar costs, row shells, and source identity.

The large-fixture oracle builds only a tiny tree of integer summaries. It never
constructs that fixture's S terms, patterns, or finite controller.
"""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from s_only import encoding
from s_only.compilation_cost import compilation_cost, dispatcher_leaf_depths
from s_only.cts import Program
from s_only.neary_fixture import canonical_json, compile_fixture
from s_only.probes import HOLE, compile_pattern, compile_rows
from s_only.program_selector_parts.patterns import (
    PatternFamily, call_pattern, chosen_pattern,
)
from s_only.selector_parts.graph import GraphBuilder
from tools.compilation_cost_report import main


ROOT = Path(__file__).resolve().parents[1]


def real_matcher_cost(pattern):
    """Allocate a small actual matcher, including then removing its terminals."""
    return len(compile_pattern(pattern).states) - 2


def paired_scalar_tree(words):
    """Independent level-wise oracle, retaining costs but no term syntax."""
    forest = []
    for phase, word in enumerate(words):
        forest.extend(((29, (phase, 0)),
                       (29 + sum(70 + 7 * (bit == '1') for bit in word),
                        (phase, 1))))
    while len(forest) > 1:
        following = []
        for index in range(0, len(forest) - 1, 2):
            left, right = forest[index:index + 2]
            following.append((27 + left[0] + right[0], left, right))
        if len(forest) % 2:
            following.append(forest[-1])
        forest = following
    return forest[0]


def scalar_phase_oracle(words):
    """Add each literal sibling and emitted row, without closed-form sums."""
    tree = paired_scalar_tree(words)
    pending = [(tree, 0, 0)]
    leaves = {}
    while pending:
        node, depth, dormant = pending.pop()
        if len(node) == 2:
            leaves[node[1]] = depth, dormant
        else:
            _, left, right = node
            pending.extend(((right, depth + 1, dormant + left[0]),
                            (left, depth + 1, dormant + right[0])))
    phases = []
    for phase, word in enumerate(words):
        depth, dormant = leaves[(phase, 1)]
        shell, base_address = 72 + 13 + 25 * depth + dormant, 4 + 2 * depth
        matcher = address = rows = 0
        if word:
            remaining = sum(70 + 7 * (bit == '1') for bit in word)
            matcher += shell + 21 + remaining
            address += base_address
            rows += 1
            for position, bit in enumerate(word):
                remaining -= 70 + 7 * (bit == '1')
                matcher += shell + 90 + remaining + 7 * (bit == '1') + 6 * position
                address += base_address + position
                rows += 1
                if position + 1 < len(word):
                    matcher += shell + 27 + remaining + 6 * position
                    address += base_address + position + 1
                    rows += 1
        phases.append((depth, dormant, rows, matcher, address))
    return tree[0], phases


class CompilationCostReviewTests(unittest.TestCase):
    def test_individual_shell_and_live_row_constants(self):
        family = PatternFamily(Program(('',)), required_period=None)
        self.assertEqual(real_matcher_cost(family.local_pattern('fresh')), 72)
        self.assertEqual(real_matcher_cost(chosen_pattern(HOLE)), 13)
        for length in range(5):
            for bits in itertools.product('01', repeat=length):
                word = ''.join(bits)
                self.assertEqual(real_matcher_cost(call_pattern(encoding.append_routine(word))),
                                 21 + 70 * length + 7 * word.count('1'))
                rows = iter(family.appender_rows(word))
                for position, bit in enumerate(word):
                    rest = word[position + 1:]
                    pattern, address = next(rows)
                    self.assertEqual(real_matcher_cost(pattern),
                                     90 + 70 * len(rest) + 7 * (rest.count('1') + int(bit))
                                     + 6 * position)
                    self.assertEqual(address, (0,) * position)
                    if rest:
                        pattern, address = next(rows)
                        self.assertEqual(real_matcher_cost(pattern),
                                         27 + 70 * len(rest) + 7 * rest.count('1')
                                         + 6 * position)
                        self.assertEqual(address, (0,) * (position + 1))
                # In particular, no extra next-call row after the last Push.
                self.assertEqual(tuple(rows), ())

    def test_scalar_oracle_and_actual_rows_for_small_programs(self):
        cases = list(itertools.product(('', '0', '1'), repeat=3))
        cases.extend((('1010',), ('01', '', '10', '01', ''),
                      ('', '11', '', '0', '', '11', '')))
        for words in cases:
            family = PatternFamily(Program(words), required_period=None)
            stats = compilation_cost(family.program)
            whole, phases = scalar_phase_oracle(words)
            self.assertEqual(stats.dispatcher_matcher_states, whole)
            for expected, actual in zip(phases, stats.phases):
                self.assertEqual(expected, (actual.route_depth,
                                 actual.dormant_literal_matcher_states_per_row,
                                 actual.selected_rows, actual.selected_action_matcher_states,
                                 actual.selected_action_address_states))
            # Allocate at most one small selected-row table at a time.
            rows = family.selected_action_rows()
            actual_matchers = sum(real_matcher_cost(pattern) for pattern, _ in rows)
            actual_addresses = sum(len(address) for _, address in rows)
            self.assertEqual(actual_matchers, stats.selected_action_matcher_states)
            self.assertEqual(actual_addresses, stats.selected_action_address_states)
            self.assertEqual(len(compile_rows(rows).states) - 2,
                             stats.selected_action_embedded_states)

    def test_embedding_omits_both_terminals_but_does_not_merge_rows(self):
        pattern = ((HOLE, HOLE), HOLE)
        row = pattern, (0, 1)
        for repetitions in range(4):
            builder = GraphBuilder()
            continuation = builder.uniform('normal')
            before = len(builder.states)
            # Even equal yes/no destinations and duplicate row objects do not
            # license the current embed operation to eliminate emitted states.
            builder.rows((row,) * repetitions, continuation, continuation)
            self.assertEqual(len(builder.states) - before, repetitions * 14)

    def test_odd_carry_depths_against_levelwise_integer_oracle(self):
        for count in range(1, 130):
            forest = [(index,) for index in range(count)]
            expected = [0] * count
            while len(forest) > 1:
                following = []
                for index in range(0, len(forest) - 1, 2):
                    merged = forest[index] + forest[index + 1]
                    for leaf in merged:
                        expected[leaf] += 1
                    following.append(merged)
                if len(forest) % 2:
                    following.append(forest[-1])
                forest = following
            self.assertEqual(dispatcher_leaf_depths(count), tuple(expected))

    def test_large_fixture_scalar_oracle_and_source_bytes(self):
        path = ROOT / 'artifacts/neary-left-toggle/program.json'
        raw = path.read_bytes()
        document = json.loads(raw)
        manifest = json.loads((path.parent / 'manifest.json').read_text())
        expected_file = manifest['files']['program.json']
        self.assertEqual(len(raw), expected_file['bytes'])
        self.assertEqual(sha256(raw).hexdigest(), expected_file['sha256'])
        # Regenerate source CTS data only; do not execute CTS or construct S.
        self.assertEqual(raw, canonical_json(compile_fixture().program_document()).encode('ascii'))
        self.assertEqual(document['source_pages'], '65-75')
        self.assertEqual(document['phase_count'], len(document['appendants']))
        self.assertEqual(len(document['provenance']), len(document['appendants']))
        total, phases = scalar_phase_oracle(document['appendants'])
        self.assertEqual(total, 4_510_017)
        self.assertEqual(sum(item[2] for item in phases), 127_288)
        self.assertEqual(sum(item[1] * item[2] for item in phases), 568_498_572_096)
        self.assertEqual(sum(item[3] for item in phases), 571_551_887_060)
        self.assertEqual(sum(item[4] for item in phases), 42_514_486)
        self.assertEqual(sum(item[3] + item[4] for item in phases), 571_594_401_546)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'report.json'
            main(['--program', str(path), '--output', str(output)])
            self.assertEqual(output.read_bytes(),
                             (ROOT / 'results/neary_compilation_cost.json').read_bytes())
            result = json.loads(output.read_bytes())
            self.assertEqual(result['program_file_sha256'], expected_file['sha256'])

    def test_static_report_has_no_construction_dependencies(self):
        # Run in a fresh process. The package public API imports terms/reduction,
        # so allow that baseline, then reject App allocation and all compiler
        # dependencies before importing the static-analysis/report modules.
        script = r'''
import builtins
import json
import sys
import s_only
import s_only.terms as terms
def forbidden_app(*args, **kwargs):
    raise AssertionError('term construction forbidden')
terms.App = forbidden_app
s_only.App = forbidden_app
original = builtins.__import__
forbidden = ('encoding', 'probes', 'terms', 'program_selector_parts', 'selector_parts')
def checked(name, *args, **kwargs):
    if any(part in forbidden for part in name.split('.')):
        raise AssertionError('construction module imported: ' + name)
    return original(name, *args, **kwargs)
builtins.__import__ = checked
from tools.compilation_cost_report import main
main(['--program', sys.argv[1]])
'''
        result = subprocess.run([sys.executable, '-c', script,
                                 str(ROOT / 'artifacts/neary-left-toggle/program.json')],
                                cwd=ROOT, capture_output=True, text=True, timeout=15, check=True)
        self.assertEqual(json.loads(result.stdout)['selected_action_embedded_states'],
                         571_594_401_546)

    def test_exact_cli_limits_accept_the_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'program.json'
            raw = b'{"appendants": ["", "10", "10"]}'
            path.write_bytes(raw)
            with redirect_stdout(StringIO()):
                result = main(['--program', str(path), '--max-input-bytes', str(len(raw)),
                               '--max-phases', '3', '--max-appendant-bits', '4'])
            self.assertEqual(result['selected_action_rows'], 8)
            self.assertEqual(result['unique_appendant_count'], 2)
            path.write_bytes(b'[""]')
            with redirect_stdout(StringIO()):
                result = main(['--program', str(path), '--max-appendant-bits', '0'])
            self.assertEqual(result['selected_action_embedded_states'], 0)


if __name__ == '__main__':
    unittest.main()
