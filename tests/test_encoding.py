"""Independent constructor, unfolding, order, sharing and inspection checks."""
from contextlib import redirect_stderr, redirect_stdout
from hashlib import sha256
from io import StringIO
import itertools
import json
from pathlib import Path
import random
import tempfile
import unittest
from unittest.mock import patch

from s_only.cts import Program
from s_only import encoding as enc
from s_only.terms import App, S, leaves, nodes, prefix
from tools.inspect_cts_encoding import inspect, main


ROOT = Path(__file__).resolve().parents[1]


def reference_program(appendants, word):
    """Tuple-only formula expansion, no production constructor or size cache."""
    s = "S"

    def app(*parts):
        result = parts[0]
        for child in parts[1:]:
            result = (result, child)
        return result

    b = app(s, s)
    zero = app(s, b, b)
    pi = app(s, b)
    live = (app(b, app(s, zero)), app(b, app(s, app(s, zero))))
    forest = []
    for word_to_append in appendants:
        routine = pi
        for bit in word_to_append[::-1]:
            routine = app(s, app(s, routine), live[int(bit)])
        forest.extend((app(b, pi), app(b, routine)))
    # A queue of level-tagged trees is a separate construction of the same
    # bottom-up layout: merge adjacent equal levels, then join residual blocks.
    blocks = []
    for tree in forest:
        blocks.append((0, tree))
        while len(blocks) > 1 and blocks[-1][0] == blocks[-2][0]:
            depth, right = blocks.pop()
            _, left = blocks.pop()
            blocks.append((depth + 1, app(b, app(s, left, right))))
    actions = blocks[-1][1]
    for _, tree in reversed(blocks[:-1]):
        actions = app(b, app(s, tree, actions))
    encoded_word = s
    for bit in word:
        encoded_word = app(live[int(bit)], encoded_word)
    halt = app(b, app(b, s))
    act = app(s, halt, actions)
    seed = app(s, encoded_word)
    environment = app(s, app(s, act, seed))
    return app(zero, zero, environment)


def reference_prefix(term):
    result = []
    pending = [term]
    while pending:
        item = pending.pop()
        if isinstance(item, tuple):
            result.append("A")
            pending.extend((item[1], item[0]))
        else:
            if item != "S":
                raise AssertionError("not a closed reference term")
            result.append("S")
    return "".join(result)


def read_routine(term):
    """Read the emitted order from literal outer Push constructors."""
    bits = []
    while term is not enc.PI:
        if not isinstance(term, App) or not isinstance(term.left, App):
            raise AssertionError("malformed appender")
        head, suspended = term.left.left, term.left.right
        if head is not S or not isinstance(suspended, App) or suspended.left is not S:
            raise AssertionError("malformed Push")
        bit = next((i for i, value in enumerate(enc.LIVE) if value is term.right), None)
        if bit is None:
            raise AssertionError("not a live bit prefix")
        bits.append(str(bit))
        term = suspended.right
    return "".join(bits)


def dispatcher_leaves(term):
    """Read the mathematical Leaf/Node grammar, preserving occurrence order."""
    result = []
    depths = []
    pending = [(term, 0)]
    while pending:
        item, depth = pending.pop()
        if not isinstance(item, App) or item.left is not enc.B:
            raise AssertionError("missing b prefix")
        payload = item.right
        # All actions are PI or S(S N)J. A Node payload is S L R with L=bF,
        # so the closed left argument's head separates the constructor roles.
        if (isinstance(payload, App) and isinstance(payload.left, App)
                and payload.left.left is S and isinstance(payload.left.right, App)
                and payload.left.right.left is enc.B):
            pending.extend(((payload.right, depth + 1),
                            (payload.left.right, depth + 1)))
        else:
            result.append(read_routine(payload))
            depths.append(depth)
    return result, depths


class EncodingTests(unittest.TestCase):
    def test_two_phase_fixture_is_byte_for_byte_identical(self):
        expected = json.loads((ROOT / "fixtures/queue_101_path.json").read_text())["initial_prefix"]
        result = enc.encode(Program(("1", "")), "101")
        self.assertEqual(prefix(result), expected)
        self.assertEqual(nodes(result), 171)
        self.assertEqual(enc.prefix_sha256(result, max_nodes=171),
                         sha256(expected.encode("ascii")).hexdigest())

    def test_literal_constants(self):
        self.assertEqual([nodes(term) for term in
                          (enc.B, enc.C0, enc.PI, *enc.VALUES, *enc.LIVE, enc.HALT)],
                         [3, 9, 5, 11, 13, 15, 17, 9])

    def test_empty_word_and_all_empty_appendants_are_valid(self):
        for p in (1, 2, 3, 5, 10):
            program = Program(("",) * p)
            term = enc.encode(program, "")
            self.assertEqual(nodes(term), 33 + 32 * p)
            self.assertEqual(prefix(term), reference_prefix(reference_program(program.appendants, "")))
        self.assertIs(enc.encode_word(""), S)
        self.assertIs(enc.append_routine(""), enc.PI)

    def test_empty_program_and_invalid_source_words_are_rejected(self):
        for words in ((), [], ("2",), (None,), (True,), ("01 1",), ("１",)):
            with self.subTest(appendants=words), self.assertRaises(ValueError):
                Program(words)
        for word in (None, 0, 1, True, b"01", (0, 1), [0, 1], "2", "0 1", "01\n", "１"):
            for function in (enc.encode_word, enc.append_routine):
                with self.subTest(function=function.__name__, word=word), self.assertRaises(ValueError):
                    function(word)
            with self.assertRaises(ValueError):
                enc.encode(Program(("",)), word)
        for bad in (None, (), ("",), [""], "01"):
            with self.assertRaises(TypeError):
                enc.compile_program(bad)

    def test_word_logical_front_is_innermost(self):
        term = enc.encode_word("00101")
        outer_to_inner = []
        while term is not S:
            self.assertIsInstance(term, App)
            outer_to_inner.append("1" if term.left is enc.LIVE[1] else "0")
            self.assertIn(term.left, enc.LIVE)
            term = term.right
        self.assertEqual("".join(reversed(outer_to_inner)), "00101")

    def test_append_routine_emits_forward_order(self):
        for length in range(6):
            for bits in itertools.product("01", repeat=length):
                word = "".join(bits)
                self.assertEqual(read_routine(enc.append_routine(word)), word)

    def test_small_appenders_execute_in_forward_order_with_native_s_steps(self):
        # This is only a bounded appender identity check, not a CTS controller.
        from s_only.reduction import contract_at
        for word in ("", "0", "1", "01", "10", "0011", "1010"):
            term = App(enc.append_routine(word), enc.encode_word("10"))
            for emitted in range(len(word)):
                path = (0,) * emitted
                term = contract_at(term, path)
                term = contract_at(term, path)
            # Each Push leaves one retained history application outside the
            # remaining active appender call. Remove exactly those wrappers.
            for _ in word:
                self.assertIsInstance(term, App)
                term = term.left
            self.assertIs(term.left, enc.PI)
            self.assertEqual(prefix(term.right), prefix(enc.encode_word("10" + word)))

    def test_phase_major_actions_and_non_power_of_two_layout(self):
        for p in (1, 2, 3, 5, 6, 7, 9, 17, 31):
            appendants = tuple(format(j, "b") for j in range(p))
            program = Program(appendants)
            compiled = enc.compile_program(program)
            expected_order = [value for word in appendants for value in ("", word)]
            self.assertEqual([read_routine(action) for action in compiled.action_terms], expected_order)
            emitted, depths = dispatcher_leaves(compiled.actions)
            self.assertEqual(emitted, expected_order)
            self.assertEqual(len(depths), 2 * p)
            self.assertEqual(max(depths), (2 * p - 1).bit_length())
            term = compiled.encode("1010")
            self.assertEqual(prefix(term), reference_prefix(reference_program(appendants, "1010")))
        # Six leaves: pairRound gives ((00,01),(10,11)) on the left and (20,21)
        # on the right. Midpoint splitting would instead produce 3+3 leaves.
        _, depths = dispatcher_leaves(enc.compile_program(Program(("0", "1", "01"))).actions)
        self.assertEqual(depths, [3, 3, 3, 3, 2, 2])

    def test_symbolic_counts_agree_with_independent_unfolding(self):
        rng = random.Random(9371)
        for _ in range(100):
            appendants = tuple("".join(rng.choices("01", k=rng.randrange(9)))
                               for _ in range(rng.randrange(1, 12)))
            word = "".join(rng.choices("01", k=rng.randrange(20)))
            program = Program(appendants)
            stats = enc.encoding_stats(program, word)
            term = enc.encode(program, word)
            serial = reference_prefix(reference_program(appendants, word))
            self.assertEqual(prefix(term), serial)
            self.assertEqual(stats.initial_nodes, len(serial))
            self.assertEqual(nodes(term), len(serial))
            self.assertEqual(stats.initial_s_leaves, serial.count("S"))
            self.assertEqual(leaves(term), serial.count("S"))
            self.assertEqual(stats.initial_nodes, 33 + 32 * len(appendants)
                             + 20 * sum(map(len, appendants))
                             + 2 * sum(a.count("1") for a in appendants)
                             + 16 * len(word) + 2 * word.count("1"))

    def test_all_reachable_objects_are_immutable_closed_s_syntax(self):
        from dataclasses import FrozenInstanceError
        term = enc.encode(Program(("01", "", "10")), "0101")
        seen = set()
        stack = [term]
        while stack:
            item = stack.pop()
            if id(item) in seen:
                continue
            seen.add(id(item))
            if isinstance(item, App):
                stack.extend((item.left, item.right))
            else:
                self.assertIs(item, S)
        self.assertEqual(len(seen), enc.unique_objects(term))
        with self.assertRaises(FrozenInstanceError):
            term.left = S

    def test_identical_actions_and_suffixes_share_by_identity(self):
        compiled = enc.compile_program(Program(("10101", "10101", "0101", "1", "")))
        self.assertIs(compiled.action_terms[1], compiled.action_terms[3])
        # The continuation after the first Push of 10101 is exactly 0101.
        self.assertIs(compiled.action_terms[1].left.right.right, compiled.action_terms[5])
        self.assertIs(compiled.action_terms[-1], enc.PI)
        for action in compiled.action_terms[::2]:
            self.assertIs(action, enc.PI)
        first, second = compiled.encode("01"), compiled.encode("11")
        self.assertIs(first.right.right.left.right, compiled.act)
        self.assertIs(second.right.right.left.right, compiled.act)

    def test_large_repeated_appendants_keep_unfolded_semantics(self):
        program = Program(("01" * 500,) * 257)
        term = enc.encode(program, "")
        self.assertEqual(nodes(term), 33 + 32 * 257 + 21 * 257_000)
        self.assertLess(enc.unique_objects(term), 3200)
        self.assertGreater(nodes(term), 5_000_000)
        # Term hashes/equality would recurse through the 1000-bit routines.
        self.assertEqual(enc.encoding_stats(program, "").initial_nodes, nodes(term))

    def test_symbolic_inspection_does_not_build_terms(self):
        with patch("s_only.encoding.App", side_effect=AssertionError("term allocated")), \
             patch("tools.inspect_cts_encoding.encode", side_effect=AssertionError("term constructed")):
            result = inspect(Program(("01",) * 3000), "1" * 1000)
        self.assertFalse(result["constructed"])
        self.assertNotIn("unique_objects", result)
        self.assertEqual(result["unique_appendant_count"], 1)


class PrefixStreamingTests(unittest.TestCase):
    def test_small_and_deep_streams_match_existing_prefix(self):
        for term in (S, enc.encode(Program(("0", "11", "")), "001"),
                     enc.encode(Program(("01" * 1200,)), "10" * 1500)):
            expected = prefix(term).encode("ascii")
            for chunk_size in (1, 17, 65536):
                chunks = list(enc.iter_prefix_chunks(term, max_nodes=nodes(term), chunk_size=chunk_size))
                self.assertEqual(b"".join(chunks), expected)
                self.assertTrue(all(0 < len(chunk) <= chunk_size for chunk in chunks))
                self.assertEqual(enc.prefix_sha256(term, max_nodes=nodes(term), chunk_size=chunk_size),
                                 sha256(expected).hexdigest())

    def test_limits_reject_before_any_streamed_byte(self):
        term = enc.encode(Program(("1", "")), "101")
        generator = enc.iter_prefix_chunks(term, max_nodes=170)
        with self.assertRaises(enc.EncodingLimit):
            next(generator)
        for bound in (True, -1, 1.0, None):
            with self.assertRaises(ValueError):
                enc.prefix_sha256(term, max_nodes=bound)
        for chunk in (True, 0, -1, 1.0, None):
            with self.assertRaises(ValueError):
                enc.prefix_sha256(term, max_nodes=171, chunk_size=chunk)
        for bad in (None, "S", (S, S)):
            with self.assertRaises(TypeError):
                enc.prefix_sha256(bad, max_nodes=171)
            with self.assertRaises(TypeError):
                enc.unique_objects(bad)

    def test_hashing_does_not_use_complete_prefix(self):
        with patch("s_only.terms.prefix", side_effect=AssertionError("whole string allocated")):
            result = inspect(Program(("1", "")), "101", with_sha256=True)
        self.assertEqual(result["initial_prefix_sha256"],
                         "3c66d04a273dd1e8401995ae114be5e8bbacaae1dd936a4d6dd169ffa60d60be")


class InspectionCliTests(unittest.TestCase):
    def invoke(self, *args):
        stream = StringIO()
        with redirect_stdout(stream):
            result = main(list(args))
        self.assertEqual(json.loads(stream.getvalue()), result)
        return result

    def rejected(self, *args):
        with redirect_stderr(StringIO()), self.assertRaises(SystemExit) as error:
            main(list(args))
        self.assertEqual(error.exception.code, 2)

    def test_default_fixture_and_empty_word(self):
        result = self.invoke("--sha256")
        self.assertEqual(result["initial_nodes"], 171)
        self.assertTrue(result["constructed"])
        self.assertEqual(self.invoke("--word", "")["source_data_bits"], 0)

    def test_json_document_array_and_seed_file(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            program = folder / "program.json"
            seed = folder / "seed.txt"
            seed.write_text("101\n", encoding="ascii")
            for document in (["1", ""], {"appendants": ["1", ""], "phase_count": 2}):
                program.write_text(json.dumps(document), encoding="ascii")
                result = self.invoke("--program", str(program), "--word-file", str(seed), "--sha256")
                self.assertEqual(result["initial_nodes"], 171)
            self.rejected("--program", str(program))
            seed.write_text("101\n\n", encoding="ascii")
            self.rejected("--program", str(program), "--word-file", str(seed))
            for document in ([], {}, {"appendants": "01"}, {"appendants": [1]}, ["2"]):
                program.write_text(json.dumps(document), encoding="ascii")
                self.rejected("--program", str(program), "--word", "")

    def test_resource_caps(self):
        self.rejected("--max-source-bits", "3")
        self.rejected("--max-phases", "1")
        self.rejected("--max-nodes", "170", "--build")
        self.rejected("--max-nodes", "170", "--sha256")
        self.rejected("--max-source-bits", "-1")
        self.assertEqual(self.invoke("--max-nodes", "0")["initial_nodes"], 171)
        with patch("tools.inspect_cts_encoding.encode", side_effect=AssertionError("constructed")):
            with self.assertRaises(enc.EncodingLimit):
                inspect(Program(("1", "")), "101", build=True, max_nodes=170)
        with tempfile.TemporaryDirectory() as folder:
            program = Path(folder) / "program.json"
            program.write_text('["01"]', encoding="ascii")
            self.rejected("--program", str(program), "--word", "", "--max-input-bytes", "3")
            program.write_bytes(b"\xff")
            self.rejected("--program", str(program), "--word", "")


if __name__ == "__main__":
    unittest.main()
