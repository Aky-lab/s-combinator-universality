"""Native reachability certificates have an explicit, strategy-free scope."""
from copy import deepcopy
import hashlib
import unittest

from s_only.traces import verify_path_certificate


class PathTraceTests(unittest.TestCase):
    def setUp(self):
        self.data = {"schema": "s-only-path-v1", "initial_prefix": "AAASSSS",
                     "steps": [{"path": "", "nodes": 7,
                                "after_sha256": hashlib.sha256(b"AASSASS").hexdigest()}]}

    def test_one_native_step(self):
        self.assertEqual(verify_path_certificate(self.data), "((S S) (S S))")

    def test_empty_path_sequence_is_reflexive(self):
        self.assertEqual(verify_path_certificate({"schema": "s-only-path-v1",
                                                 "initial_prefix": "S", "steps": []}), "S")

    def test_no_strategy_or_termination_claim_can_be_smuggled_into_schema(self):
        for name, value in (("strategy", "normal"), ("status", "normal_form")):
            changed = deepcopy(self.data)
            changed[name] = value
            with self.assertRaises(ValueError):
                verify_path_certificate(changed)

    def test_tampered_digest_size_and_path(self):
        for key, value in (("after_sha256", "0"*64), ("nodes", 9), ("nodes", True),
                           ("path", "1"), ("path", "2"), ("path", 0)):
            changed = deepcopy(self.data)
            changed["steps"][0][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                verify_path_certificate(changed)

    def test_incomplete_schema_rejected(self):
        for key in self.data:
            changed = deepcopy(self.data)
            del changed[key]
            with self.subTest(key=key), self.assertRaises(ValueError):
                verify_path_certificate(changed)

    def test_nonredex_cannot_take_a_step(self):
        changed = deepcopy(self.data)
        changed["initial_prefix"] = "S"
        with self.assertRaises(ValueError):
            verify_path_certificate(changed)


if __name__ == "__main__":
    unittest.main()
