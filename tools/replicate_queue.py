"""Reproduce the pinned two-phase queue fixture using native S contractions.

Run: python -m tools.replicate_queue
"""
import hashlib
import json
from pathlib import Path

from s_only.queue_fixture import decode, encode, source_config
from s_only.reduction import contract_at
from s_only.terms import format_term, nodes, prefix
from s_only.traces import verify_path_certificate

ROOT = Path(__file__).resolve().parents[1]


def replay():
    data = json.loads((ROOT / "fixtures/queue_101_path.json").read_text())
    final_display = verify_path_certificate(data)
    term = encode()
    if prefix(term) != data["initial_prefix"]:
        raise ValueError("independent initial construction differs from fixture")
    observations, rejected = [], []

    def inspect(index):
        observation = decode(term)
        if observation is None:
            rejected.append(index)
            return
        if observation != source_config(observation["horizon"]):
            raise ValueError(f"source readout mismatch at sample {index}")
        observations.append({"contraction": index, **observation, "nodes": nodes(term)})

    inspect(0)
    for index, record in enumerate(data["steps"], 1):
        term = contract_at(term, tuple(map(int, record["path"])))
        serialized = prefix(term)
        if nodes(term) != record["nodes"]:
            raise ValueError(f"object-tree size mismatch at sample {index}")
        if hashlib.sha256(serialized.encode("ascii")).hexdigest() != record["after_sha256"]:
            raise ValueError(f"object-tree digest mismatch at sample {index}")
        inspect(index)
    if format_term(term) != final_display:
        raise ValueError("independent final tree disagreement")
    expected = [
        {"contraction": 0, "horizon": 0, "phase": 0, "data": "101", "nodes": 171},
        {"contraction": 22, "horizon": 1, "phase": 1, "data": "011", "nodes": 17057},
        {"contraction": 85, "horizon": 2, "phase": 0, "data": "11", "nodes": 339285},
    ]
    if observations != expected:
        raise ValueError("checkpoint set differs from published fixture")
    return {"schema": "s-only-queue-replication-v1", "native_contractions": len(data["steps"]),
            "sample_decisions_checked": len(data["steps"]) + 1,
            "initial_nodes": len(data["initial_prefix"]), "final_nodes": nodes(term),
            "checkpoints": observations, "rejected_samples": rejected,
            "final_prefix_sha256": hashlib.sha256(prefix(term).encode("ascii")).hexdigest(),
            "source_commit": "85a867988442fc423279341200f81634a1e65582",
            "path_scope": "published occurrence schedule; selector address choice is a separate audit"}


if __name__ == "__main__":
    result = replay()
    (ROOT / "results/queue_101_replication.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
