"""Reproduce the bounded census and checked closed-term examples.

Run from the repository root: python -m tools.baseline
"""
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path

from s_only import App, S, format_term, nodes, parse, reduce
from s_only.traces import certificate, verify_certificate


@lru_cache(maxsize=None)
def trees(leaves):
    if leaves == 1:
        return (S,)
    return tuple(App(left, right) for split in range(1, leaves)
                 for left in trees(split) for right in trees(leaves - split))


def build():
    rows = []
    for size in range(1, 9):
        for strategy in ("normal", "applicative", "head"):
            counts = Counter()
            most_steps = largest = 0
            for tree in trees(size):
                result = reduce(tree, strategy, max_steps=100, max_nodes=10001)
                counts[result.status] += 1
                most_steps = max(most_steps, len(result.paths))
                largest = max(largest, nodes(result.final))
            rows.append({"leaves": size, "strategy": strategy, "terms": len(trees(size)),
                         "outcomes": dict(sorted(counts.items())),
                         "max_steps_observed": most_steps, "max_final_nodes": largest})
    examples = [
        ("fork_atom", "S S S S", "normal", 20),
        ("fork_pair", "S S S (S S)", "normal", 20),
        ("two_stage_fork", "S (S S) S S", "normal", 20),
        ("inner_normal", "S (S S S S)", "normal", 20),
        ("inner_head", "S (S S S S)", "head", 20),
        ("growing_carrier", "S S S (S S S) (S S S)", "normal", 12),
    ]
    summaries = []
    for name, source, strategy, steps in examples:
        result = reduce(parse(source), strategy, max_steps=steps, max_nodes=10001)
        data = certificate(result)
        assert verify_certificate(data) == format_term(result.final)
        Path(f"examples/{name}.json").write_text(json.dumps(data, indent=2) + "\n")
        summaries.append({"name": name, "source": source, "strategy": strategy,
                          "steps": len(result.paths), "status": result.status,
                          "initial_nodes": nodes(result.initial), "final_nodes": nodes(result.final)})
    return {"schema": "s-only-baseline-v1", "bounds": {"max_leaves": 8,
            "max_steps": 100, "max_nodes": 10001}, "census": rows, "examples": summaries}


if __name__ == "__main__":
    output = build()
    Path("results/baseline.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))
