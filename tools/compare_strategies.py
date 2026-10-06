"""Compare standard selectors with the certified two-phase occurrence path."""
import json
from pathlib import Path

from s_only.queue_fixture import decode, encode
from s_only.reduction import contract_at, reduce, select_path
from s_only.terms import format_term, nodes
from s_only.traces import certificate, verify_certificate

ROOT = Path(__file__).resolve().parents[1]
STRATEGIES = ("normal", "applicative", "head")


def compare():
    fixture = json.loads((ROOT / "fixtures/queue_101_path.json").read_text())
    term = encode()
    agreement = {name: {"matching_choices": 0, "first_difference": None} for name in STRATEGIES}
    for index, step in enumerate(fixture["steps"], 1):
        recorded = tuple(map(int, step["path"]))
        for name, stats in agreement.items():
            selected = select_path(term, name)
            if selected == recorded:
                stats["matching_choices"] += 1
            elif stats["first_difference"] is None:
                stats["first_difference"] = {"contraction": index, "recorded_path": step["path"],
                    "strategy_path": None if selected is None else "".join(map(str, selected))}
        term = contract_at(term, recorded)
    runs = []
    for name in STRATEGIES:
        result = reduce(encode(), name, max_steps=100, max_nodes=100001)
        if verify_certificate(certificate(result)) != format_term(result.final):
            raise ValueError("independent strategy-certificate disagreement")
        term = result.initial
        observations = [{"contraction": 0, **decode(term)}]
        for index, path in enumerate(result.paths, 1):
            term = contract_at(term, path)
            observed = decode(term)
            if observed is not None:
                observations.append({"contraction": index, **observed})
        runs.append({"strategy": name, "steps": len(result.paths), "status": result.status,
                     "final_nodes": nodes(term), "observations": observations})
    return {"schema": "s-only-strategy-comparison-v1", "common_trajectory_steps": len(fixture["steps"]),
            "choices_on_common_trajectory": agreement,
            "separate_run_bounds": {"max_steps": 100, "max_nodes": 100001}, "separate_runs": runs}


if __name__ == "__main__":
    result = compare()
    (ROOT / "results/strategy_comparison.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
