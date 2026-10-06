"""Measure the specialized finite fuel table and its local fixture coverage."""
import json
from pathlib import Path

from s_only.fuel_probe import fuel_rows, fuel_table
from s_only.probes import Configuration, Cursor, step
from s_only.queue_fixture import encode
from s_only.reduction import contract_at

ROOT = Path(__file__).resolve().parents[1]


def report():
    table = fuel_table()
    static_bound = table.tick_bound
    data = json.loads((ROOT / "fixtures/queue_101_path.json").read_text())
    term = encode()
    found = []
    for index, record in enumerate(data["steps"], 1):
        target = tuple(map(int, record["path"]))
        candidates = [target] + ([target[:-1]] if target and target[-1] == 0 else [])
        for origin in candidates:
            state = Configuration(table.start, Cursor.at(term, origin))
            ticks = 0
            while table.answer(state.control) is None:
                state = step(table, state)
                ticks += 1
                if ticks > static_bound:
                    raise ValueError("static finite-table bound violated")
            if table.answer(state.control) and state.cursor.path == target:
                found.append({"contraction": index, "origin": "".join(map(str, origin)),
                              "selected": record["path"], "microticks": ticks})
                break
        term = contract_at(term, target)
    return {"schema": "s-only-fuel-probe-v1", "pattern_rows": len(fuel_rows()),
            "finite_control_states": len(table.states), "observations_per_state": 6,
            "static_microtick_bound": static_bound, "matching_local_occurrences": len(found),
            "max_microticks_among_matches": max(row["microticks"] for row in found),
            "coverage": found,
            "scope": "local fuel selection from the supplied occurrence; active-context discovery is separate"}


if __name__ == "__main__":
    result = report()
    (ROOT / "results/fuel_probe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
