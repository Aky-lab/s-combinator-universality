"""Portable certificates and a prefix-string checker independent of the reducer.

Verification never imports production terms, redex detection, contraction or
strategy selection. It operates on serialized binary trees and byte ranges.
SHA-256 fields are integrity checks, not a substitute for replaying each rewrite.
"""
import hashlib


def _digest(source):
    return hashlib.sha256(source.encode("ascii")).hexdigest()


def _spans(source):
    if not isinstance(source, str) or not source:
        raise ValueError("a prefix tree must be a nonempty string")
    end = [0] * len(source)
    for i in range(len(source) - 1, -1, -1):
        if source[i] == "S":
            end[i] = i + 1
        elif source[i] == "A":
            left = i + 1
            if left >= len(source) or end[left] >= len(source):
                raise ValueError("incomplete application")
            end[i] = end[end[left]]
        else:
            raise ValueError("prefix trees contain only A and S")
    if end[0] != len(source):
        raise ValueError("trailing prefix tokens")
    return end


def _choose(source, end, strategy):
    if strategy == "head":
        i, path = 0, ""
        while source[i] == "A":
            if source.startswith("AAAS", i):
                return path
            i += 1
            path += "0"
        return None
    stack = [(0, "", False)]
    while stack:
        i, path, visited = stack.pop()
        if source[i] == "S":
            continue
        if strategy == "normal" or visited:
            if source.startswith("AAAS", i):
                return path
        if not visited:
            left, right = i + 1, end[i + 1]
            if strategy == "applicative":
                stack.append((i, path, True))
            stack.extend([(right, path + "1", False), (left, path + "0", False)])
    return None


def _rewrite(source, end, path):
    if not isinstance(path, str) or any(c not in "01" for c in path):
        raise ValueError("a path must contain only 0 and 1")
    i = 0
    for direction in path:
        if source[i] != "A":
            raise ValueError("path leaves the tree")
        i = i + 1 if direction == "0" else end[i + 1]
    if not source.startswith("AAAS", i):
        raise ValueError("path does not identify an S redex")
    x0 = i + 4
    y0 = end[x0]
    z0 = end[y0]
    x, y, z = source[x0:y0], source[y0:z0], source[z0:end[i]]
    return source[:i] + "AA" + x + z + "A" + y + z + source[end[i]:]


def _display(source, end):
    output, stack = [], [0]
    while stack:
        item = stack.pop()
        if isinstance(item, str):
            output.append(item)
        elif source[item] == "S":
            output.append("S")
        else:
            stack.extend([")", end[item + 1], " ", item + 1, "("])
    return "".join(output)


def certificate(result):
    """Serialize a production Reduction. Always run verify_certificate too."""
    from .terms import prefix
    from .reduction import contract_at
    current = result.initial
    records = []
    for path in result.paths:
        current = contract_at(current, path)
        serial = prefix(current)
        records.append({"path": "".join(map(str, path)),
                        "after_sha256": _digest(serial), "nodes": len(serial)})
    return {"schema": "s-only-trace-v1", "initial_prefix": prefix(result.initial),
            "final_prefix": prefix(result.final), "strategy": result.strategy,
            "max_steps": result.max_steps, "max_nodes": result.max_nodes,
            "status": result.status, "steps": records}


def verify_certificate(data):
    """Check every native step, selector choice, size and stopping condition.

    Return the final fully parenthesized term, or raise ValueError. Normal-form
    and head-normal-form observations precede the step limit at a boundary.
    """
    required = {"schema", "initial_prefix", "final_prefix", "strategy", "max_steps",
                "max_nodes", "status", "steps"}
    if not isinstance(data, dict) or set(data) != required or data["schema"] != "s-only-trace-v1":
        raise ValueError("invalid trace schema")
    strategy, max_steps, max_nodes = data["strategy"], data["max_steps"], data["max_nodes"]
    if strategy not in ("normal", "applicative", "head"):
        raise ValueError("invalid strategy")
    if type(max_steps) is not int or max_steps < 0 or type(max_nodes) is not int or max_nodes < 1:
        raise ValueError("invalid resource bounds")
    if not isinstance(data["steps"], list) or len(data["steps"]) > max_steps:
        raise ValueError("invalid step count")
    current = data["initial_prefix"]
    end = _spans(current)
    for ordinal, record in enumerate(data["steps"]):
        if not isinstance(record, dict) or set(record) != {"path", "after_sha256", "nodes"}:
            raise ValueError(f"invalid record {ordinal}")
        if len(current) > max_nodes:
            raise ValueError("step starts outside node budget")
        selected = _choose(current, end, strategy)
        if selected is None or record["path"] != selected:
            raise ValueError(f"strategy mismatch at step {ordinal}")
        current = _rewrite(current, end, record["path"])
        end = _spans(current)
        if len(current) > max_nodes:
            raise ValueError("step exceeds node budget")
        if type(record["nodes"]) is not int or record["nodes"] != len(current):
            raise ValueError(f"node count mismatch at step {ordinal}")
        if record["after_sha256"] != _digest(current):
            raise ValueError(f"digest mismatch at step {ordinal}")
    if current != data["final_prefix"]:
        raise ValueError("final tree mismatch")
    selected = _choose(current, end, strategy)
    if len(current) > max_nodes:
        expected_status = "node_limit"
    elif selected is None:
        expected_status = "normal_form" if _choose(current, end, "normal") is None else "head_normal_form"
    elif len(data["steps"]) == max_steps:
        expected_status = "step_limit"
    elif len(_rewrite(current, end, selected)) > max_nodes:
        expected_status = "node_limit"
    else:
        raise ValueError("trace stopped before a resource or terminal boundary")
    if data["status"] != expected_status:
        raise ValueError("stopping status mismatch")
    return _display(current, end)
