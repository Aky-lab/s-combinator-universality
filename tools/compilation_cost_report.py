"""Report pre-quotient controller bounds without constructing code or tables."""
import argparse
from collections import Counter
from dataclasses import asdict
from hashlib import sha256
import json
from pathlib import Path

from s_only.compilation_cost import compilation_cost, dispatcher_leaf_depths
from s_only.cts import Program


SOURCE_COMMIT = "85a867988442fc423279341200f81634a1e65582"


def report(program: Program, *, include_phases: bool = False) -> dict:
    stats = compilation_cost(program)
    result = asdict(stats)
    if include_phases:
        result["phases"] = list(result["phases"])
    else:
        del result["phases"]
    result.update(
        schema="s-only-compilation-cost-v1",
        source_commit=SOURCE_COMMIT,
        analysis="independent cost derivation for current Python literal inlining",
        dispatcher_layout="bottom-up-adjacent-pairs-no-padding",
        leaf_depth_histogram={str(depth): count for depth, count in sorted(
            Counter(dispatcher_leaf_depths(2 * stats.phase_count)).items())},
        full_controller_state_lower_bound=stats.selected_action_embedded_states,
        constructed_terms=False,
        constructed_patterns=False,
        constructed_controller=False,
        scope="pre-quotient state allocation for successful current-compiler materialization; "
              "exact selected-action component only; no memory-byte or runtime estimate")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--program", required=True, type=Path,
                        help="JSON array of appendants, or object containing that array")
    parser.add_argument("--output", type=Path, help="write deterministic JSON instead of stdout")
    parser.add_argument("--include-phases", action="store_true")
    parser.add_argument("--max-input-bytes", type=int, default=2_000_000)
    parser.add_argument("--max-phases", type=int, default=10_000)
    parser.add_argument("--max-appendant-bits", type=int, default=1_000_000)
    args = parser.parse_args(argv)
    try:
        for name in ("max_input_bytes", "max_phases", "max_appendant_bits"):
            if getattr(args, name) < 0:
                raise ValueError(name.replace("_", "-") + " must be nonnegative")
        with args.program.open("rb") as stream:
            raw = stream.read(args.max_input_bytes + 1)
        if len(raw) > args.max_input_bytes:
            raise ValueError("program exceeds max-input-bytes")
        document = json.loads(raw.decode("ascii"))
        words = document.get("appendants") if isinstance(document, dict) else document
        if not isinstance(words, list):
            raise ValueError("program JSON must contain an appendants array")
        if len(words) > args.max_phases:
            raise ValueError("program exceeds max-phases")
        program = Program(tuple(words))
        if sum(map(len, words)) > args.max_appendant_bits:
            raise ValueError("program exceeds max-appendant-bits")
        result = report(program, include_phases=args.include_phases)
        result["program_file_sha256"] = sha256(raw).hexdigest()
        output = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if args.output is None:
            print(output, end="")
        else:
            args.output.write_text(output, encoding="utf-8")
    except (OSError, UnicodeError, ValueError) as error:
        parser.error(str(error))
    return result


if __name__ == "__main__":
    main()
