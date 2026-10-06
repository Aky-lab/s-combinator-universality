"""Inspect exact initial CTS-to-S size; optionally build and stream its digest.

No source transition, S reduction, decoder or controller is executed.
"""
import argparse
from dataclasses import asdict
import json
from pathlib import Path

from s_only.cts import Program
from s_only.encoding import EncodingLimit, encode, encoding_stats, prefix_sha256, unique_objects
from s_only.terms import nodes


def _read(path: Path, max_bytes: int) -> str:
    # Bounded read, including when a file changes after any metadata check.
    with path.open("rb") as stream:
        data = stream.read(max_bytes + 1)
    if len(data) > max_bytes:
        raise EncodingLimit(f"{path}: exceeds input file cap of {max_bytes} bytes")
    return data.decode("ascii")


def inspect(program: Program, word: str, *, build: bool = False,
            with_sha256: bool = False, max_nodes: int = 10_000_000) -> dict:
    if type(max_nodes) is not int or max_nodes < 0:
        raise ValueError("max_nodes must be a nonnegative integer")
    stats = encoding_stats(program, word)
    result = {"format": "cts-s-initial-inspection-v1", **asdict(stats),
              "dispatcher_layout": "bottom-up-adjacent-pairs-no-padding",
              "initial_phase": 0, "constructed": False,
              "scope": "initial closed-S syntax only; no reductions or simulation"}
    if build or with_sha256:
        if stats.initial_nodes > max_nodes:
            raise EncodingLimit(f"initial term requires {stats.initial_nodes} nodes; "
                                f"construction cap is {max_nodes}")
        term = encode(program, word)
        if nodes(term) != stats.initial_nodes:
            raise AssertionError("symbolic size disagrees with constructed term")
        result.update(constructed=True, unique_objects=unique_objects(term))
        if with_sha256:
            result["initial_prefix_sha256"] = prefix_sha256(term, max_nodes=max_nodes)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--program", type=Path,
                        help="JSON array of binary appendants, or object with appendants array")
    words = parser.add_mutually_exclusive_group()
    words.add_argument("--word", help="binary initial word; use '' for empty")
    words.add_argument("--word-file", type=Path, help="ASCII bits and optional final newline")
    parser.add_argument("--build", action="store_true", help="also count shared object identities")
    parser.add_argument("--sha256", action="store_true", help="build and hash unfolded prefix bytes")
    parser.add_argument("--max-input-bytes", type=int, default=2_000_000,
                        help="maximum bytes in each input file")
    parser.add_argument("--max-source-bits", type=int, default=1_000_000,
                        help="maximum total appendant and data bits")
    parser.add_argument("--max-phases", type=int, default=10_000)
    parser.add_argument("--max-nodes", type=int, default=10_000_000,
                        help="expanded-node cap before optional construction or hashing")
    args = parser.parse_args(argv)
    try:
        for name in ("max_input_bytes", "max_source_bits", "max_phases", "max_nodes"):
            if getattr(args, name) < 0:
                raise ValueError(name.replace("_", "-") + " must be nonnegative")
        if args.program is None:
            program = Program(("1", ""))
        else:
            document = json.loads(_read(args.program, args.max_input_bytes))
            appendants = document.get("appendants") if isinstance(document, dict) else document
            if not isinstance(appendants, list):
                raise ValueError("program JSON must contain an appendants array")
            if len(appendants) > args.max_phases:
                raise EncodingLimit("program exceeds max-phases")
            program = Program(tuple(appendants))
        if len(program.appendants) > args.max_phases:
            raise EncodingLimit("program exceeds max-phases")
        if args.word_file is not None:
            word = _read(args.word_file, args.max_input_bytes)
            if word.endswith("\r\n"):
                word = word[:-2]
            elif word.endswith("\n"):
                word = word[:-1]
        elif args.word is not None:
            word = args.word
        elif args.program is None:
            word = "101"
        else:
            raise ValueError("--program requires --word or --word-file")
        if sum(map(len, program.appendants)) + len(word) > args.max_source_bits:
            raise EncodingLimit("source exceeds max-source-bits")
        result = inspect(program, word, build=args.build, with_sha256=args.sha256,
                         max_nodes=args.max_nodes)
    except (OSError, UnicodeError, ValueError) as error:
        parser.error(str(error))
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
