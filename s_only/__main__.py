"""Run with python -m s_only."""
import argparse
import json
from pathlib import Path

from .reduction import reduce
from .terms import format_term, nodes, parse
from .traces import certificate, verify_certificate


def main():
    parser = argparse.ArgumentParser(description="Native S-only tree reduction and trace verification")
    sub = parser.add_subparsers(dest="command", required=True)
    run = sub.add_parser("reduce")
    run.add_argument("term")
    run.add_argument("--strategy", choices=("normal", "applicative", "head"), default="normal")
    run.add_argument("--max-steps", type=int, default=1000)
    run.add_argument("--max-nodes", type=int, default=100000)
    run.add_argument("--certificate", type=Path)
    check = sub.add_parser("verify")
    check.add_argument("file", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "verify":
            data = json.loads(args.file.read_text())
            final = verify_certificate(data)
            print(json.dumps({"verified": True, "steps": len(data["steps"]),
                              "status": data["status"], "final": final}, indent=2))
        else:
            result = reduce(parse(args.term), args.strategy, args.max_steps, args.max_nodes)
            data = certificate(result)
            verify_certificate(data)
            if args.certificate:
                args.certificate.write_text(json.dumps(data, indent=2) + "\n")
            print(json.dumps({"strategy": result.strategy, "steps": len(result.paths),
                              "status": result.status, "nodes": nodes(result.final),
                              "final": format_term(result.final)}, indent=2))
    except (ValueError, OSError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
