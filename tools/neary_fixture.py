"""Generate deterministic program, binary seeds, and bounded CTS audit results."""
import argparse
from hashlib import sha256
from pathlib import Path

from s_only.neary_fixture import canonical_json, compile_fixture, encode_seed, run_fixture


def generate(output_dir: Path, *, max_steps: int = 100_000,
             max_word_bits: int = 16_384) -> dict:
    fixture = compile_fixture()
    # Complete both bounded checks before writing any artifact.
    runs = [run_fixture(symbol, max_steps=max_steps, max_word_bits=max_word_bits)
            for symbol in ("a", "b")]
    files = {
        "program.json": canonical_json(fixture.program_document()),
        "seed-a.txt": encode_seed("a").word + "\n",
        "seed-b.txt": encode_seed("b").word + "\n",
        "runs.json": canonical_json({"format": "neary-left-toggle-audit-v1", "runs": runs}),
    }
    manifest = {
        "format": "neary-left-toggle-artifacts-v1",
        "files": {name: {"bytes": len(text.encode("ascii")),
                         "sha256": sha256(text.encode("ascii")).hexdigest()}
                  for name, text in sorted(files.items())},
        "scope": "fixed two-state left-moving TM; ordinary CTS only; no S reductions",
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (output_dir / name).write_text(text, encoding="ascii")
    (output_dir / "manifest.json").write_text(canonical_json(manifest), encoding="ascii")
    # Verify bytes on disk, not merely the in-memory strings.
    for name, expected in manifest["files"].items():
        actual = (output_dir / name).read_bytes()
        if len(actual) != expected["bytes"] or sha256(actual).hexdigest() != expected["sha256"]:
            raise RuntimeError(f"artifact verification failed: {name}")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--max-steps", type=int, default=100_000)
    parser.add_argument("--max-word-bits", type=int, default=16_384)
    args = parser.parse_args()
    manifest = generate(args.output_dir, max_steps=args.max_steps, max_word_bits=args.max_word_bits)
    print(canonical_json(manifest), end="")


if __name__ == "__main__":
    main()
