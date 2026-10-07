#!/usr/bin/env python3
"""Offline, dependency-first source rebuild and fresh Lean kernel replay.

Python 3.10+, standard library only. Never downloads, installs, runs Lake, or
loads pre-existing project/upstream .olean files. See formal/README.md.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import time

VERSION = "4.33.1"
LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
UPSTREAM_COMMIT = "85a867988442fc423279341200f81634a1e65582"
UPSTREAM_MANIFEST_SHA256 = "c90a264962c28aa5cedf002f27945e00476f0cf586975ea6ad25036b94b5b301"
PROJECT_MANIFEST_SHA256 = "3dbf46e18d822369fbffeeaeb6b74923bc4916693ee5b67c890563d640713038"
WRAPPER = "SOnlyUniversalityReplay"
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
CONFIGS = {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}


class ReplayError(Exception):
    """A checked precondition or build step failed."""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_manifest(path: Path, expected_hash: str):
    data = path.read_bytes()
    if sha256(data) != expected_hash:
        raise ReplayError(f"Manifest identity mismatch: {path}")
    return json.loads(data)


def safe_relative(value: str) -> Path:
    parts = PurePosixPath(value)
    if not value or parts.is_absolute() or ".." in parts.parts or "\\" in value:
        raise ReplayError(f"Unsafe manifest path: {value!r}")
    if str(parts) != value:
        raise ReplayError(f"Non-canonical manifest path: {value!r}")
    return Path(*parts.parts)


def verified_sources(root: Path, rows: list[dict]) -> dict[str, bytes]:
    """Read verified bytes once; staging uses exactly these in-memory bytes."""
    result = {}
    for row in rows:
        relative = safe_relative(row["path"])
        path = (root / relative).resolve(strict=True)
        if not path.is_relative_to(root):
            raise ReplayError(f"Source escapes its supplied root: {path}")
        if row["path"] in result:
            raise ReplayError(f"Duplicate manifest path: {row['path']}")
        data = path.read_bytes()
        if len(data) != row["bytes"] or sha256(data) != row["sha256"]:
            raise ReplayError(f"Source identity mismatch: {path}")
        if "git_blob_sha1" in row:
            blob = b"blob " + str(len(data)).encode() + b"\0" + data
            if hashlib.sha1(blob).hexdigest() != row["git_blob_sha1"]:
                raise ReplayError(f"Git blob identity mismatch: {path}")
        result[row["path"]] = data
    return result


def header_token(text: str, position: int) -> tuple[str, int]:
    """Read an ASCII header token, respecting line and nested block comments."""
    while position < len(text):
        if text[position].isspace() or text[position] == "\ufeff":
            position += 1
        elif text.startswith("--", position):
            end = text.find("\n", position)
            position = len(text) if end < 0 else end + 1
        elif text.startswith("/-", position):
            depth = 1
            position += 2
            while depth and position < len(text):
                if text.startswith("/-", position):
                    depth += 1
                    position += 2
                elif text.startswith("-/", position):
                    depth -= 1
                    position += 2
                else:
                    position += 1
            if depth:
                raise ReplayError("Unterminated Lean header comment")
        else:
            found = MODULE.match(text, position)
            return (found.group(), found.end()) if found else (text[position], position + 1)
    return "", position


def parse_imports(data: bytes) -> list[str]:
    """Parse this pinned snapshot's header grammar, including import modifiers.

    Supports module/prelude, import, public import, meta import, import all,
    and public meta import. Only ASCII module names occur in the pinned sources.
    Stops before declarations, so strings/quotations in the body are irrelevant.
    """
    text = data.decode("utf-8")
    token, position = header_token(text, 0)
    if token == "module":
        token, position = header_token(text, position)
    imports = []
    if token == "prelude":
        token, position = header_token(text, position)
    else:
        imports.append("Init")
    while True:
        if token == "public":
            token, position = header_token(text, position)
        if token == "meta":
            token, position = header_token(text, position)
        if token != "import":
            return imports
        name, position = header_token(text, position)
        if name == "all":
            name, position = header_token(text, position)
        if not MODULE.fullmatch(name) or name in {"import", "public", "meta", "all"}:
            raise ReplayError(f"Unsupported or missing imported module: {name!r}")
        imports.append(name)
        token, position = header_token(text, position)


def dependency_order(modules: dict[str, bytes], libdir: Path) -> tuple[list[str], list[str]]:
    dependencies = {name: parse_imports(data) for name, data in modules.items()}
    external = sorted({item for deps in dependencies.values() for item in deps} - modules.keys())
    for name in external:
        if name.split(".")[0] not in {"Init", "Std"}:
            raise ReplayError(f"Unpinned dependency outside official Init/Std: {name}")
        if not (libdir / (name.replace(".", "/") + ".olean")).is_file():
            raise ReplayError(f"Missing official library dependency: {name}")
    order, active, completed = [], set(), set()

    def visit(name: str) -> None:
        if name in completed:
            return
        if name in active:
            raise ReplayError(f"Cyclic source imports at {name}")
        active.add(name)
        for item in sorted(set(dependencies[name])):
            if item in modules:
                visit(item)
        active.remove(name)
        completed.add(name)
        order.append(name)

    for name in sorted(modules):
        visit(name)
    return order, external


def validate_build_directory(path: Path) -> None:
    if path.is_symlink():
        raise ReplayError(f"Build directory must not be a symbolic link: {path}")
    if path.exists() and (not path.is_dir() or any(path.iterdir())):
        raise ReplayError(f"Build directory must be absent or empty: {path}")


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def positive_int(value: str) -> int:
    result = int(value)
    if result < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean-bin", required=True, type=Path,
                        help="existing official Lean 4.33.1 bin directory (contains lean and leanchecker)")
    parser.add_argument("--upstream-source", required=True, type=Path,
                        help="existing pinned source root containing PureSFormal/ and three config files")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="project/source-packet root (default: parent of tools/)")
    parser.add_argument("--build-dir", type=Path,
                        help="absent or empty fresh workspace; required unless --check-only")
    parser.add_argument("--check-only", action="store_true",
                        help="verify versions, hashes and dependency order; do not stage, compile or replay")
    parser.add_argument("--threads", type=positive_int, default=2, help="Lean worker threads (default: 2)")
    parser.add_argument("--memory-mb", type=positive_int, default=3072,
                        help="Lean elaborator memory limit per module (default: 3072; not an OS-wide cap)")
    parser.add_argument("--module-timeout", type=positive_int, default=600,
                        help="wall-clock timeout per elaboration in seconds (default: 600)")
    parser.add_argument("--replay-timeout", type=positive_int, default=1800,
                        help="fresh kernel replay wall-clock timeout in seconds (default: 1800)")
    args = parser.parse_args(argv)
    if not args.check_only and args.build_dir is None:
        parser.error("--build-dir is required unless --check-only")
    if args.build_dir is not None:
        validate_build_directory(args.build_dir)
    repo = args.repo_root.resolve(strict=True)
    upstream_root = args.upstream_source.resolve(strict=True)
    lean_bin = args.lean_bin.resolve(strict=True)
    lean, checker = lean_bin / "lean", lean_bin / "leanchecker"
    for executable in (lean, checker):
        if not executable.is_file() or not os.access(executable, os.X_OK):
            raise ReplayError(f"Required executable not found: {executable}")
    # Do not inherit LEAN_PATH, ELAN_TOOLCHAIN, LD_PRELOAD, or other caller hooks.
    environment = {"PATH": str(lean_bin), "LEAN_NUM_THREADS": str(args.threads), "LANG": "C.UTF-8"}
    version = subprocess.check_output([str(lean), "--version"], env=environment, text=True, timeout=30).strip()
    if f"version {VERSION}," not in version or f"commit {LEAN_COMMIT}," not in version:
        raise ReplayError(f"Wrong Lean version/commit: {version}")
    prefix = Path(subprocess.check_output([str(lean), "--print-prefix"], env=environment,
                                          text=True, timeout=30).strip()).resolve(strict=True)
    if prefix != lean_bin.parent:
        raise ReplayError("Use the official installation's actual bin directory, not an elan/shim directory")
    libdir = prefix / "lib" / "lean"
    project = read_manifest(repo / "results/formal_universality.json", PROJECT_MANIFEST_SHA256)
    upstream_rows = read_manifest(repo / "artifacts/formal-replay-2026-10-06/source-manifest.json",
                                  UPSTREAM_MANIFEST_SHA256)
    if project["upstream"]["commit"] != UPSTREAM_COMMIT or project["toolchain"]["version"] != VERSION:
        raise ReplayError("Unexpected pinned upstream/toolchain metadata")
    project_sources = verified_sources((repo / "formal").resolve(strict=True), project["modules"])
    upstream_sources = verified_sources(upstream_root, upstream_rows)
    if len(project_sources) != 56 or len(upstream_sources) != 426:
        raise ReplayError("Expected exactly 56 project and 426 upstream source/config files")
    if {name for name in upstream_sources if not name.endswith(".lean")} != CONFIGS:
        raise ReplayError("Unexpected upstream configuration-file set")
    modules = {}
    for filename, data in {**upstream_sources, **project_sources}.items():
        if not filename.endswith(".lean"):
            continue
        name = filename[:-5].replace("/", ".")
        if not MODULE.fullmatch(name) or name in modules or name.split(".")[0] in {"Init", "Std", "Lean", "Lake"}:
            raise ReplayError(f"Invalid, duplicate or reserved module: {name}")
        modules[name] = data
    if len(modules) != 479:
        raise ReplayError("Expected exactly 479 distinct source modules")
    for row in project["modules"]:
        if row["module"].replace(".", "/") + ".lean" != row["path"]:
            raise ReplayError(f"Project module/path mismatch: {row['module']}")
    order, external = dependency_order(modules, libdir)
    wrapper = "".join(f"import {row['module']}\n" for row in project["modules"]).encode()
    summary = {
        "schema": "s-only-offline-replay-v1", "status": "identity-and-dependencies-verified",
        "lean_version": version, "upstream_commit": UPSTREAM_COMMIT,
        "project_sources": 56, "upstream_modules": 423, "upstream_configs": 3,
        "official_direct_imports": external, "compile_order": order,
        "wrapper_module": WRAPPER, "wrapper_sha256": sha256(wrapper),
        "project_manifest_sha256": PROJECT_MANIFEST_SHA256,
        "upstream_manifest_sha256": UPSTREAM_MANIFEST_SHA256,
    }
    print(f"Verified 56 project + 423 upstream Lean sources and 3 configs; Lean {VERSION}.", flush=True)
    print("External direct imports: " + ", ".join(external), flush=True)
    if args.check_only:
        print("CHECK ONLY PASSED: hashes and dependency order verified; no compilation or kernel replay performed.")
        return 0
    build = args.build_dir.absolute()
    validate_build_directory(build)
    build.mkdir(parents=True, exist_ok=True)
    build = build.resolve(strict=True)
    source, output, logs = build / "source", build / "olean", build / "logs"
    for path in (source, output, logs, build / "home", build / "tmp", build / "upstream-config"):
        path.mkdir()
    for name, data in modules.items():
        path = source / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    (source / f"{WRAPPER}.lean").write_bytes(wrapper)
    for name in sorted(CONFIGS):
        (build / "upstream-config" / name).write_bytes(upstream_sources[name])
    environment.update({"LEAN_SYSROOT": str(prefix), "LEAN_PATH": os.pathsep.join((str(output), str(libdir))),
                        "HOME": str(build / "home"), "TMPDIR": str(build / "tmp")})
    summary.update({"status": "building", "lean_path": environment["LEAN_PATH"], "records": []})
    write_json(build / "replay-result.json", summary)
    started = time.monotonic()

    def run_step(name: str, command: list[str], timeout: int) -> None:
        begin = time.monotonic()
        log = logs / f"{name}.log"
        with log.open("w", encoding="utf-8") as stream:
            try:
                result = subprocess.run(command, cwd=source, env=environment, stdin=subprocess.DEVNULL,
                                        stdout=stream, stderr=subprocess.STDOUT, timeout=timeout, check=False)
                code, timed_out = result.returncode, False
            except subprocess.TimeoutExpired:
                code, timed_out = 124, True
        record = {"step": name, "command": command, "exit_code": code,
                  "timed_out": timed_out, "elapsed_seconds": time.monotonic() - begin,
                  "log": str(log.relative_to(build))}
        summary["records"].append(record)
        summary["elapsed_seconds"] = time.monotonic() - started
        if code:
            summary["status"] = "failed"
        write_json(build / "replay-result.json", summary)
        print(f"{name}: exit {code}, {record['elapsed_seconds']:.3f}s", flush=True)
        if code:
            raise ReplayError(f"Step failed: {name}; inspect {log}; use a new empty build directory to retry")

    for name in order + [WRAPPER]:
        relative = name.replace(".", "/")
        artifact = output / f"{relative}.olean"
        artifact.parent.mkdir(parents=True, exist_ok=True)
        run_step(name, [str(lean), f"-j{args.threads}", f"-M{args.memory_mb}", "-R", str(source),
                        "-o", str(artifact), str(source / f"{relative}.lean")], args.module_timeout)
        if not artifact.is_file():
            raise ReplayError(f"Successful compiler exit but missing output: {artifact}")
    summary["status"] = "replaying"
    write_json(build / "replay-result.json", summary)
    run_step("fresh-kernel-replay", [str(checker), "--fresh", "-v", WRAPPER], args.replay_timeout)
    summary["status"] = "passed"
    summary["output_hashes"] = [{"path": str(p.relative_to(output)), "sha256": sha256(p.read_bytes())}
                                for p in sorted(output.rglob("*.olean"))]
    write_json(build / "replay-result.json", summary)
    print(f"FRESH KERNEL REPLAY PASSED: {build / 'replay-result.json'}", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ReplayError, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"replay_formal: {error}", file=sys.stderr)
        raise SystemExit(1)
