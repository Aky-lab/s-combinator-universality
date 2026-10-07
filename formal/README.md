# Reproduce the formal results

The portable helper has two explicit theorem targets, sharing the same
pinned upstream closure and official Lean toolchain:

- **`--target register`** (the backward-compatible default):
  [`SOnlyUniversality.lean`](SOnlyUniversality.lean), with 56 project source
  files bound by [`formal_universality.json`](../results/formal_universality.json).
  This proves the finite-register-machine halting and first-event numerical
  output results. Its recorded fresh-kernel replay took 127.489 seconds; its
  separate declaration audit queried 1,142 declarations. See the
  [verification report](../docs/final-verification.md) for scope, axioms,
  negative controls, and resource observations.
- **`--target turing`**:
  [`SOnlyTuringUniversality.lean`](SOnlyTuringUniversality.lean), with 67 project
  source files. This aggregate adds the genuine integer-indexed-tape Turing
  machine compiler and `SOnlyTuringUniversality.halting_iff_event`.
  Its pinned [`formal_turing_universality.json`](../results/formal_turing_universality.json)
  records a successful 125.013-second fresh replay and a separate
  1,359-declaration audit. Its TM-specific numerical result is the finite
  left-stack code of the stated simulation, including visited extent and
  blank history; it does not assert arbitrary tape-output normalization.

Target selection changes only the pinned project manifest, project module
count, and declaration-free replay wrapper. It does not weaken identity
checks or permit pre-existing compiled outputs. Existing exported reproduction
packets retain their original helper and manifest bytes.

## Inputs you must provide

- Python 3.10 or newer, using only its standard library.
- An existing official **Lean 4.33.1** installation, including `leanchecker`.
  Obtain it from the [official Lean release](https://github.com/leanprover/lean4/releases/tag/v4.33.1).
  The recorded Linux x86-64 archive SHA-256 is
  `0376ac87487246b40dd077268c097e701f552e94c6d020d2373b50c7444fa22f`.
  The expected Lean commit is `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- The **423 Lean files and three configuration files** identified by
  [`source-manifest.json`](../artifacts/formal-replay-2026-10-06/source-manifest.json),
  from [`cstrawberry/predictive-universe` at commit
  `85a867988442fc423279341200f81634a1e65582`](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization).
  `--upstream-source` names the directory directly containing `PureSFormal/`,
  `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Extra files in a
  checkout are ignored; no existing compiled outputs are used.

The separately distributed reproduction packet includes the actual pinned
upstream files as a source-only ZIP, its hash manifest, and the
[MIT notice](../third_party/cinematic-strawberry-MIT.txt). No toolchain binaries
or compiled proof objects are included. With the official toolchain already
installed, the replay needs no network access.

## Fast preflight

From the repository or unpacked reproduction-packet root:

```sh
python tools/replay_formal.py \
  --target register \
  --lean-bin /absolute/path/to/lean-4.33.1-linux/bin \
  --upstream-source /absolute/path/to/pinned-upstream \
  --check-only
```

Choose `--target turing` instead for the 67-module aggregate. Omitting
`--target` always selects `register`; the helper never guesses a target from
available files.

This verifies the Lean version and commit; the selected project manifest and
shared upstream manifest identities; all **482** (`register`) or **493**
(`turing`) source/config SHA-256 hashes; the 426 upstream Git blob identities;
and the full dependency-first order. Only official `Init`/`Std` direct imports
may lie outside the pinned source set. Import parsing understands `import`,
`public import`, `meta import`, and `import all`, including nested comments.
The supplied Lean executable is run only for its version and installation
prefix. **Preflight does not compile or kernel-check any proof.** It creates
no workspace or output files.

## Fresh rebuild and kernel replay

```sh
python tools/replay_formal.py \
  --target register \
  --lean-bin /absolute/path/to/lean-4.33.1-linux/bin \
  --upstream-source /absolute/path/to/pinned-upstream \
  --build-dir /absolute/path/to/new-empty-replay
```

The script refuses a nonempty or symlinked build directory. It stages only
verified Lean source modules into that fresh workspace and compiles every
module in dependency order:

- `register`: 56 project + 423 upstream = **479** source modules, followed by
  the 56-import `SOnlyUniversalityReplay.lean` wrapper.
- `turing`: 67 project + 423 upstream = **490** source modules, followed by
  the 67-import `SOnlyTuringUniversalityReplay.lean` wrapper.

It compiles the selected wrapper and runs the corresponding fresh replay.
For `register`:

```sh
leanchecker --fresh -v SOnlyUniversalityReplay
```

For `turing`, the command is `leanchecker --fresh -v SOnlyTuringUniversalityReplay`.
Both targets always rebuild the full 423-module upstream closure from source.

The wrapper introduces no declarations. The only module-search roots are the
newly generated outputs and the explicitly selected official Lean library.
Inherited Lean paths and toolchain/loader hooks are discarded. The original
Lake configuration files are retained as evidence in `upstream-config/`;
**Lake and its configuration are never executed.**

Every build step gets a log under `logs/`. `replay-result.json` records the
selected target, source counts, ordered commands, statuses, elapsed times,
manifest identities, wrapper hash, and (after success) generated `.olean` hashes. Its final `status` is `passed` only
after successful `leanchecker --fresh`. A failure retains its logs. Retry in
a new empty directory; partial builds are never silently reused.

The defaults use two Lean threads and a 3,072 MB Lean elaborator memory limit
per module. This limit is **not an operating-system process-tree memory cap**
and does not apply to `leanchecker`. Timeouts default to 600 seconds per
module and 1,800 seconds for replay; see `--help` to adjust them. The earlier
127.489-second figure measures the final fresh replay alone, not the full
423-module upstream rebuild. Allow additional time and several GB of free RAM
for the full procedure. Generated object bytes can vary with build paths;
source hashes and successful kernel replay establish this reproduction.

## Trust and scope

This portable script is a reproducible direct-build procedure, **not an OS
sandbox**. Lean elaboration can execute metaprograms. Use a trusted official
toolchain and the verified pinned sources; an isolated disposable machine is
appropriate for untrusted material. The script checks the reported toolchain
version and commit, not the authenticity of an arbitrary executable. Verify
your downloaded official release independently. The archived verification run
additionally used namespace isolation, read-only inputs, no network, and
post-run integrity checks; those are documented in the existing reports.

The exact current helper's `--target turing` path also completed an isolated
source-only rebuild of all 490 modules plus its wrapper, followed by fresh
kernel replay. No old project or upstream objects were mounted. The full run
took 633.802 seconds, including a 136.142-second replay; the
[terminal receipt and complete logs](../results/portable_turing_replay.json)
are preserved. The earlier single-target register packet independently passed
the same source-only procedure for 479 modules in 609.449 seconds; see its
[separate receipt](../results/portable_register_replay.json).

The helper's fast tests cover profile selection and exact counts,
import/dependency parsing, manifest and source tampering, Git blob identities,
source-path escapes, and fresh-directory rejection. A mocked compiler test
checks both targets' staging, wrapper selection, result metadata and exclusion
of inherited output paths; **a mocked compiler is not proof verification**.
`--help` and real-toolchain `--check-only` verify the portable interface and
available pinned inputs. Completed proof-run evidence is kept separately and
is not rewritten by this helper update. Neither `--check-only` nor this script
reruns the separate declaration axiom audits or negative controls; those
recorded checks remain in the corresponding proof evidence.

The portable script deliberately pins each project's manifest hash and the
shared upstream manifest hash. A future proof revision must publish a new
reviewed manifest and update the corresponding target identity in the script.
A missing or unpinned target never falls back to another proof snapshot.
