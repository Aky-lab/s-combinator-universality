# Fresh replay of the generic S-controller proofs

6 October 2026. **All 423 pinned project modules compiled, and fresh official
Lean kernel replay passed for their three-root import union.** The 24 selected
declaration queries reported only `propext` and `Quot.sound`. Source, compiled
output, helper, and toolchain hashes were unchanged after replay.

- [Machine-readable result](../results/formal_replay.json)
- [Independent evidence review](formal-replay-review.md)
- [Captured evidence](../artifacts/formal-replay-2026-10-06/)
- [Exact import-closure audit](generic-formal-closure.md)

## Checked construction and toolchain

The source is Cinematic Strawberry's generic CTS-to-S construction at commit
[`85a867988442fc423279341200f81634a1e65582`](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality).
The closure consists of 423 Lean modules, with three irredundant roots:

```text
PureSFormal.Research.RootResetFiniteAllInputsTraceAgreement
PureSFormal.Research.RootResetContractProjection
PureSFormal.PureS.EncoderSize
```

The source/module identities and dependency order are recorded in
[`generic_formal_closure.json`](../results/generic_formal_closure.json).
Explicit external imports are `Std`, with Lean's implicit `Init`; both come
from the pinned official distribution. The package configuration has no
external Lake packages. Some specialized source-machine results are imported
by upstream module organization, even though the construction uses the generic
CTS declarations.

The official toolchain reports:

```text
Lean 4.33.1
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
Lake 5.0.0-src+819816b
```

The [official Linux ZIP](https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.zip)
has 896,280,645 bytes and SHA-256
`0376ac87487246b40dd077268c097e701f552e94c6d020d2373b50c7444fa22f`.
The release API, downloaded archive, and three pinned executable hashes agreed.
Safe extraction produced 17,505 regular files; every file was hashed and checked
again after replay. The source staging retained the original configuration bytes.

## Fresh compilation and exact declaration checks

Every project module was elaborated in dependency-first order with the official
compiler, using an initially empty project-output directory:

```sh
lean -j2 -M3072 -o OUTPUT.olean SOURCE.lean
```

No prebuilt project proof cache was imported. The first 38 outputs were produced
in the first local attempt. Module 39 failed to create a thread under the initial virtual-address cap;
those 38 successful outputs were retained and hash-bound, and the remaining
385 modules compiled under the revised resource envelope. All 423 final module
records have exit status zero. The resumed attempt took 388.385 seconds; its
sampled namespace peak RSS was 1,443,426,304 bytes.

The [type/axiom audit source](../artifacts/formal-replay-2026-10-06/SOnlyTypeAudit.lean)
uses only the three root imports and standard `#check`, `#print axioms`, and
`#print` commands. Its [captured output](../artifacts/formal-replay-2026-10-06/type-axiom-audit.txt)
checks the actual quantified interfaces for:

- arbitrary-program/all-input selector totality and the linear invocation bound;
- exact one-contraction answers, normal-form answers, and their projection;
- equality with every persistent contraction sample;
- exact nonempty stages, positive-stage existence, and checkpoint construction;
- positioned/paired response lists and their complete residual enumeration;
- the selected response's suffix snapshot and its seed-free public decode;
- canonical balanced dispatch and literal generator-size formulas.

`InterInvocationState` prints as `fun _contract => Unit`. Twelve queried
declarations use `propext` alone; twelve use `propext` and `Quot.sound`.
The [structured query results](../artifacts/formal-replay-2026-10-06/queried-axioms.json)
name all 24 declarations. This is the queried-declaration audit scope.

## Fresh kernel reconstruction

The [replay helper](../artifacts/formal-replay-2026-10-06/SOnlyGenericReplay.lean)
contains exactly the three imports and no declarations. After compilation,
all 424 project/helper `.olean` files were hashed and mounted read-only.
The actual replay command was:

```sh
leanchecker --fresh -v SOnlyGenericReplay
```

It exited successfully in **119.452 seconds**, with sampled namespace peak RSS
**1,516,060,672 bytes**. The [replay log](../artifacts/formal-replay-2026-10-06/fresh-kernel-replay.txt)
and [guard record](../artifacts/formal-replay-2026-10-06/guard-replay.json)
retain the command and result.

Official `--fresh` reconstructs an empty environment and sends the imported
safe, nonpartial declarations through the Lean kernel. It regenerates and
checks inductive declarations and their associated constructors/recursors.
This is a fresh invocation of the same official kernel implementation. The
separate axiom queries establish the stated dependency lists for the selected
interfaces.

## Acceptance, rejection, and isolation controls

The controls exercised both successful and rejected inputs:

1. A valid arithmetic theorem compiled and passed fresh replay.
2. An ordinary attempted proof of `False` from `True.intro` failed with a type
   mismatch and produced no accepted output.
3. The pinned `InvalidProof.lean` control deliberately inserted an ill-typed
   `invalidFalse` into an exported environment. Compilation succeeded, while
   fresh replay rejected it with the expected kernel declaration-type mismatch,
   identifying `Prop` where `False` was required. Its output was moved outside
   the project search path before compiling the real closure.
4. Filesystem/environment canaries confirmed that private workspace paths were
   absent, the environment was explicitly set, and new IPv4/IPv6/Unix sockets
   were denied. Toolchain, source, compiled replay outputs, and replay helpers
   were verified read-only.
5. An inner PID-namespace resource guard observed a 128-MiB allocation and
   rejected it under a deliberately smaller 64-MiB test cap.

The isolated processes had a 32-GiB virtual-address reservation cap. The inner
guard sampled aggregate namespace RSS every 50 ms against a 4-GiB threshold;
transient overshoot is possible. Compilation used Lean's 3,072-MB memory option,
a 300-second per-module timeout, and a 1,800-second overall build/replay timeout.
Lean's mapped/reserved address space required a larger virtual limit than its
resident-memory use. The earlier 6-/12-GiB startup failures were resource
refusals, with their successful outputs and later retries recorded explicitly.

The isolation also denies `ptrace`, `process_vm_*`, `pidfd_getfd`, sockets,
and `io_uring` paths. Ordinary process creation and signals remain available
inside the isolated PID namespace. Writable storage is limited to the public
work area and temporary filesystem. This is a tested resource/isolation setup
for the inspected sources; the sampled guard has no tamper-proof guarantee
against hostile same-UID processes. Outer launcher-only memory observations
are excluded from the reported Lean resource measurements.

## Post-replay identity checks

An external check rehashed every staged or installed file:

| Input/output set | Checked files | Result |
| --- | ---: | --- |
| Pinned sources and original configuration | 426 | Unchanged |
| Fresh project outputs and replay helper | 424 | Unchanged |
| Official installed toolchain | 17,505 | Unchanged |
| Replay, audit, and resource-guard helpers | 3 | Unchanged |

The [before](../artifacts/formal-replay-2026-10-06/outputs-before-replay.json)
and [after](../artifacts/formal-replay-2026-10-06/outputs-after-replay.json)
output manifests are byte-identical. Their SHA-256 is
`6973fcccc26c434d3d83d53b1e7d18297831a080450b525c3b1b4b445fdcbdcd`.
The independent review repeated all file hashes and inspected the raw logs.

## Role in the complete theorem

This check establishes the imported generic controller/stage/trajectory proof
closure used by [the consolidated construction](universality-theorem.md).
The project-specific register-machine front end, compact-source invariants,
Local-origin/first-event lift, and result composition have their separate
written proofs and reviews. Their mechanization is the next proof layer.
The [fixed 38-phase instance](formal-cts-instance.md) records the concrete
program and specialized theorem checks separately.

For reproduction, retrieve the exact files in the source manifest, verify the
official archive and executable hashes, start with empty project outputs,
elaborate in the recorded dependency order, compile the import-only helper,
run the type/axiom queries, freeze the outputs, and invoke the displayed fresh
replay command. Preserve the acceptance/rejection controls and final source,
output, and toolchain identity checks.
