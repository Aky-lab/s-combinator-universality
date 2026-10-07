# Review of the generic formal replay

6 October 2026. This is a separate review of the completed execution evidence,
the isolation harness, and the scope of the resulting claims. The reviewer
read the sources and logs and independently recomputed file hashes; the
reviewer did not execute Lean or the upstream project.

## Finding

The evidence supports the following statement:

> The pinned 423-module generic dependency closure was locally compiled from
> authenticated source bytes with the official Lean 4.33.1 distribution. An
> import-only wrapper over its three minimal roots then passed the official
> `leanchecker --fresh` replay. The types and axiom dependencies of 24 named
> interface declarations were queried successfully; their reported axioms
> were limited to `propext` and `Quot.sound`.

No replay-validity blocker was found in the reviewed evidence. This upgrades
the inherited generic formal interfaces from source inspection to a locally
reproduced build and fresh official-kernel replay. It does not by itself
formalize the additional first-event proof in
[the 38-phase universality construction](universality-theorem.md).

The [execution report](formal-replay.md),
[machine-readable result](../results/formal_replay.json), and
[preserved evidence](../artifacts/formal-replay-2026-10-06/) supply the run
details. The earlier [source-closure audit](generic-formal-closure.md) remains
a distinct, historical source-only result.

## Identity and coverage

The project source pin is
`85a867988442fc423279341200f81634a1e65582` in
`cstrawberry/predictive-universe`. The official Lean source commit is
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, distributed as Lean 4.33.1.
The verified ZIP SHA-256 is
`0376ac87487246b40dd077268c097e701f552e94c6d020d2373b50c7444fa22f`.

The reviewer independently established that:

- All 423 theorem sources and three original build-control files match the
  staged SHA-256 manifest. Their Git blob identities also match the pinned
  source inventory. No additional source file is present in that staged tree.
- The 423-entry build order exactly matches the earlier dependency-first
  inventory, and every project import precedes its importer.
- All 423 final build records report success and have corresponding outputs.
  The first 38 outputs came from the first cold build attempt, before that
  attempt failed on module 39. Their pre-resumption hashes still match. The
  remaining 385 were compiled successfully in the resumed attempt; this was
  not reuse of upstream precompiled project artifacts.
- `SOnlyGenericReplay.lean` contains only the three imports below, with no
  declaration or extra `Lean` import:

```lean
import PureSFormal.Research.RootResetFiniteAllInputsTraceAgreement
import PureSFormal.Research.RootResetContractProjection
import PureSFormal.PureS.EncoderSize
```

The frozen output inventory consists of exactly 423 project `.olean` files
and this one freshly compiled wrapper. The canary objects are outside the
project search directory. The configured search path contains that frozen
directory and the verified official installation; it does not expose an
upstream project build cache.

The 424-file before/after output manifests are byte-identical. Their SHA-256
is `6973fcccc26c434d3d83d53b1e7d18297831a080450b525c3b1b4b445fdcbdcd`.
After replay, the reviewer independently rehashed all 426 source/config
files, all 424 outputs, all 17,505 installed toolchain files, and the three
guard/audit/replay helpers. Every recorded digest matched. This corroborates
the executor's separate post-replay verification.

## What the successful stages establish

### Source build

Every module in the exact selected project closure compiled successfully.
The resumed build took approximately 388.385 seconds, in addition to the
earlier attempt. Its sampled aggregate namespace RSS peak was
1,443,426,304 bytes.

A successful source build alone would not exclude deliberately manipulated
Lean environments. The independent fresh-replay stage is therefore material,
rather than a redundant invocation of the source elaborator.

### Type and axiom queries

The type-audit file successfully ran `#check` and `#print axioms` for the
original 22 targets plus:

- `PureSFormal.Research.RootResetContractProjection.none_iff_normal`
- `PureSFormal.PureS.SchedulerCycle.SelectedResponseTrace.targetDecode`

Twelve queried declarations report only `propext`; twelve report `propext`
and `Quot.sound`. None of these 24 reports includes `sorryAx`,
`Classical.choice`, or a native-reduction trust axiom. This is a census of
those selected declarations' reported dependencies, not a census of every
declaration in all imported modules.

The additional full `#print` confirms that
`RootResetSelectorContract.Contract.InterInvocationState` unfolds to
`fun _contract => Unit`. Its `#check` alone would have shown only its type,
not this body. The separate `targetDecode` query also exposes the actual
frozen-carrier decoding equation, rather than merely the response structure's
type. Preconditions visible in other signatures remain part of those
theorems; querying them does not remove them.

### Fresh official-kernel replay

The terminal command was:

```text
/opt/lean/bin/leanchecker --fresh -v SOnlyGenericReplay
```

Both the inner guard and outer launcher recorded exit status zero with no
stop reason. The inner duration was approximately 119.452 seconds, and its
sampled aggregate namespace RSS peak was 1,516,060,672 bytes.

Inspection of the pinned, installed
[`LeanChecker`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/LeanChecker.lean)
and
[`Lean.Replay`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Replay.lean)
sources confirms the relevant behavior: `--fresh` imports one selected
module and replays its imported constant environment into an empty
environment using the same official Lean kernel. Safe, nonpartial
declarations are processed; unsafe and partial declarations are skipped.
Inductive constructors and recursors are regenerated and compared with their
stored forms. Axioms are accepted as axioms, making the separate selected
axiom queries necessary.

The wrapper therefore covers the three roots' exact 423-project-module
union, together with the imported official-library environment. It is not an
independent kernel implementation, an independently bootstrapped toolchain,
or a replay of the upstream project's full 1,239-module inventory.

### Positive and negative controls

The preserved controls show three distinct outcomes:

1. A valid tiny theorem compiled and passed fresh replay.
2. An ordinary invalid theorem was rejected with a source type mismatch.
3. The pinned deliberate environment-manipulation canary compiled, but fresh
   replay rejected its named `invalidFalse` declaration specifically because
   the stored proof had type `Prop` where `False` was required.

The third result checks the important distinction between successful
elaboration and fresh-kernel rejection of an injected invalid declaration.
A generic nonzero exit, missing module, or resource abort would not have
supplied the same evidence. Earlier unsuccessful setup/control attempts must
remain distinguishable from these successful controls.

## Isolation and resource qualifications

The reviewed harness clears inherited environment variables, closes
unneeded inherited descriptors, uses dedicated user/PID/UTS/IPC namespaces,
drops capabilities, and exposes the public working area instead of private
workspace or home directories. Original project sources, configuration, and
the official toolchain are read-only inside the sandbox.

The syscall filter denies socket operations, `ptrace`,
`process_vm_readv`/`process_vm_writev`, `pidfd_getfd`, and `io_uring` entry
points, among other selected operations. Ordinary process creation and
signals are not generally denied. The evidence should not describe this as
a blanket prohibition on all cross-process syscalls or as network-namespace
isolation: network access is blocked through syscall denial.

Before the successful replay, the compiled-output directory and the guard,
type-audit, and import-only helper sources were additionally mounted
read-only. A dedicated canary confirmed refusal of writes to representative
project and wrapper outputs and helper inputs. External before/after hashes
provide the complementary check of input stability.

Resource reporting needs three distinctions:

- Early 6-GiB and 12-GiB virtual-address limits caused runtime thread-creation
  failures. These were infrastructure failures, not rejected mathematical
  proofs. The completed run used a 32-GiB per-process virtual-address limit.
- The outer process monitor could not observe the nested proof processes.
  Its RSS figures are launcher-only measurements. Earlier metadata purporting
  to describe a 4-GiB aggregate inner limit is not evidence of such enforcement.
- The later guard runs inside the PID namespace and samples aggregate process
  RSS every 50 ms, stopping when its 4-GiB threshold is exceeded. A touched
  128-MiB allocation produced an approximately 150-MB observation, and a
  separate 64-MiB threshold test terminated that allocation as intended.

This is sampled monitoring, not a hard cgroup memory cap: transient
overshoot is possible, shared mappings may be counted more than once, and it
does not supply comprehensive disk, tmpfs, or thread quotas. The guard also
has a sampled process-count threshold and wall-clock timeout. The same-UID
guard/report arrangement is not a tamper-proof resource boundary against
arbitrarily hostile code; the reviewed source scan, namespace restrictions,
read-only replay inputs, and external hashing have distinct roles. None of
these qualifications turns the recorded successful replay into a failed
proof check, but they limit the security and memory guarantees one may claim.

## Remaining scope boundary

This review covers the pinned generic closure and the named interface
queries. It does not certify the project's new register-machine front end,
Local-event provenance argument, first-event composition, polynomial output
reader, or all-input equivalence of the independent Python implementation.
Those retain the verification statuses documented in their own proofs and
reviews. Any separately compiled concrete 38-phase instance is also a
separate artifact and must be reported with its own checked theorem scope.

The supported conclusion is a successful, source-bound local reproduction
of the selected generic formal interfaces with official fresh-kernel replay,
under the stated axioms and trust boundary.

## Addendum: concrete 38-phase instance

7 October 2026. The reviewer separately inspected
[`formal/SOnly38.lean`](../formal/SOnly38.lean), its
[scope report](formal-cts-instance.md),
[structured result](../results/formal_cts_instance.json), and the captured
`fixed38-*` and `guard-fixed38-*` evidence. No Lean or project test code was
executed by the reviewer.

The checked source SHA-256 is
`3fb5944191b4a22c7152f2594b2b8e3d97579da1b4f86081bd046f4993ee9128`;
the 258,792-byte compiled module has SHA-256
`e99cf78d1037f8e3104889d26cbbdecb415396af0cb16de0ddfbf37ace36137f`.
Both were independently rehashed and matched the before/after records.
The successful compiler log and guard agree on exit zero. The separate
fresh-replay log and guard agree on exit zero, 113.727 seconds, and sampled
namespace peak RSS of 1,513,676,800 bytes. All 13 printed axiom reports match
the result: two have no axioms, two use only `propext`, and nine use
`propext` with `Quot.sound`.

The actual theorem statements support these concrete claims:

- The literal program has 38 appendants, 760 bits, and 40 ones; finite-phase
  enumeration binds these counts to `program.appendant`. The designated
  phase-17 appendant and dispatcher route `0100011` are checked, and its
  response is nonempty for every suffix. Static parsing independently
  confirmed that the Lean production literal matches the Python table.
- The fixed controller starts at the root, has `Unit` boundary state and a
  positive fixed linear-time coefficient, and terminates on every finite
  tree. Successful and unsuccessful selector answers have the stated
  one-contraction and zero-contraction consequences.
- For every input bitword and contraction index, the constructed trajectory
  agrees with the persistent trajectory and takes a native S step. The
  public-checkpoint decoder returns the exact CTS iterate, and any successful
  public decode identifies its checkpoint and configuration.

These last conclusions are specializations of the pinned generic results.
The answer/decode hypotheses identify an actual selector answer or decoder
result; they do not assume the missing source-universality or first-event
theorem. The checked decoder is `PublicDecoder.decode`, not the completed-F17
event observer or numerical result reader. The remaining source, first-event,
regular-observer, and output-composition proof boundary therefore remains.

This module's two imports reach 422 upstream project modules, omitting the
standalone `EncoderSize` root. Its separate fresh replay covers that imported
environment plus the new module; the earlier generic replay still covers all
423 upstream modules. The reviewer repeated the post-instance hashes of all
426 pinned source/config files, 424 original compiled/helper outputs, and
17,505 toolchain files, with no mismatches.

The expanded public evidence also resolves the earlier packaging suggestions:
its losslessly compressed full toolchain manifest reproduces the recorded
digest, and the resumed build driver, first-attempt records, raw canary
statuses, and historical-memory correction are preserved. No concrete-instance
proof-validity blocker was found within the stated scope.
