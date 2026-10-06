# Independent review: the finite-prefix first-event transfer

6 October 2026. Independent review of
[the CTS-to-F17 composition](cts-event-transfer.md), using the pinned source
at `85a867988442fc423279341200f81634a1e65582` and the previously reviewed
[Local-origin argument](local-event-provenance-review.md).

## Verdict

**Scoped signoff as a written mathematical composition.** I found no remaining
off-by-one, missing nonempty-successor premise, or missing sample-transfer
premise in the revised argument. The restriction to prefixes before the first
target event is sufficient. The first target completion occurs in the first
job of stage `r+1`, at that job's last response, when `r` is the zero-based
first target CTS prestate index.

This signoff concerns the exact construction defined using the pinned upstream
encoder and selector. It relies on the imported source theorems and on the
previously reviewed occurrence and source-simulation proofs. It is not a Lean
elaboration, dependency replay, proof of the Python port, or unrestricted
event-provenance theorem for arbitrary CTS inputs.

The review challenged five seams independently: the inclusive nonempty
horizon, stage/job chronology, complete contraction coverage, the seed-free
audit decoder, and the identity of the root-reset selector being transferred.

## 1. The inclusive endpoint is essential and is supplied

`SchedulerStageAssembly.allNonemptyRawAt` takes `fuel` but constructs stage
`fuel+1`. Its premise is exactly

```text
forall i <= fuel+1, (CTS.iterate P i (CTS.initial P w)).data != [].
```

Thus an event at `c_r` alone would not suffice to instantiate this theorem at
stage `r+1`: it additionally requires `c_(r+1)` to be nonempty. The revised
proof explicitly supplies that fact. At the target phase, deleting the head
one appends a 19-bit word, so the successor has at least 19 bits regardless of
the old suffix length.

For smaller stages, restricting this same hypothesis supplies every required
endpoint. In the event-free case, the source's nonexhaustion theorem supplies
the hypothesis at every finite horizon. The one-hot exact-step lemma also
excludes exhaustion inside a 19-step block: before its last deletion, an
original bit of that block remains; at its boundary the simulated tag queue
is nonempty.

This is why initially-empty and first-empty stage branches are unnecessary
for the **new annotated event lift**. They remain dependencies of the imported
general scheduler results. The review does not erase those dependencies or
claim that arbitrary CTS trajectories stay nonempty.

## 2. The stage number and response index are correct

The body of `allNonemptyRawAt` calls:

1. `SchedulerNestedPhase.positiveStagePhaseInvariantAt` for the first
   clock/launch/fuel segment;
2. `SchedulerNonfinalJobs.completeAt` with both `fuel` and its recursive job
   count equal to `h-1`;
3. `SchedulerNestedResponse.completeNonemptyTerminalJobRawAt` with fuel `h`.

`completeAt` passes `h` as the response fuel of each nonfinal job. Therefore
there are `h-1` nonfinal jobs plus one terminal job, all with exactly `h`
responses. The second argument called `count` in that recurrence counts jobs;
it does not shorten the next job's source horizon.

The source reset is explicit, not inferred from an endpoint decoder:

- `nonemptyBase_toSelected_zeroRunAt` starts from the literal seed Base and
  `(Registers.newJob P).clearScan`, at `CTS.zeroPhase P`.
- `selectedNonemptyPendingPrefixAt` appends the current response's sample
  list before recursively processing the completed successor carrier. Its
  successor call uses `finalRegisters.advance` and its conclusion identifies
  the final selected prestate with the named `CTS.iterate`.
- `selectedNonemptySweepToFreshCheckAt` and
  `completeNonemptyTerminalJobRawAt` add the final response after that prefix.
- `handoffFuelConfigurationsAt` resets to `Registers.newJob` and rebuilds the
  environment from the original `bits` for the next job.

It follows that each job at stage `h` executes response prestates
`c_0,...,c_(h-1)` in order. Stages through `r` never execute response `r`.
The first job of stage `r+1` does execute it, after precisely `r` earlier
responses. That is the claimed first target response.

The optional index formula also agrees with the source definitions:

```text
firstAccept = B(r+1) + 3r + 10 + J(r+1),
B(1)=1, and B(h)=K(h-1) for h>1.
```

`positiveStageConfigurationsAt_length` is `3*(h-1)+10`;
`handoffFuelConfigurationsAt_length` is `2*h+6`; the first job has cost
`J(h)`. In the all-nonempty branch every marker cost is zero. The total stage
cost cross-check is the identity

```text
3*(h-1)+10 + (h-1)*(J(h)+2*h+6) + J(h)
  = (h+1) + h*(2*h+6+J(h)),
```

whose right side is `ExactCheckpointRun.stageCost` after unfolding
`jobsCost`. The exceptional `B(1)=1` accounts for the sole generator staging
contraction. Omitting that exception would give a one-sample error.

## 3. Sample coverage uses exact chains, not just endpoints

The theorem type `PositiveStages` alone would not prove the new event
invariant. In particular, public checkpoint rejection is unrelated to
whether a noncheckpoint tree contains `F17`. The composition correctly lifts
the actual construction bodies and retains generated ancestry while doing so.

The required strengthened invariant includes the completed outer zipper,
not merely the active carrier. It begins with the empty zipper. Each job
extends it using the actual `freshContinuationParents` of its final response;
each stage retains that generated zipper. Thus the proof never obtains
arbitrary audit syntax from an unrestricted `CompletedParents` or
`ReachableAudit.Holds` constructor.

The inspected nonempty branch lists exactly these mutating operations:
generator prelude; CLOCK; launch; positive and zero FUEL; selected C4; the
three FRAME rows; route contractions; appender contractions. These are the
cases of the reviewed Local-origin proof. In particular:

- `normalResponse_exactPairedMutationChain` is constructed directly from
  `normalResponse_exactPositionedMutationChain`, so the paired root list and
  the registered occurrence cursors belong to the same execution.
- `pendingNonemptyCycleTrace.returnToDown` and the subsequent descent are
  `ZeroMutationRun` witnesses.
- `selectedFreshNonterminalJobAt` appends an empty mutation list from
  `freshReturn_toCheck_exactMutationChainAt`.
- `selectedFreshTerminalRawSegmentAt` appends
  `SchedulerRootContinuation.freshReturn_exactMutationChain`, also with no
  mutation after the completed response.

There is consequently no unclassified contraction hidden in a guard, return,
or next-stage entry in this branch. C4 uses the selected canonical occurrence
and the same literal post-deletion carrier supplied to FRAME.

The ordered exact-chain induction in the composition is valid. For a
`next` constructor, `SchedulerBound.seekMutation_bound` and
`FiniteController.advance_eq_of_seekMutation` identify its head with the
persistent run's next contraction sample. Induction identifies every later
entry with the corresponding sample index. A `done` constructor contributes
no sample. This is the all-entry version of the inspected proof of
`SchedulerTraceAlgebra.ExactMutationChain.contractionRun_eq_last`; it does
not assume that set membership establishes chronology.

`RawStageSegment.first` and `.extend` concatenate these exact lists from the
literal encoder. The `PositiveStages.horizonLower` field gives `h<=K(h)`,
so arbitrary finite samples are covered by choosing a sufficiently large
all-nonempty horizon. Sample zero is handled by the encoder's lack of H6.

## 4. The first witness reads the correct frozen suffix

`SchedulerCycle.SelectedResponseTrace.targetDecode` concerns the literal
deleted carrier `V`, not the mutable completed accumulator. For the selected
prestate `(p,b::u)`, it supplies

```text
CarrierDecoder.decode? P A.tree w continuation admissible V = some u.
```

The normal-response label is the old phase and selected bit:
`SchedulerNestedResponse.scannedRegisters_coherentAt` retains `p`, while
register advance occurs for the next response. Clock-exit admissibility is
explicitly supplied by `Dovetail.clockExit_admissible` in the complete-job
constructors.

`CheckpointRun.decodeCarrier?_of_decode` applies to exactly this equation and
returns

```text
CheckpointDecoder.decodeCarrier? P A.tree V = some u.
```

Its proof uses `pathDecodes_to_termOnly`, including the parser-disjointness
facts needed for the ordered public grammar. Therefore this is a proved
seed-free decoder bridge, not an instruction to drop the parameters of a
different function.

The reviewed occurrence lemma places `V` at `LLLR` and preserves that entire
subtree under the registered changes. At the first accepting sample an F17
witness cannot originate in an earlier completed target response, because
that earlier sample would itself have accepted. Every witness there therefore
has the just-completed response's suffix `u`. Prepending one reconstructs
exactly `c_r.data`; restoring the fixed 17 zeroes then invokes the existing
UT19 prestate reader.

This establishes the first-preorder-witness readout even if more than one
matching occurrence exists. No uniqueness assumption and no search for a
convenient payload are required. There is also no need to prove that a target
audit remains fresh forever after the first acceptance.

## 5. The transferred selector and the controller contract coincide

`RootResetFiniteAllInputsTraceAgreement.termOnlyPath_eq_persistentPath`
quantifies over every sample index.
`SchedulerInvariant.SampledGood.uniformCertificate` in `SchedulerDecoder`
explicitly sets its encoder to
`generator (compileActions P A.tree) w`, closing the encoder identity.

The selector/contract seam is also exact. After unfolding the finite-priority
wrapper, both `RootResetReadonlySelector.selectStep?` and
`RootResetContractProjection.projectedStep?` are the same match on the
contract's `select` result: normal gives `none`; a redex gives `some target`.
The all-input root-start, finite-control, linear-in-term-size bound and
one-contraction conclusions consequently apply to the selector used by the
trajectory theorem. The stopping-time function is an interpreter bound;
it is not persistent invocation state. `InterInvocationState` is `Unit`.

Whole-tree equality transfers both the regular descendant predicate and its
current-tree reader, including first acceptance and the preorder witness.
An additional equality of controller cursor paths is unnecessary. The
upstream normal-mode register and finite label-query invariants are internal
dependencies of the all-sample equality, not missing caller hypotheses of
this new lift.

## 6. What this review did and did not verify

I independently checked all 33 supplemental source files against their
recorded pinned Git blob IDs. One matched byte-for-byte; the other 32 matched
after removing exactly one cache-added terminal LF. I inspected the relevant
declarations and construction bodies, including the additional read-only
selector and scheduler-decoder definitions. A small independent
standard-library calculation recovered target leaf index 35 and route
`0100011` from 76 phase-major leaves paired in adjacent rounds. It also checked
the displayed stage-cost identity for horizons 1 through 100 and several
arbitrary job costs; the algebra above establishes the general identity.

No upstream code was executed, no software was installed, and no Lean proof
or imported dependency closure was replayed. Source identity is not kernel
verification. No production file was changed and no new runtime test of a
large UT19 S trajectory is claimed.

The inherited premises are now separated correctly:

- For the exact pinned definitions and the source nonempty-prefix domain,
  the new written lift supplies generated-stage coverage, response labels,
  recomputation ordering, and first-event chronology.
- Imported all-sample equality supplies transfer to the exact finite
  root-reset selector. The public decoder theorem supplies the audit bridge.
- The previously reviewed Local-origin and source/UT19 invariants remain
  substantive mathematical inputs; this review does not re-prove them.
- All-input equivalence of the repository's Python encoder, selector, and
  static-code factories remains a separate reproduction obligation.
- Initially-empty inputs, first-empty stages, and arbitrary later samples
  are outside the new annotated lemma. Their absence from this proof does
  not limit the stated compiled-source first-event result.

The full pinned source links and exact theorem names are collected in the
[composition's source index](cts-event-transfer.md#pinned-source-index).

## 7. Consolidated-theorem integration check

I also reviewed [the consolidated theorem](universality-theorem.md), at SHA-256

```text
22f28945d048731ea5ff2b33f2b1caea25624710fc76a18077ba88767192074e
```

**Scoped signoff:** its quantified statement does not strengthen the component
results beyond the written composition reviewed above. In particular:

- The total mathematical decoder explicitly rejects when no F17 exists and
  uses current-input-size-derived sufficient limits. Practical default-cap
  refusal is not silently treated as either a result or a halting decision.
  It also rejects malformed payloads and invalid final-coordinate arithmetic.
- The selector claim on arbitrary finite S trees follows from the fixed
  contract together with `RootResetContractProjection.none_iff_normal`:
  nonnormal inputs receive exactly one contraction, and normal inputs receive
  none. The stronger assertion that every encoded sample has a successor is
  separately supplied by all-sample trajectory agreement.
- The controller, event pattern, carrier/result grammar, and numerical output
  coordinate are fixed independently of the source machine and input. The
  varying source data enters only through the initial syntax. Decoder and
  controller costs are measured against their current finite input, not
  against the original source size or its eventual running time.

The consolidated document preserves the distinction between a written
mathematical theorem, inspected upstream formal sources, pending local kernel
replay/mechanization, and the separate Python reproduction obligation. No new
execution or broader source-simulation audit is asserted by this integration
check.
