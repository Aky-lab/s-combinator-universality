# From exact CTS stages to the first F17 event

6 October 2026. This is a **written composition proof**, based on inspected
pinned source declarations and their construction bodies. It is not a local
Lean elaboration, dependency replay, or execution of the upstream software.
The imported S construction is Cinematic Strawberry's at commit
`85a867988442fc423279341200f81634a1e65582`.

The useful strengthening is a **finite nonempty-prefix theorem**. The compiled
UT19 source is nonempty until its first designated event and stays nonempty
forever if that event never occurs. Therefore the first-event universality
argument needs no generated EMPTY-stage induction. This is a restriction on
the required proof, not an assertion that arbitrary CTS inputs never empty.

## 1. Exact mathematical construction

Fix the ordinary binary CTS program `P` of period 38 obtained from the UT19
one-hot construction. Define, using the pinned definitions themselves,

```text
A       = WeakPathUniversality.canonicalDispatcher P
E(w)    = generator (compileActions P A.tree) w
S_P     = RootResetFiniteAllInputsTraceAgreement.selector P
C_P     = RootResetFinitePrioritySelector.selectorContract P A
T_w(n)  = RootResetTermOnlyTransfer.run S_P n (E(w)).
```

`canonicalDispatcher` is `BalancedActionTree.dispatcher`; this has 76
phase-major leaves, false before true, combined by adjacent-pair rounds without
padding. Its `(17,true)` leaf has route `0100011`. `F17` is the exact completed
fresh-Local pattern for that route and its 19 history arguments, with independent
holes as in [the event audit](ut19-s-event-audit.md). Let `H(T)` mean that some
occurrence in `T` matches `F17`.

The mathematical decoder locates the first preorder `F17`, extracts its `LLLR`
audit `V`, applies the seed-free public carrier grammar to `V`, prepends `1`,
and applies the phase-17 UT19 result grammar. The source-machine result then is
`(x_1-3)/2`. These are the algorithms and bounds in
[the current-tree reader proof](s-event-readout.md) and
[the auxiliary-interface bounds](auxiliary-interface-bounds.md).

There is **no Python encoder or selector in this definition of `T_w`**. Universal
correspondence of the independent Python port is consequently a reproduction
claim, not a hypothesis of this mathematical construction. Similarly, define
the mathematical event pattern from the pinned fixed syntax, rather than from
an unproved claim that a Python factory produces it.

### Imported totality and trajectory facts

The exact types have the following scope.

1. `RootResetFiniteAllInputsTraceAgreement.selectsEveryContractionRun` quantifies
   over every `program : CTS.Program`, `layout : ActionDispatcher program`,
   `bits : List Bool`, and `index : Nat`. It states that the finite root-reset
   selector sends the erased persistent sample at `index` to `some` of the
   erased sample at `index+1`. It has no caller-supplied stage or label premise.
2. `termOnlyPath_eq_persistentPath` identifies `T_w(n)` with the term of
   `WeakPathUniversality.finiteCTSWeakPathUniversality P` at **every** `n`, not
   merely at public checkpoints. Its encoder is definitionally the displayed
   generator, through `SampledGood.uniformCertificate` and
   `ControllerProjection.UniformCertificate.uniformRealizes`.
3. `RootResetFinitePrioritySelector.selectorContract P A` supplies a finite
   primitive controller. Its invocation always begins at `Cursor.atRoot T`
   with the same start control; `Contract.InterInvocationState` is `Unit`.
   `RootResetContractProjection.invocation_bound` gives
   `stoppingTime(T) <= C_P.coefficient * (T.size+1)`. The coefficient is a fixed
   positive natural number determined by `P,A`, independent of the input.
   `some_result` gives exactly one native occurrence contraction; `none_result`
   gives zero contractions and an address-normal term. Selector and contract
   projection are definitionally equal: `RootResetReadonlySelector.selectStep?`
   and `RootResetContractProjection.projectedStep?` use the identical match on
   the contract's `select` result. On the encoded trajectory item 1
   supplies `some` at every invocation.

Thus neither arbitrary-input selector totality nor root-reset/persistent
agreement is a missing mathematical premise in the pinned source. Their local
verification remains distinct from inspecting these declarations. Whole-term
equality in item 2 transfers any current-tree observer and decoder. It is not
necessary additionally to prove equality of the two controllers' cursor paths.

In particular, `RootResetOrderedCarrier.NormalInvariant` and the finite
phase/bit-query lemmas are upstream dependencies used to establish item 1.
They need not be re-established as separate hypotheses of our event lift.
For the persistent trace, the response's semantic bit, suffix, and
`RegistersCoherent` evidence already identify its source prestate.

## 2. What the stage theorems do, and do not, quantify over

Write `c_i = CTS.iterate P i (CTS.initial P w)` and
`K(h) = ExactCheckpointRun.checkpointTime P A w h`.
The pinned CTS iterate totalizes empty queues, but agrees with ordinary CTS
at every nonempty prestate.

`SchedulerRecurrence.positiveStages P A w offset` constructs
`Nonempty (PositiveStages P A w (offset+1))`. A `PositiveStages` object carries
an `ExactMutationChain` from the literal initial configuration, its complete
ordered list of post-contraction configurations, a length equal to `K(h)`,
and `h <= configurations.length`. This is premise-free. Its underlying
`rawStageAt` explicitly divides into initially empty, finite all-nonempty, and
first-empty cases. `initialGood` and `exactCheckpoint` are derived from these
finite constructions; they are not additional simulation assumptions.

However, `PositiveStages` does not itself carry an origin annotation for every
descendant `H6`, nor does `WeakPath.Realizes` mention `F17`. Its decoder
`acceptsOnly` field concerns the **public checkpoint decoder**, not our event
language. We must lift the actual constructive stage proof, rather than infer
event provenance from those weaker conclusion types.

For this lift we use `SchedulerStageAssembly.allNonemptyRawAt`. Its explicit
source premise is

```text
for every i <= h, c_i.data is nonempty,
```

where its argument `fuel` is `h-1`. It builds the stage's literal sample list as

```text
phaseConfigurations ++ nonfinalConfigurations ++ terminalConfigurations.
```

The phase list has `3(h-1)+10` samples. Then `h-1` nonfinal jobs and one
terminal job run. **Every job starts from the same original word `w`, phase
zero, and executes precisely the responses for `c_0,...,c_(h-1)`, in that
order.** The derivation of this last statement, including intermediate
samples, is given next.

## 3. The labelled nonempty-prefix lemma

### Statement

Assume `w` is nonempty and `c_i.data` is nonempty for `0 <= i <= h`, with
`h >= 1`. There is an exact generated scheduler prefix through stage `h`
such that:

1. It lists every native contraction sample from the encoder through `K(h)`,
   in order. It uses precisely the registered construction contexts of
   [the Local-origin proof](local-event-provenance.md).
2. In stage `g`, for every `1 <= g <= h`, each of its `g` jobs completes the
   responses indexed `i=0,...,g-1` in that order. If
   `c_i = (p, b :: u)`, that response has label `(p,b)` and a creation snapshot
   `V` with
   `CheckpointDecoder.decodeCarrier? P A.tree V = some u`.
3. Every completed fresh labelled Local occurrence in this prefix inherits
   its label and snapshot from one of those responses. Each newly born
   response shell first matches its own completed-label pattern at that
   response's final native contraction. Older completed shells with the same
   label may already exist; global firstness is proved separately in Section 4.
   Copies and the registered accumulator/continuation changes preserve the
   associated creation audit.

The origin annotations in item 3 are proof-only. They are not runtime
registers, encoded data, observer state, or input to the selector.

### Proof: ordered exact chains

An `ExactMutationChain machine terminal before Q` has only two constructors:

- `done` records a zero-mutation run to `terminal` and an empty list;
- `next` records a successful executable `seekMutation` from `before` to the
  head sample, followed by the tail chain.

Consequently, if `before` is persistent sample `s`, its list entry `j`, indexed
from zero, is persistent sample `s+j+1`. Prove this by induction on the chain.
For `next`, `SchedulerBound.seekMutation_bound` converts its successful search
to the scheduler's fixed bound; `FiniteController.advance_eq_of_seekMutation`
identifies that same first mutation with `system.next before`. The successor
equation for `contractionRun` identifies the head sample. Apply the induction
hypothesis to the tail. The `done` case has no entry to check.

This is the indexed strengthening of the same induction written in
`SchedulerTraceAlgebra.ExactMutationChain.contractionRun_eq_last`; the existing
`PhysicalMarkerExclusion.exactChain_contractionRun_mem` alone gives membership
and would not by itself justify chronology. Appending chains appends their
ordered samples. A zero-mutation bridge changes no S term and adds no hidden
contraction sample. We use this induction below whenever a constructor composes
an exact chain.

### Proof: one normal response and its audit

`SchedulerCycle.SelectedResponseTrace` carries the actual selected front
`b :: u`, the canonical deletion contexts, the literal post-deletion carrier
`V = deletedCarrier b outerContext innerContext`, and the equation

```text
CarrierDecoder.decode? P A.tree w continuation admissible V = some u.
```

It also gives the completed carrier's decode as the ordinary CTS successor
word. `SchedulerNestedResponse.scannedRegisters_coherentAt` preserves the
old phase while setting the selected response bit to `b`; hence the response
label is `(p,b)`, not the successor phase. Advancing after the response gives
the next phase and clears the normal scan registers.

The snapshot is readable without those semantic parameters:
`CheckpointRun.decodeCarrier?_of_decode` has exactly the quantified implication

```text
CarrierDecoder.decode? P tree bits continuation admissible term = some decoded
  implies
CheckpointDecoder.decodeCarrier? P tree term = some decoded.
```

Apply it to the trace's `targetDecode`. Its proof goes through
`pathDecodes_to_termOnly`, so this implication respects public parser priority
and the repeated Base-continuation equality; it does not simply discard a
runtime argument to a source-dependent decoder.

`selectedPendingSegmentAt` constructs the selected C4 sample followed by the
response list. `normalResponse_exactPositionedMutationChain` identifies every
response contraction with its actual script position and occurrence cursor.
`normalResponse_exactPairedMutationChain` pairs the same list with
`responseEntries`, and `responseEntries_spec` gives the corresponding
`ResponseRootMutation` constructor for every entry. The enumeration is exactly
three FRAME rows, then the indexed route rows, then the indexed appender rows.
`responseEntries_finalFlags` and `ResponseSamplePairs.terminalDecomposition`
identify its unique final entry as the completed Local with snapshot `V`.
The route/action parser theorems exclude an earlier completed match in that
new shell. An empty appendant completes at the route leaf; a nonempty one at
the final second Push contraction. For F17 it is the latter.

The [reviewed occurrence lemma](local-event-provenance-review.md) now applies
to these literal rows and contexts. It handles new contractum nodes, copied
argument occurrences, and rebuilt ancestors, including old Locals inside the
working carrier and off-path audits. It does not need any claim that the
carrier or its audits are free of old Locals.

### Proof: a bounded job

The base of `completeNonemptyJobAt` uses
`nonemptyBase_toSelected_zeroRunAt` with `Registers.newJob`, the literal
`baseCarrier` for `w`, and phase zero. Thus the first response is for `c_0`.

For the inductive step, `selectedNonemptyPendingPrefixAt` constructs
`firstConfigurations ++ tailConfigurations`. It applies
`selectedPendingSegmentAt` for the current response; then
`pendingNonemptyCycleTrace` supplies the next selected carrier and
`nextResponse`. Its code explicitly uses the completed previous response as
the new source, `finalRegisters.advance`, and the successor bit/suffix.
Its recursive conclusion identifies the final source configuration with the
corresponding `CTS.iterate`. The return/descent bridge is a `ZeroMutationRun`.
This proves the ordered response list by induction, not just its endpoint.

For a nonfinal job, `selectedNonemptySweepToFreshCheckAt` ends in
`selectedFreshNonterminalJobAt`. Its final response has nonempty output, so
the return to the next continuation check has an **empty mutation list**.
The outer zipper is extended by the literal
`freshContinuationParents`; it enters the new shell's continuation at `RL`.
For the terminal job, `completeNonemptyTerminalJobRawAt` uses the same pending
prefix and `selectedFreshTerminalRawSegmentAt`. The final response is again
the last listed sample, and `freshReturn_exactMutationChain` gives the
mutation-free suffix to the next stage's clock source.

All jobs therefore execute their source responses in chronological order.
All appended outer layers are actual completed shells from these jobs. We
retain their origin annotations when extending the zipper. We are not
claiming that an arbitrary inhabitant of the permissive `CompletedParents`
or `ReachableAudit.Holds` type has such ancestry.

### Proof: all contractions of a stage are covered

The exact mutating cases in the inspected all-nonempty constructor bodies are:

| Segment | Literal contraction list | Registered context |
| --- | --- | --- |
| Initial prelude | `initialPreludeConfigurations`, one generator staging contraction | Literal encoder root |
| Clock | `clockConfigurationsAt` and `clockTailConfigurationsAt` | Environment application inside the completed `RL` zipper |
| First launch | `positiveStageLaunchConfigurationAt` | Same active stage endpoint |
| Fuel | `fuelConfigurationsAt`: two positive rows per unit, then five zero rows | Literal pending frames followed by the completed zipper |
| Selected deletion | `selectedC4Configuration` | `CanonicalTraversal.SelectedFront` and its deletion context |
| Response | `normalResponse_exactPositionedMutationChain`, paired with `responseEntries` | Current FRAME/dispatcher/appender, below pending and completed parents |
| Between jobs | `handoffFuelConfigurationsAt`: one launch, then the same fuel rows | Literal next-job clock exit inside fresh `RL` contexts |
| Return and next-stage entry | Zero-mutation exact-chain suffix | Literal continuation entry and cursor-only traversal |

These are precisely the prelude/CLOCK/launch/FUEL/C4/FRAME/route/appender and
outer-context cases already proved in the Local-origin proof. There is no
additional mutation hidden in a return, guard, probe, or continuation handoff:
the exact chains or zero-mutation witnesses above account for them. Neither
COMMIT nor an EMPTY response is used in this nonempty branch.

`SchedulerNonfinalJobs.completeAt` composes a complete job, its launch/fuel
handoff, and the remaining jobs, in that order. Each handoff explicitly resets
to `Registers.newJob` and the original encoded seed. For stage `g`,
`allNonemptyRawAt` sets its count of nonfinal jobs to `g-1` and appends one
terminal job. Its initial phase list is the displayed clock/launch/fuel list.
This proves the `g` jobs, their input reset, and every-sample coverage.

Finally apply `RawStageSegment.first` and `.extend` inductively, retaining the
occurrence annotations on the previously generated prefix and on its outer
zipper. The nonempty hypothesis for a smaller stage follows by restriction.
These exact prefixes have length `K(h)` and start at the literal encoder.
The ordered exact-chain induction identifies them with the actual persistent
contraction samples. The local occurrence lemma transports all annotations
through every listed contraction. This proves all three claims. QED.

## 4. First-event theorem without EMPTY-stage assumptions

Let `lambda=(17,true)` and suppose the CTS input `w` satisfies the following
source condition:

- if no `c_i` has phase 17 and leading bit 1, then every `c_i` is nonempty;
- if `r` is the least such index, then `c_0,...,c_r` are nonempty.

Since the appendant at phase 17 has 19 bits, `c_(r+1)` is nonempty too.
These conditions hold for every compiled source input by the UT19
[no-premature-exhaustion theorem](ut19-simulation-invariants.md) and
[exact-step one-hot lemma](alternating-tag.md).

**Theorem.** The exact root-reset trajectory `T_w` reaches `H` if and only if
the CTS trajectory has a `lambda` event. When the least CTS event index is
`r`, the first accepting S sample is the final response contraction of the
**first job of stage `r+1`**. Every F17 witness at that first sample has a
frozen audit whose public carrier decode is the tail of `c_r.data`.

**Proof, absence.** If there is no source event, every finite horizon is
nonempty. For any S sample `n`, choose a positive horizon `h >= max(1,n)`.
The labelled-prefix lemma covers it because `h <= K(h)`. All possible
completed Local origins in that prefix have labels of source prestates, none
equal to `lambda`. The encoder itself contains no H6, and the occurrence
lemma excludes manufactured matches. Hence `H` is false at every sample.

**Proof, firstness and presence.** Suppose `r` exists. Stages `g <= r` contain
only response indices `i < g <= r`, so no target response. In stage `r+1`,
the first job performs `c_0,...,c_r` in order. Its first `r` responses and all
its earlier scaffolding samples cannot create F17. The target response's
proper FRAME/route/appender prefixes cannot create a completed target either.
Its final contraction creates the completed fresh target Local and therefore
accepts. This is an actual contraction sample even when the job is nonfinal:
public-checkpoint decoder silence at that point does not affect `H`.

At this first accepting sample no witness can descend from an earlier
completed target response, since that earlier sample would already have
accepted. The origin lemma therefore attaches every witness to the just
completed `c_r` response. Its trace gives `targetDecode = some u` for
`c_r.data = 1 :: u`; the public-decoder bridge gives the same `u` without seed
or continuation inputs. The snapshot is at `LLLR`, and the frozen-audit
lemma preserves it. Prepending 1 reconstructs precisely `c_r.data`.

All this reasoning is about the persistent samples identified by the exact
chains. Apply `termOnlyPath_eq_persistentPath` pointwise to transfer presence,
absence, the least accepting index, the current preorder witness, and its
literal audit to `T_w`. QED.

This proof does not require target audits to remain fresh forever after the
first event. Nor does it claim that an arbitrary later F17 carries the source's
first result. It only uses the current tree at its first accepting sample.

### An optional exact first-index formula

Write `J(h)=ExactCheckpointRun.jobCost P A w h`, and let
`B(1)=1`, `B(h)=K(h-1)` for `h>1`. The source constructors above give

```text
firstAccept = B(r+1) + 3r + 10 + J(r+1).
```

`B` is the stage's starting sample, including the one generator-prelude
contraction in the stage-one case. The next `3r+10` samples are its initial
clock/launch/fuel phase, and `J(r+1)` counts the first complete nonempty job.
There is no marker or other contraction after its last response before the
continuation check. This is a mathematical index identity; no encoder,
controller, detector, or decoder computes `r` or uses this formula.

## 5. Composition with the machine input and bounds

For a finite source machine and input, the independently proved front end
produces the compact UT19 seed and then `w`. The first-event theorem identifies
halting with the fixed regular language `H` along `T_w`. At its first accepting
sample, the UT19 structural readout gives exactly the nonempty tuple of final
BP2 counters. The front-end theorem proves `C >= 1` and `x_1 = 2n+3` for the
source-machine result `n`, so the fixed first-coordinate map `(x_1-3)/2`
returns precisely `n`. A total defensive implementation rejects an empty
tuple, `x_1 < 3`, or even `x_1`; none occurs at a compiled first event.
The controller, detector,
decoder, program `P`, and dispatcher `A` are fixed over all such inputs.

The numerical composition in [the bounds document](auxiliary-interface-bounds.md)
is consistent with the pinned generator size convention, which counts leaves
and application nodes. `EncoderSize.generator_size_counts_exact` gives fixed
code size plus `16*zeroCount+18*oneCount`. The fixed actions have size 16,489,
so `encoderConstant=16,529`. A one-hot tag word of `q` symbols has `19q` bits
and `q` ones, giving exactly

```text
|E(w)| = 16,529 + 306q.
```

The displayed source bound uses unary expansion of binary input values; its
singly exponential binary-input bound is syntax-only, not a bound on source
running time. The detector's regular transition table is fixed, and the
current-tree reader's sufficient budget is polynomial in current input size.
For the exact controller the imported all-input bound is
`C_P.coefficient*(|T|+1)` microticks per invocation. None of these interfaces
performs unbounded source evaluation.

## 6. Verification status and remaining distinctions

- **Imported, source-inspected proofs:** arbitrary-input finite-controller
  contract; all-input root-reset/persistent equality; premise-free stage
  construction; exact selected-response traces and public carrier bridge.
- **New written proof here:** the labelled finite nonempty-prefix lift,
  exhaustive case propagation through those constructive stage bodies,
  least-event chronology, and the first-audit result composition.
- **Previously written and independently reviewed here:** Local occurrence
  nonmanufacture/frozen-audit lemma, source front end and UT19 invariants,
  regular pattern detector, and bounded structural output reader.
- **Subsequent formal validation:** the imported 423-module dependency closure
  has passed [fresh official Lean kernel replay](formal-replay.md), with exact
  type/axiom probes for the relevant interfaces. The new labelled-prefix and
  first-event composition remains the written proof reviewed here.
- **Still a separate reproduction task:** an all-input equivalence theorem for
  the Python encoder/selector/controller and fixed-code factories. Existing
  finite fixture agreement does not establish it. The mathematical theorem
  above does not require this port theorem.
- **Broader statement not established by this lemma:** label-specific event
  provenance for arbitrary initially empty CTS seeds, arbitrary first-empty
  stages, or unrestricted later samples after our first target event. Such a
  theorem would need the corresponding annotated EMPTY/COMMIT branches. These
  branches are unnecessary for the compiled-source first-event result proved
  here, because the source nonexhaustion theorem discharges the restricted
  hypothesis.

This is a mathematical proof composition to review, not a claim of prize
acceptance or a fresh machine-checking result. The source assertions,
written proofs, and local runtime checks should remain separately reported.

## Pinned source index

All links below refer to the exact commit named above.

- [RootResetFiniteAllInputsTraceAgreement](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFiniteAllInputsTraceAgreement.lean): all-sample selector equality and term-only path equality.
- [RootResetFinitePrioritySelector](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFinitePrioritySelector.lean), [RootResetSelectorContract](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetSelectorContract.lean), and [RootResetContractProjection](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetContractProjection.lean): fixed-root all-input finite-controller contract and one-contraction projection.
- [WeakPathUniversality](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/WeakPathUniversality.lean) and [WeakPath/Interface](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/WeakPath/Interface.lean): generic quantifiers and the exact limits of checkpoint-only conclusions.
- [SchedulerStageAssembly](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerStageAssembly.lean): `allNonemptyRawAt`, `rawStageAt`, `positiveStages`, `initialGood`, `exactCheckpoint`.
- [SchedulerAllStages](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerAllStages.lean) and [SchedulerTraceAlgebra](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerTraceAlgebra.lean): exact whole-prefix lists, their length/lower bound, and operational sample identification.
- [SchedulerNestedPhase](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerNestedPhase.lean) and [SchedulerJobHandoff](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerJobHandoff.lean): exact clock/launch/fuel lists and reset-to-original-seed handoffs.
- [SchedulerCycle](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerCycle.lean) and [SchedulerResponseInvariant](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerResponseInvariant.lean): `SelectedResponseTrace`, positioned and paired script traces, and the complete response residual enumeration.
- [SchedulerNestedResponse](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerNestedResponse.lean) and [SchedulerNonfinalJobs](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerNonfinalJobs.lean): ordered response/job recursion and exact fresh terminal/nonterminal seams.
- [SchedulerRootContinuation](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerRootContinuation.lean) and [SchedulerCompletedContext](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerCompletedContext.lean): literal fresh continuation parents and mutation-free fresh returns.
- [CheckpointRun](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/CheckpointRun.lean#L233-L246): `decodeCarrier?_of_decode`, the precise seed-free audit readout bridge.
- [BalancedActionTree](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/BalancedActionTree.lean), [EncoderSize](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/EncoderSize.lean), and [ExactCheckpointRun](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/ExactCheckpointRun.lean): static layout/size and exact contraction-count definitions.

The supplemental audit retrieved and Git-blob-verified 33 source files at this
pin, in addition to the previously verified Local-provenance sources. A
standard-library check independently recalculated the 76-leaf target route
`0100011` and the arithmetic constants `16,529` and `306`. These checks certify
source identity and finite arithmetic, not theorem validity.
