# Root-reset controller: interface audit

Source-level audit of the candidate package at commit `85a867988442fc423279341200f81634a1e65582`, reviewed 6 October 2026.

## Finite control and persistent state

[`FiniteController.Machine`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/FiniteController.lean#L23-L84) includes a finite list covering every control value. Its transition sees the current control, node kind and incoming side. Commands are stationary updates, single-edge left/right/parent moves, focused contraction or rejection.

The [`Cursor`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/Cursor.lean#L49-L97) is an occurrence-tree zipper with a focus and a parent-frame list. Its depth grows with the current tree. The [invocation contract](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetSelectorContract.lean#L508-L530) resets this cursor to the root and uses the same initial control on every invocation. Inter-invocation state is `Unit`; only the resulting bare term persists.

Thus the finite-state restriction applies to the controller, while the changing tree remains unbounded storage.

## One invocation

The concrete [read-only selector](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetReadonlySelector.lean#L168-L365) has an all-finite-input bound `K*(size+1)` on primitive microticks. It ends in an absorbing terminal and makes zero contractions precisely for a normal term; otherwise it makes one certified contextual S contraction.

The priority pass can decline a term. In that case explicit parent moves restore the root before a complete Euler traversal looks for an ordinary redex. The stopping budget is proved from tree size and does not appear as an unbounded counter in runtime control. The bound concerns one tree walk, rather than the duration of an entire simulated source computation.

## Observation and source chronology

The [marker observer](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFiniteMarkerObserver.lean#L12-L168) runs a read-only priority scan followed by a literal halt-field test. It returns false when priority selection declines. The [tree-automaton agreement](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetMarkerTreeAutomaton.lean#L32-L56) connects it to a finite bottom-up tree automaton on every input tree.

The [fixed computation contract](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/RootResetChallenge.lean#L28-L156) fixes the universal program, selector and readers before receiving a source instance. Its halting event occurs along that selected trajectory, which continues rewriting after the source has halted. The [headline chronology](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/RootResetHeadline.lean#L18-L41) supplies ordered observations for each finite source horizon.

The [all-input agreement bridge](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFiniteAllInputsTraceAgreement.lean#L11-L47) explicitly connects finite-selector output to every contraction sample of the encoded path, with separate empty and nonempty cases.

## Audit outcome and next check

The inspected definitions expose finite control, root reset, exact mutation count and selected-trajectory scope clearly. No concrete mismatch was found among these interfaces. This review inspects declarations and their intended meaning; independent kernel replay is recorded separately when executed.

The next concrete test is to reconstruct the small fixture's selector and compare its chosen occurrence at all 85 contractions. Empty input, priority declines and return-to-root behavior need separate cases. The [native queue replication](queue-replication.md) already supplies a checked term sequence against which those selections can be tested.

## Implemented components

The [restoring pattern compiler](probe-compiler.md) now produces immutable finite tables, with independent exhaustive tests and explicit state/microtick accounting. The [seven fuel endpoint rows](fuel-probe.md) have been transcribed into this model and recover 25 local recorded selections. Active-context traversal and whole-selector priority assembly remain the next integration layer.

Finite [spine walkers](spine-walkers.md) now support strict-child descent and restoring ancestor queries with explicit termination bounds. General ancestor recognition is broader than inverse descent; reconstruction requires the documented uniqueness and boundary conditions. The remaining integration must preserve the source construction's scope guards and priority ordering.
