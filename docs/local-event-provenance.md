# Generated Local origins and frozen event audits

6 October 2026. This is a mathematical proof for the **literal construction
scripts and their registered contexts**. The fixed-scheduler interface and
implementation correspondence are stated separately below. The construction
and the source lemmas are due to Cinematic Strawberry, commit
`85a867988442fc423279341200f81634a1e65582`. The occurrence argument here is an
additional consequence, not an upstream theorem with a renamed conclusion.

## 1. The useful invariant is a reserved head prefix

Write application left-associatively and put

```text
b = S S,  h = b S,  H = b h.
```

A fresh Local, including an unfinished one, is

```text
X = H V D (S W A_s) (K A_k).
```

Its head has exactly six arguments, whose first two are `S,h`. Call this
the **H6 signature**. Every instance of `F17` has this signature. Neither
recognizing `H` in static code nor recognizing an arbitrary six-argument
term is enough.

For a construction-created shell, retain a proof-only birth label, initially
the label of the response script being executed. This annotation is not
stored in the S term, finite controller, or observer. Record its creation
snapshot `V` as well. Copies inherit the annotation; changing a registered
accumulator or continuation does not change it.

Here and below, a *construction trace* starts at the literal encoder and uses
the actual CLOCK/FUEL/FRAME/route/appender/C4/COMMIT scripts, with their
registered occurrence contexts. In particular:

- A working whole carrier is a generated Base, fresh Local, or marked Local.
  Its arity is five or six. Appender accumulators are live wrappers around
  such a carrier.
- C4 follows the Base queue, Local accumulator, live predecessor, and
  tombstone predecessor edges. It does not reduce a history/audit sibling.
- A completed outer Local is entered only at `RL`; a pending frame is
  entered at `R`. Generated continuations are the literal clock exits.
- A route is the script's fixed route, and an appender keeps its actual
  remaining-word and history-list indices. An independent-hole match is
  not substituted for these generated-stage hypotheses.

These assumptions describe operations and syntax, not the desired event
conclusion. They are essential: the permissive public grammar alone is too
weak, as Section 5 shows.

### Lemma 1: H6 shell birth and inheritance

In a construction trace, every H6 occurrence is the root of a fresh response
shell, or an unchanged copy of such a root. A new root with this signature
can first arise only at the third FRAME contraction. Subsequent changes to
that shell occur in its registered dispatcher/accumulator or continuation;
they preserve its recorded response label and snapshot, except that COMMIT
removes the fresh signature.

**Proof.** Induct on native contractions, tracking occurrences rather than
equal subterms. A contraction has three kinds of potentially affected
occurrence: newly assembled contractum nodes, copied argument occurrences,
and rebuilt ancestors of the contracted occurrence. Copies inherit their
annotations. For the other two kinds use the following exhaustive head check.

1. **Initial literals, CLOCK, launch, and FUEL.** Static `H` itself has arity
   two. All static dispatcher and appender code has arity at most two; seed
   cells have arity three. A positive numeral is `b C_m`, with second spine
   argument `C_m`, never `h`; `C_0` has first argument `b`, not `S`.
   Clock wrappers have first argument `C_m`, not `S`. The new FUEL forms
   headed by `S` have first argument `E`, `b E`, or the clock exit `B`, none
   of which is `S`. The positive-FUEL pending residual is additionally
   `E B X = S D B X`, where `E=S D`; it has arity three and `D` is an
   application, hence also differs from `S`. The other FUEL head is `b E`, with second argument
   `E`, not `h`. Adding the displayed fuel arguments cannot change either
   discriminator. The final Base inherits its head from the generated
   clock exit `B`, which also lacks the `S,h` prefix. Its queue mutation
   changes neither that head nor the arity-three direct alpha field.

2. **FRAME.** The first residual `(D V)(B V)` has first argument `Act`;
   the second `((Act V)(Seed V))(B V)` has first argument `H`. Neither is
   `S`. The third contraction is exactly
   `Act V -> (H V)(A V)`, at `LL` of the second residual. The two retained
   parents supply the seed and continuation fields, yielding precisely
   `H V (A V) (Seed V) (B V)`. This is the one new H6 shell, with the
   response script's route/label and the actual whole-carrier snapshot
   `V`. Its shorter H-headed left prefixes have arities three, four, and
   five; they are not additional H6 occurrences.

3. **Route activation.** `Chosen(V,Y) = S V Y` has first argument `V`,
   which is a whole carrier and hence not `S`. A dormant compiled call
   has first two arguments `S,a`, where `a` is either `PI`, a Push routine,
   or the fork `S F_L F_R`. None is `h`: `PI` has arity one, Push's first
   argument is an application, and a fork's first argument is the compiled
   child `F_L`, not `S`. Fork application can add arguments but cannot
   change this prefix. New H6 descendants can therefore only be copied
   descendants of `V`; the enclosing shell keeps its identity.

4. **Appender steps and histories.** Push code, the intermediate
   `S N X (L_i X)`, and the final `PI` spine all have first argument other
   than `S`: respectively `S N`, `N`, and `b`; `N` is never `S`.
   Appending right-hand history arguments preserves that discriminator.
   Live wrappers have second argument `v_i`, not `h`. The only less
   immediate new application is a history `X (L_i X)`. If `X` already
   has a live wrapper, this has arity four. Otherwise `X` is a whole
   carrier. A fresh `X` has arity six, so the new application has arity
   seven and its H6 left child is the old shell itself. A Base lacks the
   reserved prefix. A marked `X` has first argument its creation snapshot,
   of arity five or six, and consequently also lacks that prefix. Thus a
   history cannot create a counterfeit H6 root, including the dangerous
   arity-five-to-six case.

5. **C4 and its complete ancestor path.** The replacement
   `L_i Y -> S Y (v_i Y)` creates only arity-one/two prefixes and exact
   copies of `Y`. Along the registered path, live/tombstone contexts have
   fixed arity three/two, Base contexts have the non-H prefix above, and
   action/route contexts have the discriminators just checked. A Local
   ancestor changes only its accumulator occurrence inside the dispatcher.
   Its H6 skeleton, route, label, history count, and halt audit stay fixed.
   This includes old Locals inside a working carrier, not just outer
   continuation layers.

6. **COMMIT.** Replacing `H V` by `S V (h V)` changes the enclosing fresh
   Local from arity six to five. Its first argument is now the whole
   carrier `V`, not `S`. The newly formed `h V` has arity three. Copies
   inside `V` are unchanged. No H6 root is created.

7. **Pending and completed outer contexts.** Pending parents have head
   arity three and do not extend the child's left spine. A completed
   Local's continuation replacement leaves its own dispatcher and halt
   field fixed. The intervening continuation call `K A_k` deserves a
   separate check: it can become H6 only if its changing child `K` has
   the reserved prefix and arity five. Here an **active endpoint** means the
   whole term substituted into a completed/pending outer-context hole, not
   the instantaneous cursor focus. A cursor can visit an H-headed arity-five
   left prefix inside an existing fresh Local; its sixth-argument parent is
   that same Local, rather than a new `K A_k` application. No generated whole
   endpoint has the dangerous combination. Fresh endpoints have arity six; marked and Base
   endpoints lack the prefix; the arity-five FRAME residual has first
   argument `H`; all CLOCK/FUEL/pending endpoints were checked above.
   Hence a rebuilt parent cannot manufacture a match across the hole.

Cursor-only commands change none of these terms. These cases include all
new contractum nodes and every rebuilt ancestor, completing the induction.

### Corollary 1: label-specific completed-pattern provenance

For a fixed dispatcher leaf `lambda`, let `F_lambda` be its completed fresh
Local pattern, with the exact route and action-history count. Every match in
a construction trace descends from a response completed with label `lambda`.

**Proof.** Lemma 1 gives the shell birth. Before route completion, the route
parser rejects. After route completion, the route determines its original
label uniquely, even when different leaves have equal action code. An
unfinished nonempty appender has first spine argument different from `b`,
whereas a completed action begins with `PI = S b` and has the exact history
count. Thus the born shell first satisfies a completed pattern at its final
response mutation, with its birth label. Accumulator changes preserve the
fixed completed dispatcher skeleton. Continuation changes and copying also
preserve it. COMMIT removes the fresh alternative. No non-completion step
can change a different label into `lambda`.

For UT19, `lambda=(17,1)`, route `0100011`, and history count 19. This is
exactly `F17`, not merely the language of some equal appender code.

## 2. The frozen audit lemma is stronger than accumulator preservation

Let `X` be a construction-created fresh Local whose snapshot was `V`.
Suppose a later occurrence is obtained by copying `X`, by a canonical C4
inside its selected accumulator, or by replacing its active continuation.
At every fresh descendant instance,

```text
subterm(X, LLLR) = V.
```

**Proof.** Expand the shell: `LLLR` is the argument of `H V`. A Local's
accumulator path starts `LLR`, so it is disjoint from `LLLR`. A continuation
path starts `RL`, also disjoint. Context replacement therefore preserves
the entire audit subtree, not merely its decoded word. Copying preserves
that equality. For nested canonical C4, induction through the actual Local
contexts gives the same result for each enclosing Local. Off-path Locals,
including those in tombstone audits and retained action histories, are
unchanged or copied exactly. New FRAME/route/appender wrappers never select
inside a pre-existing halt audit. COMMIT, if selected for this shell, changes
its status and removes it from the fresh-language claim; it does not license
an arbitrary reduction inside its audit.

This is an occurrence theorem under the selected construction contexts.
It does **not** say that arbitrary S reduction preserves an audit. The audit
contains redexes; reducing one deliberately would invalidate the premise.

For the UT19 target the newly completed successor is nonempty because the
appendant has 19 bits. It therefore is not immediately committed. While it
remains the current response, the next ordinary action is either continuation
entry or one C4 followed by pending-frame handoff. Later it is an inner
carrier layer or a frozen outer/history copy, never the current shell of an
EMPTY response. Thus the born target's fresh audit is retained by this schedule.

## 3. Exact source lemmas supporting these proofs

Use the following pinned files, with this common prefix:

`https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/`

- [ReachableAudit.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/ReachableAudit.lean): `SnapshotRoute` (28), `actionResponse` (135), `SnapshotDispatchAt.reduceAccumulator` (267), `Layer` (322), `Layer.reduceAccumulator` (371), and `Holds` (493). Their types distinguish the immutable creation snapshot from the current accumulator. `Layer.reduceAccumulator` alone is an existential lifted reduction; it must not be cited as arbitrary-strategy safety.
- [CanonicalTraversal.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/CanonicalTraversal.lean): `localContext_plug` (511), `SelectedFront` (1327), `SelectedFront.delete` (2261), and `Decodes.deleteCanonical` (2800). In the `inside` and `segment` deletion cases the same snapshot, halt state, route context, and label are reconstructed around the changed current/segment context. The last theorem supplies the literal unique selected address and replacement equality. This supplies the occurrence information absent from a bare `StepsN` endpoint assertion.
- [SchedulerResponseInvariant.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerResponseInvariant.lean): `RouteMutation` and `.parser` (28, 86), `ActionMutation` and `.parser` (175, 202), `ResponseRootMutation` (273), `responseEntries` and `responseEntries_spec` (652, 690). These enumerate the unfinished and final response samples. `ActionMutation.done_eq` (239) preserves the actual order of all history arguments.
- [SchedulerCycle.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/SchedulerCycle.lean): `SelectedResponseTrace` (218) carries the selected front, literal post-deletion carrier, exact run, its suffix decode, and the completed successor decode. `normalResponse_exactPositionedMutationChain` (3416) retains the contraction cursors, rather than just a list of equal erased roots.
- [RootResetOrderedCarrier.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetOrderedCarrier.lean): `selectedResponseTrace_preserves` (400) proves the deleted carrier has the old phase and deleted head bit, and the completed response advances the phase and decodes the CTS successor. [RootResetGeneratedCarrierLabels.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetGeneratedCarrierLabels.lean), `selected_response` (26), joins those facts to the finite label query; its EMPTY cases use bit false.
- [PrimitiveLocalResponse.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/PrimitiveLocalResponse.lean): `run_execute` (69) returns precisely `LocalResponse.completed`, with the actual supplied post-deletion carrier in its halt audit.
- [RootResetFiniteAllInputsTraceAgreement.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFiniteAllInputsTraceAgreement.lean): `termOnlyPath_eq_persistentPath` transfers properties of the entire current tree. It does not itself prove the new H6 invariant.

`Research/RootResetReachableStageGrammar.lean` supplies a marked-only proposed
grammar without a scheduler-closure assertion, so it cannot replace the
construction-trace premise. The public checkpoint theorem likewise
classifies checkpoints rather than arbitrary descendant matches.

## 4. Event and output consequence, with the transfer boundary visible

Assume the exact generated-script/CTS correspondence and fair stage coverage
of the pinned construction. Corollary 1 then implies

```text
some current S tree has an F17 occurrence
    iff
some CTS prestate has phase 17 and head 1.
```

For soundness, trace a matched shell to its completed response; the normal
response label theorem gives that CTS prestate. EMPTY cannot have bit one.
For completeness, a sufficiently long finite recomputation job executes the
transition, and its final appender contraction creates the fresh pattern.
Its response cost is `3 + 2*7 + 1 + 2*19 = 56` contractions after the
post-deletion pending-frame entry. C4 itself is one additional contraction.

At creation, `SelectedResponseTrace.targetDecode` gives
`DecodeCarrier(V) = suffix`. The frozen-audit lemma therefore gives the
current-tree readout `1 ++ DecodeCarrier(X[LLLR])` at every retained fresh
instance from that birth, even if its current accumulator has since changed.

At the first accepting sample, a match cannot be merely a copy of an earlier
match. It is a completion. Each recomputation job executes a prefix from the
original seed in order; reaching a later source event would already have
completed the earlier one. Consequently the first accepted sample supplies
the first source event and the UT19 prestate reader applies. This argument
does not license choosing an arbitrary much-later event's output.

The observation predicate itself is still just the finite current-tree
pattern language; no construction annotation or source evaluation is part
of the algorithm. Whole-term trajectory equality transfers this extensional
statement to the upstream root-reset selector. Applying it to this
repository's native selector additionally requires the port-correspondence
argument; the present document does not silently replace that proof with
bounded testing.

## 5. A concrete obstruction to a tempting shortcut

`ReachableAudit.Holds` is stronger than the public grammar, but is not a
certificate of unrestricted descendant provenance. Let `Z` be any fabricated
instance of `F17`, for example instantiate every wildcard by `S`. Set

```text
Q = tombstone(0, S, Z) = S S (v_0 Z).
M = MutableBase.mutableBase(actions, seedBits, continuation, Q).
```

`CellSpine.Decodes Q []` follows from the empty predecessor, because a
tombstone's audit is independent and ignored. Therefore `ReachableAudit.Holds.base`
certifies `M`, yet `M` contains `Z` in that audit. No source event or generated
creation history was assumed. Even requiring an admissible generated clock
exit as `continuation` does not remove the example.

Thus a proof by induction on `Holds` that simply declares every audit safe
is invalid. Lemma 1 uses an induction on the actual **generation operations**;
the C4 case introduces an audit by copying its actual predecessor. It never
uses the unrestricted tombstone-audit constructor to introduce new syntax.
This is why keeping the generated occurrence history matters.

## 6. Scope and regression checks

The H6 and frozen-audit arguments apply to the generated-script interface.
Their native-implementation transfer uses the premises in Section 4. The
observer remains a regular descendant-pattern language, and numerical output
is read at its first accepting sample. Pinned source declarations support the
argument; their kernel replay is tracked separately.

Focused checks in `tests/test_local_event_provenance.py` passed on 6 October
2026 (three tests, 0.154 seconds, under a 60-second/512-MiB process limit).
They check H6 birth sites, frozen-audit identity, and stable completed labels
through the existing 85-contraction `101` fixture; a direct accumulator
contraction; and an actual fabricated UT19 `F17` inside a decodable empty
Base's tombstone audit. These are regression checks of the proof's difficult
cases, not a substitute for its induction or the implementation transfer.
