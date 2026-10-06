# Independent review: Local-event provenance

6 October 2026. Review of [the proof](local-event-provenance.md) and
[the earlier event audit](ut19-s-event-audit.md), based on symbolic cases,
pinned source declarations, and independent standard-library regression checks.

## Verdict and precise scope

**Scoped signoff:** the reserved-prefix argument establishes Local birth,
completed-label provenance, and frozen fresh halt audits for the literal
generated scripts, under their stated registered occurrence contexts. The
symbolic case analysis below establishes the result; the finite tests check
its difficult boundary cases.

Applying this result to the native root-reset trajectory uses the six imported
premises in Section 6, including complete generated-stage coverage and
implementation correspondence.

Two precision corrections were requested and have been incorporated in the
reviewed proof:

1. The second positive-FUEL residual is `E B X = S D B X`. Its first argument
   is `D`, not one of `E`, `b E`, and `B`. It is harmless: its head arity is
   three. The revised FUEL paragraph now includes it explicitly.
2. In the continuation argument, an **endpoint** means the whole term placed
   at an outer completed-Local/pending-frame context hole. It must not mean
   every instantaneous cursor focus. An `H`-headed arity-five prefix exists
   inside every fresh Local, and `localReturn = [U,U,U]` visits that prefix.
   The enclosing sixth-argument parent is its existing Local, not a new
   independently rebuilt `K A` context. The revised case 7 now makes this
   distinction explicit.

With these corrections checked, the local proof closes the stated
nonmanufacture issue. It does not derive global provenance from the public
carrier grammar or from `ReachableAudit.Holds` alone.

## 1. The discriminator and the induction being used

Put `b = S S`, `h = b S`, `H = b h`. A fresh response root has the literal
spine `S S h V D SeedField ContinuationField`, so its head arity is six and
its first two arguments are exactly `S,h`. Call this `H6`.

An occurrence induction is required. For each contraction, inspect:

- all three newly assembled contractum applications;
- occurrences copied from the redex arguments;
- every ancestor rebuilt between the redex and the whole root.

Copied occurrences retain their existing origin annotation. Old `H6`
ancestors rebuilt only in a registered mutable field retain the same origin.
Thus the difficult cases are a genuinely new scaffold root and a new match
crossing an outer-context hole. The arguments below address both.

The induction starts at the literal encoder. Every initial subtree has head
arity at most four. One cannot instead start with an arbitrary inhabitant of
`Holds`, since that predicate admits unrelated syntax inside tombstone audits.
After the induction starts, arbitrary *generated* carrier contents are
allowed: old genuine Locals can occur in current carriers, frozen snapshots,
history arguments, or tombstone audits. They need not be excluded or erased.

## 2. Exhaustive scaffold calculation

Use `D = S Act Seed`, `E = S D`, `Act = S H Actions`. Here `B` denotes a
literal generated clock exit, not the primitive `b`; `K` below is a
continuation metavariable, not another primitive combinator.

### Initial code, CLOCK, launch, and all seven FUEL rows

`C_0 = S b b` has first argument `b`. For `m > 0`,
`C_m = S S C_(m-1)` has second argument `C_(m-1)`, which is never `h`.
Indeed `C_j` is never `S`, and `C_(j+1) = h` would require `C_j = S`.
Clock wrappers `S C_n U` have first argument `C_n != S`.

The terminal pair, every clock-growth prefix, its environment application,
and a launched `C_n E B` therefore lack the reserved prefix. Their newly
assembled children have the same discriminators or head arity at most two.

The full FUEL residual table is:

| Row | Whole local residual | Exclusion |
| --- | --- | --- |
| positive 1 | `S E (C_m E) B` | First argument `E != S` |
| positive 2 | `E B (C_m E B)` | Arity three; first argument `D != S` |
| zero 1 | `(b E) (b E) B` | Second argument `E != h` |
| zero 2 | `S (b E) (E (b E)) B` | First argument `b E != S` |
| zero 3 | `(b E) B alpha` | Second argument `E != h` |
| zero 4 | `S B (E B) alpha` | First argument `B != S` |
| zero 5 | `B alpha beta` | Inherits the non-`H` prefix of `B` |

Here `alpha = E (b E) B` and `beta = E B alpha`. The additional newly
assembled children in these rows are precisely applications/prefixes of
`b E`, `E (b E)`, `E B`, `B alpha`, and the listed numerals/environments.
No arbitrary carrier becomes their head. Pending frames have arity three.

For a terminal clock exit, `B` has prefix `S,C_n` and arity four; for a
nonterminal exit, its first argument is `C_n` and its arity is three. Hence
the resulting Base can have arity six or five respectively, but cannot have
the reserved prefix. Base queue mutation leaves this head unchanged.

These are the literal residuals in `SchedulerInvariant`'s
`fuelPositive{First,Second}MutationConfiguration` and
`fuelZero{First,Second,Third,Fourth,Fifth}MutationConfiguration`, with the
clock equations in `Clock` and `Dovetail`.

### FRAME

The first two residuals are `(D V)(B V)` and
`(Act V)(Seed V)(B V)`. Their first arguments are `Act` and `H`, respectively,
and their arities are four and five. The third contraction, at `LL`, replaces
`Act V` by `(H V)(Actions V)`; its two retained parents produce
`H V (Actions V) (Seed V) (B V)`.

This creates exactly one new `H6` root. The other new `H`-headed applications
have arities three, four, and five. Any enclosing application with this new
whole shell as its left child has arity at least seven, not six.

### Route and appender stages

A compiled call is `b a V`, with `a` an appender or a compiled fork. None of
these `a` equals `h`: the empty appender `PI = S b` has arity one; Push has
an application as its first argument; a fork has a compiled child as its
first argument, and that child is never `S`.

After exposure, `Chosen(V,Y) = S V Y` has first argument `V != S`. A fork
contraction creates two compiled calls and their application. Before a child
is selected that application inherits the non-`H` compiled-call prefix;
after selection it inherits the first argument `V` of the activated child.
This checks intermediate route ancestors, not just the selected-call root.

The initial Push call, its `S N X (L_i X)` intermediate, and every subsequent
remaining-appender spine have first arguments different from `S`. The
completed `PI` spine has first argument `b`. Appending retained right-hand
history arguments does not alter any of these discriminators.

The only new application headed by a variable carrier is `X (L_i X)`.
During an uninterrupted appender, `X` is either the original whole carrier or
that carrier under one or more live wrappers. A live wrapper has arity three;
a fresh whole Local has arity six; marked whole Locals and Bases of arity
five lack the `H` prefix. Consequently this history cannot create `H6`.
If `X` is fresh, its existing `H6` root is simply the left child of a new
arity-seven history. This explicitly handles the arity-five-to-six risk.

`RouteMutation.parser`, `ActionMutation.parser`, and their `done_eq` lemmas
then rule out an early completed-pattern match in the born shell. An empty
action completes at the final route contraction; a nonempty action completes
at its final second Push contraction. For `F17` the latter is the relevant
case. Route syntax distinguishes leaves even when their appender codes agree.

### C4 and COMMIT

C4 creates `S Y (v_i Y)`: its three new applications have arities one, two,
and two. Any `H6` below them is copied from `Y`. Along the selected ascent,
live/tombstone contexts have fixed arity three/two; Base contexts retain
their non-`H` head; action and route contexts retain the discriminators above.
Enclosing Locals are reconstructed with unchanged halt field, route, and
history list. Their existing `H6` roots inherit their annotations.

COMMIT changes `H V` to `S V (h V)`. The whole selected shell now has arity
five and first argument `V != S`. The new `h V` has arity three. Thus COMMIT
removes one fresh signature and only copies any genuine descendants of `V`.

## 3. The continuation-hole check is indispensable

A pending wrapper has its hole on the right, so it cannot extend the hole's
left spine. A completed Local has continuation field `K A`. This field can
newly acquire `H6` only if the whole replacement for `K` has arity five and
the reserved prefix.

The endpoint table above rules this out: CLOCK/launch/FUEL endpoints lack
the prefix; a pending frame has arity three; FRAME's arity-five residual has
first argument `H`; fresh response endpoints have arity six; marked endpoints
and Bases lack the prefix. Rebuilding another outer wrapper preserves this
classification: its root is either pending arity three, fresh arity six, or
marked arity five with a frozen whole-carrier first argument. Induction
therefore covers an arbitrarily long alternating outer-context chain.

This statement is deliberately about whole hole endpoints. It does not deny
the existence of internal `H`-headed arity-five prefixes.

There is a short negative control showing why the restriction cannot be
dropped. For arbitrary terms `V,W,D,A`, contracting the left child of

```text
(S (H V) (S W) D) A
```

produces

```text
H V D (S W D) A.
```

The latter is `H6` even though the former need contain no `H6`. Taking `D`
to be the independently instantiated completed target dispatcher and `A` to
be an application even manufactures the target Local pattern. This is not a
counterexample to the construction trace: the pre-contraction endpoint is
not one of its generated rows. It is a counterexample to a context-free
version of the proposed lemma.

## 4. Frozen audits and source support

In a fresh Local the audit is at literal address `LLLR`. The mutable
dispatcher begins at `LLR`, and the active continuation begins at `RL`.
These are disjoint occurrence addresses, not merely semantically equivalent
carrier descriptions.

`ReachableAudit.Layer.reduceAccumulator` preserves its snapshot, halt status,
route, and label, but is only an existential lifted `StepsN` result. The
stronger occurrence conclusion comes from `CanonicalTraversal`:

- `localContext_plug` displays the fixed snapshot around the variable
  accumulator context.
- In `SelectedFront.delete.inside`, only `currentContext` is replaced.
- In `SelectedFront.delete.segment`, only `segmentContext` is replaced.
- Both cases rebuild the same snapshot, halt state, label, and route context.
- `Decodes.deleteCanonical` gives the selected literal address and the
  equality obtained by replacing that occurrence with the C4 contractum.

Induction through these contexts protects every enclosing fresh Local,
including old Locals inside a working carrier. A Local in an off-path audit
or history is untouched; copying it copies its audit exactly. The induction
does not need those off-path terms to be devoid of Locals.

For the UT19 target, the nonempty 19-bit appendant prevents immediate COMMIT.
Subsequent selected C4 steps act in carrier accumulators; COMMIT for a later
EMPTY response targets that later response's own halt field. The permanent
freshness assertion for the old target therefore uses the stated scheduler
discipline, not just `Layer.reduceAccumulator`.

The forged-tombstone example in the original proof is valid. A tombstone's
audit is unrestricted and ignored by queue decoding, so `Holds.base` can
hide a fabricated `F17`. None of the inspected source lemmas silently turns
`Holds` into generated-from-encoder descendant provenance.

## 5. Inspection and independent finite checks

Source inspection was pinned to commit
`85a867988442fc423279341200f81634a1e65582`. The local source copies of
`ReachableAudit`, `CanonicalTraversal`, `SchedulerResponseInvariant`,
`SchedulerInvariant`, `SchedulerCompletedContext`, `Frame`, `Clock`,
`Dovetail`, `SchedulerCycle`, `RootResetOrderedCarrier`,
`RootResetGeneratedCarrierLabels`, and
`RootResetFiniteAllInputsTraceAgreement` were independently checked against
the Git blob SHAs returned for that commit. The supplied copies had one
extra terminal newline; normalizing that newline gave exact blob matches.
No kernel elaboration or dependency replay was performed.

Primary source directory:
[pinned PureSFormal source](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal).
In particular, the all-sample transfer is
[`termOnlyPath_eq_persistentPath`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFiniteAllInputsTraceAgreement.lean).

`tests/test_local_event_provenance_review.py` defines its own tiny immutable
AST and literal one-occurrence reducer. It imports no production constructor,
parser, selector, or reducer. Six tests passed in 0.028 seconds under a hard
180-second timeout and a 512-MiB address-space limit:

- every positive/zero FUEL row in bare, pending, fresh, and marked contexts;
- CLOCK expansion and launch for four small clock indices;
- FRAME birth, route activation, and appender intermediates up to 19 bits,
  with already genuine nested Locals in copied snapshots;
- nested-Local C4 at a literal selected accumulator address and copies into
  a new tombstone audit;
- COMMIT's removal of just the selected fresh root;
- the deliberately nongenerated cross-hole counterexample above.

The tests audit all newly assembled nodes and rebuilt ancestors and permit
old `H6` objects to be copied. Object identity is a test aid only. They are
not a proof about all source inputs, actual root-reset selection, or arbitrary
S reduction.

## 6. Inherited premises not independently discharged here

The following remain assumptions or imported results of the composition,
rather than consequences of this review:

1. Every contraction sample of the persistent scheduler is generated by the
   listed scripts in the exact registered contexts, including stage changes,
   initial-empty jobs, EMPTY sweeps, and continuation handoffs. The inspected
   local equations support this interface; this review did not replay the
   complete scheduler recurrence or its dependencies.
2. The semantic register/`NormalInvariant` induction attaches every normal
   completed response to the correct ordinary/totalized CTS prestate, starts
   every job from the seed and phase zero, and gives EMPTY the false-bit
   label. `selectedResponseTrace_preserves` is a one-response theorem with
   explicit premises; it does not itself establish the global induction.
3. Stage coverage and ordering: every finite source prefix is completed by a
   sufficiently large recomputation job, and no later event can be exposed
   before the first event within that job. These are needed for completeness
   and the first-accepted-sample numerical output statement.
4. The pinned source's all-sample root-reset/persistent trajectory equality.
   Once supplied, whole-tree equality suffices to transfer the extensional
   current-tree observer and audit readout; a new equality of root-reset
   contraction addresses is not additionally needed for that transfer.
5. Correspondence of this repository's Python encoder, selector, and literal
   route pattern with the pinned construction for all relevant inputs.
   Fixture agreement alone does not establish this universal port theorem.
6. Correctness and adequate resource budgets of the exposed structural
   carrier reader and the UT19 first-event prestate reader, plus the upstream
   source-machine/UT19 simulation theorem. An exhausted budget is not a
   negative event decision.

In particular, existence of a genuine descendant Local proves a past source
event, not that the next transition is that event. A numerical readout from
an arbitrary later retained event is not justified by this local argument.
