# UT19 designated-event observation at the S level: audit and exact obligations

Audit date: 6 October 2026. This note specifies a regular S-tree event language
and its output interface. The [generated-script provenance proof](local-event-provenance.md)
addresses the occurrence and audit-preservation obligations identified here;
the fixed-scheduler connection is a separate premise.

## 1. Conclusion

The smallest promising Boolean witness is:

> Some occurrence in the current S tree is a completed **fresh** Local whose
> selected dispatcher route is labelled `(17, 1)`.

This is an explicitly regular tree language, with no clock comparison,
carrier comparison, source evaluator, or input-dependent control. Its
regularity can be proved directly from one finite linear pattern. Fresh alone
is sufficient: this transition appends 19 bits, so its immediate successor is
nonempty. Including the marked pattern is possible but unnecessary.

The remaining hard obligation is **generated-occurrence provenance**. Neither
the existing checkpoint theorem nor the local pattern/parser equivalence
alone proves that a match anywhere in a reachable tree records a real
phase-17/head-one source transition. Retained genuine history is harmless for
an eventual-event statement; accidentally manufactured matches are not.

For output, an arbitrary matching Local's accumulator is unsafe: it can have
changed after that response completed. The fresh halt-field audit at its
fixed address `LLLR` is the preferable candidate. At response creation it
holds the post-deletion, pre-append carrier. If its occurrence is preserved
without re-entry, decoding it and restoring the deleted `1` reconstructs the
required pre-event CTS word. That preservation is an additional trajectory
obligation, stated below.

## 2. Fixed program, route, and exact finite pattern

Let `P = ut19.compile_cts()`. It has 38 phases and 760 appendant bits, fixed
independently of the Brainpocalypse II source program and input. The selected
event is the CTS **prestate** predicate

```text
H(c) := c.phase = 17 and c.word starts with 1.
```

With published one-based tag symbols, put `e = E(18) = 0^17 10`. Then
`P.appendants[17] = e`, of length 19. In the repository's unpadded
adjacent-pairing dispatcher, leaf `(17,1)` has the seven-edge route

```text
rho = L R L L L R R = 0100011.
```

Labels must be identified by this structural route, never by equal appender
code: multiple labels can have equal actions.

Use the constructors in `program_selector_parts/patterns.py`. Every `_`
below is a fresh independent wildcard. Let

```text
A19 = (((PI _) _) ... _)        exactly 19 history arguments after PI _
Chosen(X) = S _ X
Call(code) = literal(code) _.
```

At the target leaf the pattern is `Chosen(A19)`. At each of the seven route
ancestors, wrap it with `Chosen(active Call(dormant_code))` for a left turn
or `Chosen(Call(dormant_code) active)` for a right turn. The dormant code is
the fixed compiled sibling at that node. Call the resulting pattern `D17`.
The target Local pattern is

```text
F17 = (((HALT _) D17) ((S _) _)) (_ _).
```

This is exactly the `(17,1)` member obtained by `dispatch_records()` and
`local_pattern('fresh', ...)`, with `required_period=None`. The completed
action accumulator has a fixed address: `LLR`, then the route-response
address, then `L^19 R`. That address has 38 edges. The fresh halt audit is
always at `LLLR`, independent of route and appendant length.

Define the actual proposed Boolean language, on **every** finite closed S tree:

```text
W(T) := there exists an occurrence address a such that F17 matches T[a].
```

Off trajectory, `W` is only this syntax predicate. Its holes deliberately
accept fabricated payloads. It is not a reachability certificate.

### Direct regularity proof

Let `K` be the finite set of subpatterns of `F17`, including `_` and `S`.
A bottom-up state consists of a subset `M` of `K` and one Boolean `found`.
`M` records the patterns matching exactly at the current subtree root.

- At `S`, `_` and `S` match; application patterns do not.
- At `App(x,y)`, `_` matches, `S` does not, and pattern `(p,q)` matches
  exactly when `p` belongs to the left child's `M` and `q` to the right's.
- `found` is true exactly when `F17` belongs to this root's `M`, or either
  child's `found` is true.

Accept exactly the states with `found=true`. Induction on the input tree
proves exact agreement with `W`, including malformed/off-trajectory trees.
There are at most `2^(|K|+1)` states; no claim is made that enumerating that
cover is practical or that this bound is tight.

A finite tree walker is even easier to describe: use a restoring fixed-pattern
probe at each occurrence during a complete preorder Euler traversal. Accept
at the first match; reject after returning from the root. A finite control
records the traversal phase and the fixed probe state; the one occurrence
zipper is its only unbounded cursor context. Every probe restores its origin
on failure. There are `N` probes and a linear number of traversal edges on an
`N`-occurrence tree, so termination follows on all inputs with bound `c*N`
for a program-static constant `c`. No native contraction is performed.

This traversal is a new observer's deliberate descendant search. It is not
the marker observer's prohibited use of a reduction selector's Euler fallback.

### What the local pattern really proves

The completed-route shape fixes the label and history count. Chosen children
have head arity two, while dormant compiled calls have head arity three, so
the left/right alternatives cannot be confused. The `PI` prefix excludes
unfinished appender forms at that **same** route response. The patterns do
not compare holes or require their content to be well-formed carriers.

Pinned `RootResetCompletedLocalPatterns.local_sound` and `accepts_iff_parse`
give the general local syntax/parser correspondence. The repository's
`dispatch_records()` additionally retains each individual route label. A
label-specific version follows by the same route induction. It is not a
source-semantic theorem.

The initial encoded term cannot already match `F17`: its every subtree has
head arity at most four. Literal routines, dispatchers and `ACT` have arity at
most two; live word cells have arity three; the initial clock envelope has
arity four. A fresh Local has head arity six. A marked Local has arity five,
so adding that alternative would not create an initial match either.

## 3. Exact global obligations for event equivalence

Write `T_n` for the fixed native root-reset trajectory and `c_k` for the
ordinary/totalized CTS trajectory from the encoded compact seed. The desired
claim is

```text
(exists n, W(T_n)) iff (exists k, H(c_k)).
```

The following obligations are sufficient. They must be proved at **occurrence
addresses**, not merely by equality of whole erased next terms.

1. **Birth/origin of every accepted occurrence.** Every `F17` occurrence in
   every `T_n` descends, by preserved occurrence/copy history, from a completed
   normal response whose semantic label was `(17,1)`. The only new matches
   introduced by a contraction must be either such a completed response or
   copies of already genuine matches. The induction must inspect ancestors
   whose previously incomplete fixed skeleton changes, not only the redex
   root and its copied arguments.
2. **Exhaustive stage exclusion.** Prove the preceding assertion for CLOCK,
   all seven FUEL prefixes, Base creation, C4 deletion, both FRAME contractions,
   every dispatcher exposure/fork, every appender intermediate, response
   completion, COMMIT, continuation handoff, and stage/job launch. Dormant
   `ACT`, appender code, seed copies, and retained audits may contain `HALT`;
   that alone establishes nothing. No partial route or clock may create a
   target Local outside the stated completion case.
3. **Semantic labels.** A normal response with label `(phi,b)` must originate
   in a genuine `c_k` with phase `phi` and deleted head `b`. In particular an
   EMPTY response uses a false-bit label and cannot introduce `(17,1)`.
   The recovered phase must be semantic phase, not merely a label inferred
   from an arbitrary malformed predecessor.
4. **Coverage.** Each genuine CTS transition is eventually completed in a
   sufficiently large recomputation job, and its completed Local occurs in a
   sampled S term before later work. Thus a phase-17/head-one transition
   supplies a fresh `F17` occurrence, because its 19-bit appendant makes the
   successor nonempty.

With 1–3, any accepting occurrence supplies an actual `H(c_k)`. With 4, every
`H(c_k)` eventually supplies an accepted occurrence. This is a complete
composition proof **conditional on those obligations**, not a claim that
they have all been discharged here.

The upstream source gives substantial ingredients: exact normal-response
construction, coherent semantic registers, clean completed outer parents,
stage/job selector chains, and all-sample root-reset transfer. Its manuscript
also describes the relevant generated-role exclusions. Its existing public
checkpoint theorem only classifies full checkpoints, and its existing marker
soundness theorem concerns selected EMPTY-origin halt-field contractions.
Neither theorem has the descendant-labelled-Local conclusion above. The
all-subterm birth/origin lemma is the extra proof to add, rather than silently
treating one of those theorems as if it already stated it.

Retained genuine history needs no exclusion for this existential language.
It proves that the event occurred during a genuine source prefix. In
contrast, it would defeat a claim that `W(T_n)` means the **next** transition
is the event. This proposal makes no such next-transition claim.

No paired-clock equality is dropped from a checkpoint parser here. The new
language deliberately accepts some noncheckpoint responses. An earlier job
within a stage is allowed to witness a real event; its unmatched terminal
continuation is irrelevant to the existential claim.

## 4. Output must use a specified current occurrence and first-event timing

The source theorem and `ut19_readout.read_cts_result` concern the first event's
**pre-transition** queue. A Boolean witness alone does not identify that queue.

There is already a conservative public-API composition:

```text
d := compile_reader(P).decode(T)
if d is present, d.phase = 17, and d.data starts with '1':
    return read_cts_result(Configuration(word=d.data, phase=17))
```

At the first accepted event checkpoint this is correct conditional on the
upstream exact checkpoint realization and correspondence of the Python port.
It uses only the current tree and the fixed program. It does **not** establish
a regular Boolean observer: the checkpoint reader compares unbounded clock
indices and Base continuations. Keeping this already justified conditional
composition separate is preferable to deleting those comparisons without a
replacement reachable-language proof.

### Why arbitrary accumulator reversal is unsound

If a newly completed event Local's accumulator decodes to `z`, then

```text
c_k.word = '1' + u,
z = u + e,
c_(k+1).phase = 18,
e = 0^17 10.
```

At that creation boundary, check the literal suffix `e`, remove it, and
prepend `1`. This is a valid inverse of that specific CTS transition.
However, a completed Local inside a working carrier can later have its
accumulator changed by head deletions. The pinned manuscript explicitly
distinguishes these from immutable completed outer continuation layers.

A bounded check of the repository's existing `101` fixture demonstrates the
problem for `P=('1','')`:

- A `(0,1)` Local first completes at sample 22, with accumulator `011` and
  fresh halt audit decoding to `01`.
- At sample 47, the completed `(0,1)` Local at occurrence path `101` has
  accumulator `11`, while its fresh halt audit still decodes to `01`.
- Removing its fixed appendant `1` and restoring a deleted `1` now produces
  `11`, which is not that response's original prestate `101`.

The paths here use `0=L, 1=R`; samples are numbered before contraction zero.
This is a real fixture counterexample to a generic readout rule, not evidence
that UT19 itself has reached an S-level event.

### Prefer the retained post-deletion audit

Pinned `LocalResponse.completed` is exactly

```text
Carrier.activeShell bits continuation (freshHField carrier)
                    completedRoute carrier carrier.
```

`PrimitiveLocalResponse.run_execute` starts from a response frame over the
post-C4 carrier and preserves that carrier in the fresh halt field while the
selected appender wraps its separate active occurrence. At the response's
creation, the carrier at `LLLR` therefore decodes to `u`, the prestate with
its first bit removed.

The proposed output composition at a certified event occurrence `X` is

```text
u := DecodeCarrier(X[LLLR])
return read_cts_result(Configuration(word='1' + u, phase=17))
```

`DecodeCarrier` is the structural carrier operation already implemented as
`CompiledReader._queue`, not full checkpoint `decode`. Exposing it as a
public, resource-bounded interface is a future production task. It may use
unbounded input-dependent structural work; the Boolean finite/regular
observer and the output transducer have different contracts. Neither one
needs to rerun the source or consult a saved trajectory.

For this composition to be correct, add the following explicit obligations:

5. **Audit origin and immutability.** At a genuine completed target Local,
   `LLLR` is the same post-deletion carrier occurrence copied before append.
   Thereafter the selected run never contracts inside that halt-audit
   occurrence. Copying it preserves its value. This must hold for Locals
   inside working carriers as well as completed outer layers; a generic
   independent-hole parser theorem does not supply it.
6. **First accepted sample.** Let `n0` be the least `n` with `W(T_n)`. Prove
   that any chosen target occurrence in `T_n0` originates at the least source
   event index `k0`. Stages enumerate bounds in order, every job recomputes
   the source prefix from the original seed, and the first job that covers
   `k0+1` must expose that event before any later event. These stage facts
   must be joined to the birth/origin invariant. On later accepted samples,
   a matching Local could instead record a later event.
7. **Carrier readout correctness and budgets.** The structural reader on the
   protected carrier must return exactly `c_k0.word[1:]`. The restored word
   must pass the existing UT19 prestate grammar; the resource caps must
   suffice. A budget refusal is not a negative halting decision.

One can choose a current occurrence deterministically, for example the first
preorder match. The selector must be rerun on the supplied current tree;
cached addresses from earlier samples are not part of this interface. For a
current-tree-only numerical output theorem, the first-accepted-sample premise
must remain visible unless a separate structural method identifies the first
source event among all retained occurrences.

## 5. Source-specific suffix fact: useful, but not an S proof

There is a short exact CTS lemma. The compact seed's final tag symbol is 6
or 19. Every nonempty UT19 production except `18 -> 18` ends with a symbol
other than 18. Consequently:

> Before the first `(17,1)` CTS transition, no CTS queue has suffix `e=E(18)`;
> the successor of that first transition does have suffix `e`.

Proof directly at the CTS level: the initial binary word ends in `E(6)` or
`E(19)`. Deleting a first bit without appending cannot create a previously
absent 19-bit suffix; it either preserves that suffix or leaves fewer than
19 bits. Every nonempty non-event appendant consists of whole 19-bit blocks
and ends in a block other than `E(18)`. The event appendant is exactly `e`.
Induction proves the assertion, without a queue-length lower bound or a
clock-alignment guess. The corresponding tag-queue argument is the same
last-symbol invariant.

This permits a redundant suffix check at a newly completed target response.
It does not justify searching arbitrary S subtrees for the encoded suffix:
the non-event productions `3 -> 18,4` and `9 -> 18,10` append `E(18)` as a
proper prefix. Their partially executed S appenders can temporarily build
that live suffix before completing the remainder. Dormant code and copied
carriers create additional roles. Completed-route timing and occurrence
provenance are still essential.

## 6. More conservative alternative: observe the selected initial appender

If proving provenance of all descendant Local matches is too broad, use the
existing read-only priority selection worker, then a fixed inverse-address
check that its endpoint is the **initial appender call** in the `(17,1)`
fresh response. Its local pattern is `F17` with `A19` replaced by
`literal(append_routine(e)) _`, and its endpoint address is the fixed
18-edge shell/route-response address. Inverse inspection must validate every
incoming side and restore the endpoint, rather than merely searching for a
similar ancestor. Reject if priority selection declines; no Euler fallback.

`RootResetSelectedActionRows.generated_initial` already identifies this
generated appender occurrence, and `PrimitiveLocalResponse.run_execute`
identifies its argument. Its right child is the post-deletion carrier, so
the same prepend-`1` output formula applies before any bit is appended.

This gives a finite read-only composition using the existing priority
worker's all-input bound plus a constant-size restoring probe. Its global
semantic proof still needs occurrence-preserving identification of the
selected stage and the semantic label. Equality of next whole terms is not
enough. It avoids arbitrary retained-history acceptance but has a larger
finite-control dependency than the direct regular descendant language.

## 7. Verification boundary and primary sources

Independently established here: the finite-pattern language definition and
direct regularity proof; fixed route and appendant inspection; the initial
arity exclusion; the CTS suffix invariant; the algebraic output inverses at
their stated boundaries; and the concrete mutable-accumulator counterexample.

The bounded scratch check reconstructed only the existing 85-contraction
`queue_101_path.json` fixture with the repository's one-occurrence S rewrite.
It parsed current subtrees independently of saved source configurations and
found first completed labels `(0,1)` at sample 22 and `(1,0)` at sample 55.
It ran under a 60-second/512-MiB process limit. No large UT19 S reduction or
new production observer was compiled or run. Finite checks do not discharge
the global obligations above.

The following source texts were inspected at commit
`85a867988442fc423279341200f81634a1e65582`; their upstream theorem proofs were
not replayed. The repository's Python correspondence is likewise a separate
proof obligation, beyond finite tests.

- [Completed Local patterns](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetCompletedLocalPatterns.lean): finite independent-hole patterns and local parser agreement.
- [LocalResponse](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/LocalResponse.lean) and [PrimitiveLocalResponse](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/PrimitiveLocalResponse.lean): exact completed fields and response scripts.
- [Selected action rows](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetSelectedActionRows.lean): labelled initial appender rows, addresses, and generated executions.
- [Response candidate probe](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetResponseCandidateProbe.lean): active frontend followed by nearest completed fresh ancestor, not a global provenance theorem.
- [Finite all-input trace agreement](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFiniteAllInputsTraceAgreement.lean): native whole-term selector transfer and exact checkpoint realization.
- [Marker observer soundness](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetMarkerObserverSoundness.lean): the distinct EMPTY event, using occurrence-preserving physical marker arguments.
- [Paper, active-copy exclusion](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/paper.md#active-copy-exclusion): generated roles, completed outer-parent preservation, and the explicit mutable-working-carrier distinction.

Related repository interfaces: [source simulation](ut19-simulation-invariants.md),
[one-hot CTS translation](alternating-tag.md), [result reader](ut19-readout.md),
[generic event composition](event-composition.md), [checkpoint reader](cts-reader.md),
and [the different marker observer](marker-observer.md).
