# Research map

Literature reviewed 6 October 2026; verification updated 7 October 2026. The project studies native S rewriting, fixed reduction controllers, source compilers, and structural observation interfaces. The [end-to-end theorem](universality-theorem.md) and [final verification](final-verification.md) record the completed 67-module construction and fresh kernel replay.

## The computation interface

A universality construction needs five explicit components:

1. A finite source program and input.
2. A terminating encoder producing a finite S-only application tree.
3. A fixed rule for selecting one native contraction at each step.
4. A bounded observer that recognizes completed work in the current tree.
5. A decoder that recovers the source result at accepted observations.

The [challenge announcement](https://writings.stephenwolfram.com/2021/06/1920-2020-and-a-20000-prize-announcing-the-s-combinator-challenge/) allows computation to be observed during ongoing growth and explicitly discusses both selected-path and multiway formulations. These lead to different proof obligations. Every experiment here names its selector and observation interface.

## Direct construction: September 2026

Cinematic Strawberry's [Pure S Is Computationally Universal Under a Fixed Root-Restarted Finite Controller](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality) is the most developed direct construction found in this review.

The public package claims a uniform compiler from deterministic Boolean-tape machines through a fixed 912-phase cyclic tag system. A finite controller restarts at the root for each invocation, navigates the current tree and performs one S contraction. The output is observed along the selected trajectory. A fixed regular tree language detects source halting; separate readers recover source configurations and the terminal scanned bit. Finite control does not bound the depth of the current tree or cursor navigation.

The inspected [headline declaration](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/RootResetHeadline.lean) ties those interfaces to the same trajectory. The package reports 1,239 Lean modules and 319 public declarations. The [verification guide](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/VERIFICATION.md) and [definition inventory](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/TRUSTED_DEFINITIONS.md) are the starting points for an independent replay.

The package is under the repository's [MIT license](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/LICENSE). This repository's initial reducer is independently implemented. Reused source must preserve the applicable notice and attribution.

Version check: the latest upstream commit found was [`c402a632`](https://github.com/cstrawberry/predictive-universe/commit/c402a63231bad6309c541b6951badf86c4d52749), dated 29 September 2026. Its [five-commit comparison](https://github.com/cstrawberry/predictive-universe/compare/85a867988442fc423279341200f81634a1e65582...c402a63231bad6309c541b6951badf86c4d52749) has no changed path inside the pure-S package. The audit therefore keeps the package pinned at `85a867988442fc423279341200f81634a1e65582`.

The pinned 423-module dependency closure has now passed a clean build, fresh official Lean kernel replay and axiom audit. The added 67-module construction, including the conventional tape-machine compiler, also passed fresh replay with 1,359 declaration queries; see the [final verification record](formal-turing-universality.md). This checks the dependency closure used by the concrete 38-phase construction, rather than all 1,239 upstream modules.

## Recent complementary work

### Nathan Douglas: formal simulation interfaces, August 2026

The [CombinatorCalculusPlayground](https://github.com/ndouglas/CombinatorCalculusPlayground/tree/5a7d3a25014983ec3bebef3eb9870933585209cb) develops explicit simulation interfaces and obstructions. The inspected [`PathEncoding`](https://github.com/ndouglas/CombinatorCalculusPlayground/blob/5a7d3a25014983ec3bebef3eb9870933585209cb/CombinatorCalculusPlayground/Universality/Defs.lean) demands an injective encoding that preserves source reachability. Its [calibration theorems](https://github.com/ndouglas/CombinatorCalculusPlayground/blob/5a7d3a25014983ec3bebef3eb9870933585209cb/CombinatorCalculusPlayground/Universality/Calibration.lean) rule out such encodings of the entire SK rewrite system into pure S using an SK cycle and pure-S acyclicity. The same obstruction applies to its iota host, illustrating how strong that interface is. A construction that retains history and uses many tree representatives for one source configuration has different obligations.

Latest commit found: `5a7d3a25014983ec3bebef3eb9870933585209cb`, 25 August 2026. These Lean sources were inspected, not executed.

### Nakano and Iwami: finite-automaton nontermination certificates

The [CIAA 2024 paper and full version](https://arxiv.org/abs/2406.14305) use SAT-generated tree automata to establish nontermination of non-erasing sole-combinator systems, with a final sink state simplifying the search. Eight combinators receive nontermination witnesses. This supplies a useful methodology for independently checkable certificates.

Iwami and Nakano's [2026 journal paper](https://doi.org/10.2197/ipsjjip.34.39), released 15 January 2026, extends tree-automaton nontermination arguments to families of O-like and S-like combinators. The [publisher's abstract](https://www.jstage.jst.go.jp/browse/ipsjjip/34/0/_contents?from=0) states the result at the family level. Nontermination certificates and encoded computation answer different questions; the automata technique is relevant to classifying carrier terms and checking invariants.

## Established constraints

- Waldmann's *The Combinator S* establishes decidability of normalization and absence of ground loops. The [author's thesis](https://www.imn.htwk-leipzig.de/~waldmann/pub/phdthesis/) and [Dance of the Starlings](https://www.cs.ru.nl/~henk/BEKW.pdf) provide the foundational theory.
- [Vatan (2022)](https://arxiv.org/abs/2210.12893) proves non-definability of an identity-like combinator, implying non-definability of K. This concerns literal combinator behavior on arguments. The selected-path observation interface must be evaluated on its own stated encoding and readout.
- For any closed contraction `S x y z -> x z (y z)`, the number of S leaves increases by `leaves(z) - 1`. This elementary invariant is useful for debugging and bounds. The change can be zero, so leaf count alone is not a strict termination measure.

## Implementation and audit order

1. Build an independent immutable occurrence-tree reducer and a separate trace checker. Record one path per contraction and distinguish normal forms, head-normal forms and resource exhaustion.
2. Validate every one-step rewrite and selector choice over all closed S trees through eight leaves against a separate tuple-based oracle.
3. Check the small closed gadgets and preserve their complete native traces as regression fixtures.
4. Transcribe the candidate's queue encoding into a small, attributed executable specification. Reproduce the published `101 -> 011 -> 11` two-phase example, including every intermediate rewrite and reported occurrence-tree size.
5. Audit the controller's primitive observations, root reset, exactly-one-contraction boundary and totality on malformed trees. Test observer acceptance at every intermediate sample, including copied inactive fields.
6. Rebuild the pinned formal package in an authorized Lean environment. Record dependency hashes, exit codes, public theorem types, axiom dependencies and checker provenance.
7. Trace the encoder, source simulation, sample chronology and readout theorems end to end. Extend practical tests to tiny Boolean-tape programs once the queue layer agrees.

The highest-value first replication target is the small queue trace. It checks concrete native semantics and occurrence identity before the substantially larger compiler and formal verification surface.

## Replication checkpoints

The independent reducer, exhaustive small-term checks and closed gadgets are implemented. The [85-contraction two-phase queue replication](queue-replication.md) reproduces every published literal contractum and all 86 checkpoint decisions. The [controller interface audit](controller-audit.md) records the finite-selector model and theorem dependencies.

The finite restoring-pattern compiler is implemented with an explicit six-observation transition table and a general restoring proof. The seven [fuel endpoint rows](fuel-probe.md) recover 25 local selections in the recorded trace. [Standard-selector comparisons](strategy-comparison.md) locate the first departure from that trajectory at contraction 3 for normal/head order and 4 for applicative order.

The [compact source fixture](neary-fixture.md) now materializes a 482-phase CTS and verifies both two-state write-and-halt cases. Its [generic S initial encoding](cts-encoding.md) has exactly 1,342,619 expanded nodes. [Spine-walker components](spine-walkers.md) add descending and restoring ancestor queries to the finite-controller toolkit. The [event-composition lemma](event-composition.md) isolates how a distinguished CTS production event can be observed through exact S readout.

The fixed two-phase [root-reset selector](root-selector.md) is reconstructed as a 257,299-state primitive control graph. It independently chooses all 85 published addresses. A separate model review disables source/fixture access during execution and tests 6,918 small trees plus 500 adversarial contexts. The pinned build and official kernel replay are complete, with theorem meaning and execution scope reviewed separately in the [proof audit](formal-proof-review.md).

The [succinct positive-period controllers](succinct-periodic.md) reproduce the
same indexed graphs through period five. [Construction-time code sharing](pooled-selector.md)
preserves their immutable values while reducing repeated descriptor storage.

The [compact-source survey](compact-universal-programs.md) identifies ais523's
UT19 as an explicit 38-phase ordinary CTS endpoint. Its
[source fixtures](ut19-fixtures.md), [one-hot translation](alternating-tag.md),
[memory lemma](running-xor-memory.md), and
[counter/clock simulation proof](ut19-simulation-invariants.md) specify the
unpadded BP2 interface, exact first selected-18 event, and preserved results.
S-level event observation and exact first-sample numerical output are joined
in `SOnlyUniversality.result_iff_first_event`; see the [dependency map](proof-dependencies.md).
