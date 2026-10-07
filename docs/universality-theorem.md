# Universality along a fixed S-only trajectory

The construction has one fixed finite root-reset controller, one fixed regular
tree event and one fixed current-tree numerical decoder. Its encoder accepts
an arbitrary finite register machine and arbitrary natural inputs.

The end-to-end formal statement is
[`SOnlyUniversality.result_iff_first_event`](../formal/SOnlyUniversality.lean).
It includes the source compiler, nontermination direction, first acceptance
and numerical output. The S encoding and generic finite-controller machinery
specialize Cinematic Strawberry's construction at upstream commit
[`85a867988442fc423279341200f81634a1e65582`](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality).

## Statement

There are a fixed controller C, a fixed regular tree language H, a total
syntax encoder E and a total current-tree decoder D such that the following
holds for every finite `INC/DECJZ/HALT` register machine M and natural-register
input a.

E(M,a) is a finite closed term in

    T ::= S | (T T).

Let T₀=E(M,a), and obtain Tₙ₊₁ by invoking C on Tₙ. Every invocation starts
at the root with the same finite control. The control observes only S versus
application and entry from root, left or right, and uses stationary control
changes, single-edge moves and a single occurrence contraction of

    S x y z → x z (y z).

Only the resulting S term persists between invocations. For a fixed constant
κ, every invocation on every finite input tree terminates within
κ(|T|+1) microticks. A nonnormal tree produces one contraction; a normal tree
produces none. Every tree on the encoded trajectory has a next contraction.

For every natural result v,

    M(a) halts with register 0 equal to v
      iff
    there is a first index n with Tₙ in H, and D(Tₙ)=v.

A nonhalting source has no event at any S sample. Every matching event witness
in the first accepted tree has the same frozen audit and numerical result,
so the decoder's fixed first-preorder choice is sound.

The encoder has singly exponential bit-time in an explicit binary description
of M and a. Event recognition is a fixed bottom-up tree automaton. Decoder
cost is polynomial in the current occurrence-tree size. These auxiliary
bounds are independent of the source computation's running time.

## Fixed interfaces

### Controller and initial term

The fixed source CTS P is the 19-bit one-hot translation of UT19: nineteen
encoded TAKE productions followed by nineteen empty SKIP phases. Its period
is 38, with 760 appendant bits and 40 ones.

C is the pinned `RootResetFinitePrioritySelector.selectorContract P A`,
where A is the canonical balanced dispatcher. Its selector is
`RootResetFiniteAllInputsTraceAgreement.selector P`. Neither depends on M
or a. The formal contract's inter-invocation state is literally Unit.

`SOnlySimulation.machineBits M a` constructs a finite bitword w through the
checked machine/BP2/UT19 compiler. The initial S tree is

    E(M,a) = generator (compileActions P A.tree) w.

The formal source compiler uses uniform helper allocation and an initial
Waterfall offset of five. Its exact definitions and bounds are in
[the frontend report](formal-register-machine-frontend.md). The earlier
selective Python compiler remains an independently tested reference variant.

### Event

H is descendant occurrence of `SOnlyEventPattern.targetPattern`: a completed
fresh Local with label `(17,true)`, route `0100011`, and nineteen completed
appender history arguments. All holes are independent.

`SOnlyObserver` proves its exact finite bottom-up semantics. Its checked
occurrence-based cover has length `2^(targetPattern.size+1)`; the separate
Python recognizer shares equal subpatterns and has a 1,751-bit cover. These
are two finite recognizers of the same independent-hole syntax language.

### Current-tree decoder

`SOnlyCurrentDecoder.read` finds the first matching shell in root-left-right
preorder. It reads the frozen LLLR audit through the public seed-free carrier
grammar and restores the deleted true bit. The phase-17 current bitword has
form `10` followed by complete nineteen-bit one-hot blocks. Decoding those
blocks and restoring the known head symbol 18 gives published UT19 symbols.

The numerical projection locates the first maximal run of symbol 16, checks
that its length is a power of four at least four, and returns its exponent
minus one. If that counter value is odd and at least three, D returns
`(counter−3)/2`; otherwise it rejects. This reads only the supplied current
tree. It does not run the source, search a trace or use an input-dependent
controller.

The first selected witness is retained even if its payload is malformed;
the decoder never substitutes a later convenient witness. The global
first-event theorem establishes that every actual first-event witness gives
the required successful result.

## Proof composition

1. **Finite machines to literal BP2.** `SOnlyMachineNat` proves two-way
   halting simulation from arbitrary finite source machines and inputs to an
   all-zero dense-counter BP2 program. Every halted target's first counter is
   exactly `2*v+3`. The compiler executes actual initialization, guarded
   blocks, delays, restarts and falling-off halt.

2. **BP2 to UT19.** The `SOnlySimulation` modules prove actual assembled-word
   FIFO execution, temporal memory initialization, scheduled alignments,
   protected zero-decrement restart, and the first selected-18 event. The
   nonhalting proof covers every microstep through strictly progressing
   prefixes. At the first event, the first ordinary counter has a maximal
   16-run of length `4^(2*v+4)`.

3. **UT19 to the fixed CTS.** `SOnlySource` proves exact `19*n` boundary
   simulation for arbitrary finite words and identifies every interior event.
   A first tag event at n becomes the first CTS event at `19*n+17`. Empty
   states cannot generate an event. Compiler outputs satisfy
   `NoPrematureEmpty`, so exhaustion cannot precede the designated event.

4. **Actual S-stage coverage.** The exact-chain chronology is strengthened
   through the real response, job, clock, fuel and stage constructors.
   `SOnlyGlobalStages` preserves generated label/snapshot licenses at every
   actual contraction sample. C4 deletion, copied subtrees and rebuilt Local
   ancestors preserve the licensed frozen fields.

5. **First acceptance and every witness.** Before the first target response,
   source labels exclude target origins. Every proper response sample retains
   the old licenses; only the final contraction adds the selected target and
   its literal deleted carrier. `SOnlyGlobalFirstEvent` identifies first S
   acceptance at `firstJobPreResponseTime bits r + 57`, where r is the first
   CTS event index. Every matching shell at that sample has the same LLLR
   snapshot. Public current-state decoding reconstructs exactly the source
   event's word and output.

6. **End-to-end theorem.** `SOnlyUniversality` discharges the source-liveness,
   source-result and generated-origin conditions using the preceding
   compilers and transfers. `result_iff_first_event` quantifies only over the
   machine, natural input and requested result. `halting_iff_event` and
   `nonhalting_no_event` give the corresponding observation equivalences.

## Auxiliary bounds

Let R be the number of source registers, Q the number of labels and s the
sum of input values. Put `k=R+5Q`, `N=4k+1` clocks and `C=8k+3` BP2 counters.
The formal compiler has the kernel-checked bound

    L ≤ 2C(2s+9) + N(18C+2) + C + 4N + 4.

The actual compact initializer chooses
`depth=log2(L+2)+2`, giving memory width `W=2^depth≤4L+8`. Its literal seed
size and construction work are polynomial in C, L and W. Source naturals
written in binary can produce unary compiler blocks, yielding the stated
singly exponential bound in binary input size. This bound does not require
the more precise operation count of a particular Python implementation.

For a current occurrence tree of size m, the decoder's carrier recursion
makes one strict-descendant recursive call per layer. Input-size fuel gives
an exact all-input equivalent decoder; decoded word length is at most m.
Spine-list construction has a quadratic worst case. Charging each classifier
accordingly gives a safe cubic constructor/list bound, with polynomial
bit-operation overhead. [The decoder audit](lean-current-decoder-bound.md)
separates the checked simulation/size recurrences from the written audit of
individual imported parser operations.

The controller's all-input linear bound is part of the pinned formal
contract. The event cover and transition correctness are proved in Lean.

## Why the source model is universal

A finite-register `INC/DECJZ/HALT` machine simulates a Turing machine using two
base-B encoded stacks and finitely many scratch registers. Push is repeated
multiplication/addition by a fixed base; pop is quotient/remainder by that
base with the residue in finite control. All arithmetic macros terminate on
finite registers. Head movement pushes one stack and pops the other; empty
pop supplies blank. A permanently-zero scratch register implements
unconditional jumps. Finite output can be accumulated in register 0 before
halt.

[The explicit construction](universal-bp2-front-end.md#7-why-the-chosen-source-suffices-for-arbitrary-effective-computation)
gives the stack macros and a binary-word output convention. The same reduction is now instantiated by a checked literal three-register
compiler: [the conventional-Turing-machine theorem](formal-turing-universality.md)
proves exact tape-machine halting equivalence through the same S interfaces.
The register result theorem above continues to supply arbitrary numerical
output. Complete bit-cost analysis remains written mathematics.

## Verification and attribution

The final proof sources, exact theorem types, declaration dependencies,
clean-build records and fresh-kernel replay receipts are collected in the
[final verification report](final-verification.md). Independent source and
cross-layer reviews accompany the certificate.

Cinematic Strawberry supplies the generic pure-S encoding, finite controller
and scheduler construction. The fixed UT19 source and original machine ideas
are attributed to ais523 and the primary sources linked in the component
reports. This project provides the explicit source/event/output composition,
new formal source compilers and global first-event proofs, and the independent
reproduction and auditing code.
