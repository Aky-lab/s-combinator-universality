# Smaller fixed universal CTS candidates

Research checked 6 October 2026.

## Result

The best new candidate is **ais523's UT19 followed by the elementary one-hot
2-tag-to-CTS translation**: a completely specified, fixed **38-phase ordinary
binary CTS**, with **760 appendant bits** and a maximum appendant length of
**76 bits**. Its author supplies a constructive finite-word universality
argument and a finite-input compiler. The compiler's initial-word size is
polynomial in its explicitly written source program, despite the exponential
representation of counter values during execution.

The 38 appendants below stay fixed across source programs and inputs.
The published universality argument is an author-written construction. The
[compact-source proof](ut19-simulation-invariants.md) develops its counter,
memory, restart, first-event, and result-reading invariants for the unpadded
encoder. The optional empty-queue cleanup has a separate source discrepancy.

## 1. UT19: provenance and exact fixed program

The [UT19 article](https://esolangs.org/wiki/UT19) identifies the construction as
ais523's 2023 work. Its [revision history](https://esolangs.org/w/index.php?title=UT19&action=history)
records the initial proof as the author's edit on 9 September 2023 and the last
author edit as revision `122761`, 31 January 2024. The current page identifies
its [permanent revision as `154545`](https://esolangs.org/w/index.php?title=UT19&oldid=154545),
26 March 2025; the last change adds an alphabetical transcription. The numerical
table and detailed simulation argument are the primary source used here. The
page declares a CC0 public-domain dedication. This is original author research
hosted on a wiki, not a peer-reviewed theorem or a machine-checked proof.

UT19 has deletion number 2, alphabet `{1,...,19}`, and these productions:

```text
 1 -> 2 3
 2 -> 4 4
 3 -> 18 4
 4 -> 1 1 19
 5 -> 7 9
 6 -> 8 9
 7 -> 10 10
 8 -> 11 10
 9 -> 18 10
10 -> 5 6
11 -> 6 5 19
12 -> 14 14 14 14
13 -> 15
14 -> 16 16
15 -> 16 17
16 -> 12 13
17 -> 12 12 12 12
18 -> 18
19 -> epsilon
```

Let `P_i` be row `i`, and define the 19-bit code

```text
E(i) = 0^(i-1) 1 0^(19-i),       1 <= i <= 19.
```

Extend `E` by concatenation, including `E(epsilon) = epsilon`. The following is
a full, unambiguous specification of the proposed binary CTS, indexed from 0:

```text
alpha_(i-1) = E(P_i),            1 <= i <= 19
alpha_j     = epsilon,         19 <= j <= 37
initial phase = 0
initial binary word = E(w), where w is the encoded UT19 source input
```

Derived table sizes:

| Quantity | Value |
| --- | ---: |
| Phases | 38 |
| Nonempty appendants | 18 |
| Total production symbols before binary encoding | 40 |
| Total appendant bits | 760 |
| Total appendant ones | 40 |
| Maximum appendant length | 76 |
| Binary input length for an `n`-symbol UT19 word | `19n` |

These counts follow directly from the displayed table, not from executing a
compiler. The one-hot method is the construction in
[Cook 2004, Section 2.2, printed pages 7–8](https://wpmedia.wolfram.com/sites/13/2018/02/15-1-1.pdf).

### Why this is an ordinary CTS

In the first 19 phases a one-hot symbol `i` selects exactly `E(P_i)`. The next
19 phases consume another encoded symbol without appending anything. With at
least two source symbols present, 38 ordinary CTS steps therefore implement
one standard 2-tag step. All encoded appendants have lengths divisible by 19,
so block alignment is preserved.

For short queues the precise convention matters. The CTS continues alternating
between producing from an encoded symbol and ignoring an encoded symbol,
including symbols newly appended after the original queue has become short.
It halts only when the binary queue is empty. This is UT19's third halting
convention, the continuous alternating convention. It is not automatically the
convention that stops as soon as a 2-tag queue has fewer than two symbols, nor
the convention that resets alternation after a short queue.

More explicitly, the source state for that convention is `(w, parity)`, with
`parity` either `produce` or `ignore`, initially `produce`. A source microstep
first tests whether `w` is empty; if so it halts. Otherwise it removes the head
symbol, appends its production exactly when parity is `produce`, and toggles
parity. A singleton in produce parity can therefore supply the symbol removed
by the following ignore step. UT19's article explicitly supports this
semantics; an even-length invariant is not its justification.

### A designated halt event, separate from empty-queue termination

The source article also uses symbol 18 as a halt instruction **only when it is
about to produce**. In the displayed CTS this event is exactly

```text
current phase = 17 and current first bit = 1.
```

An 18 in the ignored source-symbol position is consumed in the empty half of
the 38-phase cycle and cannot cause this event. Merely finding an 18 anywhere
in the queue is incorrect: normal, nonhalting intermediate words can contain
ignored 18s. The actual appendant at phase 17 is `E(18)`, so this is a designated
nonempty event, not a native CTS halt instruction.

Both source and CTS predicates are **pre-transition** observations. The CTS
has consumed the 17 leading zeroes of `E(18)` when its predicate becomes true,
but has not consumed the one or appended `E(18)` yet. Its source block boundary
was at phase 0; ignored blocks begin at phase 19. This partial-block offset
must be included in an output decoder.

The [compact-source proof](ut19-simulation-invariants.md) establishes this
predicate's correspondence with source halting for the stated encoder grammar.
Its transfer to S uses the separate [event-composition interface](event-composition.md).

## 2. What universality the source argues

UT19 simulates **Brainpocalypse II**, a finite program of increments and
conditional decrements of finitely many unbounded natural-number counters.
Attempting to decrement zero instead makes that counter 1 and restarts the
program; falling off the end halts. All counters start at zero. The UT19
article gives separate component arguments for its three-pass cycle,
running-XOR program memory, counters, restart, and halting.

The [Brainpocalypse II specification and proof](https://esolangs.org/wiki/Brainpocalypse_II)
is pinned by the page to [revision `172507`](https://esolangs.org/w/index.php?title=Brainpocalypse_II&oldid=172507).
It reduces the Waterfall Model to Brainpocalypse II, including initialization
and a standard halt. The
[Waterfall Model's proof](https://esolangs.org/wiki/The_Waterfall_Model)
([revision `193038`](https://esolangs.org/w/index.php?title=The_Waterfall_Model&oldid=193038))
in turn reduces counter machines, using the one-decrement-continuation
construction established in
[The Amnesiac From Minsk, level 1](https://esolangs.org/wiki/The_Amnesiac_From_Minsk)
([revision `173298`](https://esolangs.org/w/index.php?title=The_Amnesiac_From_Minsk&oldid=173298)).
These pages also declare CC0. This is a finite-input computation route; no
infinite periodic background supplies a program or work space.

The input compiler may vary the Brainpocalypse II program: that program lives
in the **UT19 queue**, while the 19 tag productions and 38 binary appendants
remain fixed. An arbitrary-machine/input front end must use restart-safe input
initialization: a naive increment prefix would run again after every source
restart. The BP2 article gives a marker-and-cancellation construction for this
purpose. That earlier compilation layer is separate from the compact encoder.

The source distinguishes:

- **Standard halt:** counters may retain nonzero results. The UT19 article
  states that their values can be recovered at a halt-symbol event.
- **Perfect halt:** all source counters are zero. The article additionally
  arranges cleanup so the queue eventually disappears under its empty-queue
  convention.

The first interface retains results. The
[first-event grammar](ut19-simulation-invariants.md) specifies maximal runs of
symbol 16 with lengths `4^(x+1)`, giving a uniform
[structural counter decoder](ut19-readout.md).
The second interface erases results during its separate cleanup phase.

## 3. The finite-input compiler and its size

The article links the author's
[Brainpocalypse II-to-UT19 Perl compiler](http://nethack4.org/esolangs/bp2-to-ut19.pl).
The HTTP source was retrieved and inspected as text on 6 October 2026; the
HTTPS endpoint timed out/returned 502 in the available retrieval routes.

```text
Retrieved size: 5,006 bytes
SHA256: 7a648e7f7762a87812e17370e80d18d4e09d050eb627c0ba64ef6b26d4ba2166
```

No immutable repository revision was found for that file. The digest pins the
inspected bytes; the URL itself is mutable. No license notice appears in the
file, so the wiki's CC0 status does not establish a license for this separately
hosted implementation. Reuse of that implementation has a licensing ambiguity;
an independent implementation can instead be derived from the openly published
construction.

The following bound is **static accounting of what this file prints**, not a
claim that its output has been validated by execution.

Let:

- `L >= 1` be the number of explicit numeric increment/decrement commands.
- `C = max(counter label) - min(counter label) + 1` be the span of used labels.
  Relabel densely to avoid huge unused gaps; this language's numeric syntax
  permits that without changing its computation.
- `N = 2^ceil(log2(L+3))`.

The compiler adds one restart-initialization command and two halt commands,
pads the expanded program to `N` commands, and generates `2N` running-XOR
entries in each of `C+2` program-memory blocks. There are `C+1` counters,
including the extra halt counter, all initialized by four symbols each. One
leading 19 supplies the initial odd alignment.

For block `j`, let `I_j` be the number of transformed entries that receive an
extra inverter (`0 <= I_j <= 2N`), and let `t_j` be the cleanup top-up count
(`0 <= t_j <= 2047`). Its memory output contains exactly

```text
4N + 3I_j + 2t_j
```

symbols. Consequently its full printed seed satisfies

```text
|w| = 1 + 4(C+1) + sum_j (4N + 3I_j + 2t_j)
    <= 1 + 4(C+1) + (C+2)(10N + 4094).

|E(w)| <= 19 * [1 + 4(C+1) + (C+2)(10N + 4094)].
```

For example, `L=1, C=1` gives `N=4` and an upper bound of **235,809 binary
seed bits**, not an observed output size. All starting counters are zero, so
the exponential representation of *runtime counter values* does not force
an exponential seed at this compilation stage. This bound is in the explicitly
written Brainpocalypse II representation; it does not by itself bound the
cost of compiling an arbitrary binary-encoded source into that representation.

Removing cleanup padding gives much smaller examples. The construction below
specifies that variant; its execution and output contract are established in
the [compact-source proof](ut19-simulation-invariants.md).

### Source-level encoder formulas

These formulas define a small independent encoder. Use a nonempty numeric
program with dense labels `1,...,C`; the added halt counter is `C+1`. Prepend
the initialization marker `^`, append halt markers `$a,$b`, then append idle
markers `=` to reach the power-of-two length `N` above.

There is one memory block at each position `b=1,...,C+2`, immediately before
counter `b` when it exists. Set `S=[b=1]` and `F=[b=C+2]`. For a command on
counter `x`, set `J=[x=b or x=b-1]`; for either halt marker use `x=C+1`.
Each expanded command contributes two bits to that block's desired width-parity
sequence `v`:

```text
^       -> (F, 0)
=       -> (S OR F, 0)
+x      -> (0, J XOR S XOR F)
-x      -> (S OR F, J)
$a      -> (S OR F, J AND NOT F)
$b      -> (0, 0)
```

Each `v` has length `2N`. The running-XOR initializer is the following binary
linear transform, indexed from zero:

```text
a_i = XOR of v_j over j whose binary set bits include all set bits of i.
```

Equivalently, recursively replace `(first half, second half)` by
`(first half XOR second half, second half)` until reaching individual bits.
For each transformed bit, in index order, emit

```text
A = [5,6]          when a_i=0
B = [5,6,1,1,19]   when a_i=1.
```

Begin the whole queue with `[19]`; append each memory block and then
`Z=[12,13,12,13]` for its counter, except that no counter follows the last
memory block. These are all-zero source counters, including the halt counter.
This is the compact, no-cleanup-padding variant. The inspected compiler
additionally appends `t_b` copies of `[1,1]` after each memory block, before
its counter, with the residue targets in the discrepancy table below.

For this no-padding variant the exact symbol count is
`1+4(C+1)+4N(C+2)+3 sum_b I_b`, bounded by `1+4(C+1)+10N(C+2)`.
Dense relabeling gives `C <= L`, so this particular encoder's initial-word
size is quadratic in explicit source command count in the worst case.

### Small hand-checkable seed for `+1`

The one-command source program `+1` starts counter 1 at zero, increments it,
and halts retaining result 1. Here `C=1`, `N=4`, and the expanded program is
`[^,+1,$a,$b]`. Its three parity vectors and transformed vectors are:

```text
before counter 1: v=00001000, a=10001000
before counter 2: v=00010100, a=00111100   (counter 2 is the halt counter)
after counter 2:  v=10011000, a=11111000
```

With `A,B,Z` as above, the compact initial queue is exactly

```text
[19]
B A A A B A A A Z
A A B B B B A A Z
B B B B B A A A
```

It contains `1+22+4+28+4+31 = 90` tag symbols, hence **1,710 CTS input bits**,
with source parity `produce` and CTS phase 0. This is a hand-derived seed
specification; execution validation is a separate fixture.

For this same example the inspected padded compiler would add respectively
1,970, 2,034, and 2,012 copies of `[1,1]`, yielding 12,122 tag symbols or
230,318 bits by static accounting. All three padding counts are even. Each
such pair turns into an inverter component after the first pass; pairs of
inverters have neutral width parity during normal computation. The
[compact-source proof](ut19-simulation-invariants.md) establishes the unpadded
variant directly from its component grammar and width vectors.

### Restart and nonhalting fixtures

Use the same `A,B,Z` definitions and envelope
`[19] block1 Z block2 Z block3`. A transformed bit 0 denotes `A`, and 1 denotes
`B`.

The source program `-1` fails its first decrement, sets its counter to 1,
restarts, then decrements to 0 and halts. Its expanded program has `N=4`:

```text
block 1: v=00111000, a=11011000
block 2: v=00010100, a=00111100
block 3: v=10101000, a=10101000
```

This again has 90 tag symbols and 1,710 binary seed bits.

The source program `-1 -1` never falls through: after the initial restart,
every run decrements 1 to 0 and then restarts by attempting the second
decrement. Here the expanded program is
`[^,-1,-1,$a,$b,=,=,=]`, so `N=8`:

```text
block 1: v=0011111000101010, a=0011110010000010
block 2: v=0001010100000000, a=1100001100000000
block 3: v=1010101000101010, a=1000000010000010
```

This has 144 tag symbols and 2,736 binary seed bits. Source nonhalting follows
from its two-command semantics. The [executable fixture](ut19-fixtures.md)
also certifies an exact repeated tag configuration, including parity, with an
event-free prefix and cycle. The general source proof covers arbitrary valid
programs independently of this recurrence certificate.

### Interfaces of the symbol-18 construction

The [source proof](ut19-simulation-invariants.md) and
[one-hot lemma](alternating-tag.md) establish the first four items and the CTS
part of the fifth. The S composition requires its corresponding observer:

1. The initialization, three-pass macrocycle, and running-XOR memory agree with
   the source counter program after any finite number of source restarts.
2. Producing from 18 is impossible in every nonhalting valid macrocycle,
   including transient passes and ignored occurrences of 18.
3. A source fall-through halt reaches a producing 18 after finitely many tag
   microsteps, without earlier queue exhaustion or a spurious halt event.
4. The first such event retains a specified, structurally recoverable output
   counter. Its stage and partial-block offset determine the decoder; no source
   interpreter or unbounded search for an earlier configuration is hidden in
   the observation.
5. One-hot simulation transfers that same event to phase 17 plus leading 1;
   the S readout then transfers it through the existing event-composition
   hypotheses.

Ordinary empty-queue halting is a separate theorem requiring perfect-halt
cleanup and resolution of the residue discrepancy.

### Concrete source discrepancies and edge cases

The article's empty-halting paragraph specifies persistent-component counts
modulo 2048 as follows:

| Memory block | Article | Inspected compiler |
| --- | ---: | ---: |
| Before first counter | `-2` | `-68` |
| Before halt counter | `-68` | `-2` |
| Other pre-counter blocks | `1024` | `1024` |
| After halt counter | `-23` | `-23` |

The first and pre-halt targets are swapped in compiler lines 130–138. This is
a reproducible source disagreement, **not a demonstrated counterexample** to
either version. The correct cleanup needs to be established independently.
The compiler's padding is repeated `[1,1]` pairs, whereas its ordinary memory
inverter is `[1,1,19]`; the transient first-pass behavior also needs to be
accounted for, not silently normalized away.

Other static caveats: the parser's truth test rejects the numeric label 0,
and an empty source program has no properly established minimum counter label.
Start with nonempty programs and dense positive labels. The generic language
semantics do not require these implementation restrictions.

## 4. Alternatives and exclusions

- **UT22:** the same author's no-empty-tag-production variant. Its explicit
  table gives 44 binary CTS phases, 968 appendant bits and maximum length 88
  by the same translation. It adds cost for a restriction the current CTS
  backend does not require; it shares the proof and encoding questions.
- **Cook 2004 plus a fixed standard binary UTM:** Section 2.1 uses `10m` tag
  symbols for an `m`-state binary machine; Section 2.2 gives `20m` CTS phases.
  With the standard 15-state binary machine in
  [Neary–Woods 2009, Table 16 and Section 3.5](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf),
  that is a prospective **300-phase** construction. The table is reconstructible
  from the two sources, but was not instantiated here. Its tape halves are
  represented by unary multiplicities of binary integers, retaining exponential
  seed growth. Cook's presentation does not specify the needed halt adapter;
  the UTM's undefined `(u10,c)` transition needs an explicit event interpretation.
  [Cook 2009, version 1, Section 1.2](https://arxiv.org/pdf/0906.3248v1) gives
  an empty-production halt recipe in a related compiler, but its literal
  endpoint-marker construction yields 960 phases for that machine. Transferring
  the recipe into the 300-phase special case would need verification.
- **Neary's direct binary-TM-to-CTS construction:** its linear represented-tape
  input length is attractive, but `120Q+242` phases gives 2,042 phases at
  `Q=15` even before clarifying state-count/halting conventions. The printed
  right-transition omission still needs independent completion. The existing
  482-phase all-left fixture establishes neither a universal source machine nor
  that missing half of the compiler.
- **Two-symbol tag systems:** Neary's
  [2015 binary-tag universality result](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf)
  does not mean deletion number 2. A small alphabet with a large deletion
  number is not a tiny 2-tag or few-phase CTS front end.
- **Spiral Rise's five-symbol tag translation:** its
  [author's page](https://esolangs.org/wiki/Spiral_Rise) explicitly leaves the
  lookup-table/universality step unproved, and its natural halt can become a
  nonempty loop. It is not a proven replacement.
- **Weak and semi-weak small TMs, Rule 110 backgrounds, and tiny illustrative
  CTSs:** these do not supply a finite-word universal program merely because
  their model or an infinite-background simulation is universal. In particular,
  a tag table obtained from the weak `(2,3)` machine is not automatically
  universal on finite words.

## 5. Construction status and next checks

- **Source compilation:** [three complete source fixtures](ut19-fixtures.md),
  including an exact nonhalting recurrence, and a general
  [written simulation proof](ut19-simulation-invariants.md).
- **Fixed binary endpoint:** the [one-hot translation](alternating-tag.md)
  provides exact microstep counts, singleton semantics, and the phase-17 event.
- **Native controller:** the dispatcher has
  `32*38 - 7 + 20*760 + 2*40 = 16,489` expanded nodes. Whole-controller
  construction and native execution have separate resource costs; the
  [code-sharing representation](pooled-selector.md) addresses repeated literals.
- **S observation and output:** compose the fixed source event and result
  reader with the current-tree S interfaces. This is the next simulation layer.
- **Earlier universal-machine compilation:** make restart-safe initialization
  and the BP2 output convention explicit. The 300-phase Cook/standard-UTM route
  remains a scholarly alternative with a different initial-word size cost.
