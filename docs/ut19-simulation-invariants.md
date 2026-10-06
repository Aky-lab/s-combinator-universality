# Compact UT19 source simulation: counters, clock, restart, and first event

This gives an all-input mathematical correctness argument for the **unpadded**
encoder specified in [compact-universal-programs.md](compact-universal-programs.md#source-level-encoder-formulas)
and implemented in [`s_only/ut19.py`](../s_only/ut19.py). It uses the separately
proved [running-XOR memory lemma](running-xor-memory.md). The literal productions
and component design come from ais523's CC0
[UT19 construction](https://esolangs.org/wiki/UT19), especially its Global cycle,
Counters, and Halt behaviour sections. The source semantics are the numerical
version of [Brainpocalypse II](https://esolangs.org/wiki/Brainpocalypse_II#Numerical_version).
Sources checked 6 October 2026.

The argument is conditional on the precise grammar, encoding, and semantics
below. It establishes a designated-symbol event and a structural output at that
event, not the optional empty-queue cleanup, a new proof of Brainpocalypse II
universality, a generic CTS-to-S simulation, or S-combinator universality. It is
a written proof with independent finite checks, not a machine-checked theorem.

## 1. Exact statement and conventions

The source is a nonempty finite list of `L` commands `+x` or `-x`, using exactly
the dense labels `1,...,C`, where `C >= 1`. Values are unbounded natural numbers,
initially zero. Increment adds one. A decrement at a positive value subtracts
one and continues; at zero it sets that counter to one and returns to command
zero, preserving every other counter. Falling off the list halts.

Let `H=C+1` be the added halt counter, `N` the least power of two at least `L+3`,
and `W=2N`. There are `C+2` memory blocks, each with `W` cells. Their order is

```text
M_1 K_1 M_2 K_2 ... M_C K_C M_H K_H M_(H+1).
```

The expanded command list is `^`, the source commands, `$a`, `$b`, then `=`
padding to length `N`. Each expanded command uses two memory observations.
Memory initializers and width vectors are exactly those in the linked encoder
specification. Every initial counter is `[12,13,12,13]`; a single 19 precedes
the first memory. No cleanup padding is present.

This is a mathematical finite-word construction. Implementation limits can
refuse an oversized source or seed, and a bounded evaluator can stop before
reaching an event. The theorem applies to each successfully materialized seed;
it does not turn a resource-limit result into either halting or nonhalting.

Use the [continuous alternating semantics](alternating-tag.md#exact-source-convention):
one microstep removes one head symbol, appends its production in **take** phase
only, and toggles take/skip. Initially the phase is take. An empty queue stops.
The designated event is the **pre-transition** state with phase take and head
18. A skipped 18 or an 18 elsewhere in the queue is not an event.

**Theorem.** For every source program in this grammar, its compact seed has a
first designated event exactly when the source eventually falls off the end.
There is no earlier event or queue exhaustion. At that first event, the maximal
runs of symbol 16, in order, have lengths

```text
4^(x_1+1), ..., 4^(x_C+1),
```

where `(x_1,...,x_C)` is the source's final counter tuple. These runs can be
read structurally without rerunning the source or searching an execution trace.

### Passes and alignment bits

A pass processes exactly the symbols present at its entrance; its output is
the concatenation of their selected productions, in order. Write `F_g(w)` for
that output when `g=0` means the first symbol is taken and `g=1` means skipped.
The following pass begins at alignment

```text
g' = g XOR (|w| mod 2).
```

An interior component begins at `g XOR (length of its preceding prefix mod 2)`.
This identity concerns the length **being consumed**, not the length being
produced. FIFO order preserves the component decomposition between passes.

One halfcommand is three passes: Command, Parity, Reset. A memory observation
occurs at Command entrance, before that halfcommand updates the memory. The
local alignments `q,p,r` below refer to a component's Command, Parity, and Reset
entrances. For a standalone component they are exterior hypotheses; do not
infer that running it as a whole isolated queue supplies them.

## 2. Complete raw counter lemma

For `n >= 0` define the ordinary and protected words

```text
C(n) = [12,13]^(2^n),
T(n) = [12]^(2^(n+1)),
D    = T(1) = [12,12,12,12].
```

An ordinary source value `x` at a source-command boundary is `C(2x+1)`.
The exponent `n` is an internal counter value, not the source value.

Only these six productions are needed:

```text
12 -> [14,14,14,14]     13 -> [15]
14 -> [16,16]          15 -> [16,17]
16 -> [12,13]          17 -> [12,12,12,12].
```

### Increment

Starting with `C(n)` and `q=0`, exactly `2^n` copies of 12 are selected:

```text
Command             Parity                  Reset                  next Command
C(n)       ->       [14]^(2^(n+2))    ->     [16]^(2^(n+2))    ->   C(n+1).
```

The Parity and Reset words have even length and are constant-symbol words.
Exactly half their symbols are selected, independently of `p` and `r`.
Thus this equation is valid for both values of either exterior alignment.

### Decrement at positive exponent

Starting with `C(n)`, `q=1`, and `n >= 1` gives

```text
C(n) -> [15]^(2^n) -> [16,17]^(2^(n-1)).
```

The second arrow is independent of `p` because `2^n` is even. At Reset:

```text
r=0: [16,17]^(2^(n-1)) -> C(n-1),
r=1: [16,17]^(2^(n-1)) -> T(n).
```

The second case is essential: a nonzero decrement does **not** retain the
ordinary representation under odd Reset. The smallest example is
`C(1) -> [15,15] -> [16,17] -> D`, not `C(0)`. The global proof must rule out
such a nonzero decrement whenever a different counter causes odd Reset.

### Decrement at exponent zero

For `C(0)=[12,13]` and `q=1`, the Parity word is the singleton `[15]`:

| Parity `p` | Reset `r` | Reset word | Following Command word |
| --- | --- | --- | --- |
| 0 | 0 | `[16,17]` | `C(0)` |
| 0 | 1 | `[16,17]` | `D` |
| 1 | 0 or 1 | empty | empty |

The first row is a saturated exceptional case, not a negative exponent. The
second row will implement a source zero decrement. The third row will delete
the halt counter. None of these counter productions emits an 18.

### Protected counter

Both alignments of `T(n)` select `2^n` copies of 12. Consequently for either
`q`, either `p`, and either `r`,

```text
T(n) -> [14]^(2^(n+2)) -> [16]^(2^(n+2)) -> C(n+1).
```

In particular `D` increments to `C(2)` even when the requested command is a
decrement. A following ordinary increment produces `C(3)`, encoding source
value one. This protection lasts exactly one halfcommand: the result is
ordinary again.

Every Command counter word in this lemma is even, as is every Reset counter
word, including the empty exceptional word. The only odd Parity counter word
is the singleton produced by decrementing `C(0)`.

## 3. Width vectors determine both counter actions and global phases

Let `v_b(t)` be the width parity of memory `M_b` at Command observation `t`,
and let `g` be that Command pass's global alignment. Because all its counter
words are even, counter `k` has Command alignment

```text
q_k = g XOR XOR_(b=1..k) v_b(t),
g_Parity = g XOR XOR_(b=1..H+1) v_b(t).              (1)
```

Equivalently, specified alignments `q_1,...,q_H` and specified next phase `p`
uniquely determine the widths:

```text
v_1 = g XOR q_1,
v_b = q_(b-1) XOR q_b             for 2 <= b <= H,
v_(H+1) = q_H XOR p.                                (2)
```

This telescoping form gives a direct action-first derivation of the encoder's
vectors, rather than assuming that a memorized width table has the right effect.
For a source target `x`, write `J_b=[b=x or b=x+1]`, `S_b=[b=1]`, and
`F_b=[b=H+1]`. Since `S` and `F` have different positions, `S OR F = S XOR F`.
For `1 <= k <= H`,

```text
XOR_(b<=k) J_b = [k=x],
XOR_b J_b = 0,
XOR_b (S_b XOR F_b) = 0.
```

Substituting the published width pairs into (1), or deriving them from (2),
therefore gives the following exact schedule. `I` and `d` mean counter
alignment zero and one respectively, not a presupposition that decrement
closure is already safe.

| Marker | First half | Second half | Parity phases |
| --- | --- | --- | --- |
| `^` | `d` all, with global Command `g=1` | `I` all | 0, 0 |
| `+x` | `I` all | `I` at `x`, `d` elsewhere | 0, 0 |
| `-x` | `d` all | `d` at `x`, `I` elsewhere | 0, 0 |
| `=` | `d` all | `I` all | 0, 0 |
| `$a` | `d` all | `d` at `H`, `I` elsewhere | 0, 1 |
| `$b` | `I` all | `I` all | 0, 0 |

Except for the first half of `^`, the displayed Command phase is zero. The
last two halves `$b`, and the padding, will not be reached before the first
designated event; their rows only verify the full encoded vector definition.

For `$a`'s second half the only odd memory is `M_H`: the formula
`J_b AND NOT F_b` removes the `b=H+1` endpoint of the halt target. Thus ordinary
counters increment, the halt counter decrements, and global Parity is odd.

## 4. Global three-pass invariant

Every memory cell and inverter produces a two-symbol Parity component, and
every such component produces a two-symbol Reset component. Together with
the counter lemma, this gives

```text
g_Reset = g_Parity XOR (total Parity length mod 2),
g_next_Command = g_Reset,                           (3)
```

and every Reset component has the same alignment `g_Reset`. The second identity
uses the **even length of the Reset word**, not the generally variable lengths
of its Command productions.

In a nonhalting halfcommand, (1) makes `g_Parity=0`. If no `C(0)` decrements,
every Parity component is even. Every memory then has local `p=0`, global
Reset is zero, and the memory lemma's normal case applies. If exactly one
`C(0)` decrements, it is the only odd Parity component. That singleton has
local `p=0`, because all preceding components are even; local `p` becomes one
only **after** it. Equation (3) makes global Reset one. The memory lemma resets
all memories exactly, both those before the singleton (`p=0,r=1`) and those
after it (`p=1,r=1`). Its 18s occur only in positions skipped by this odd Reset.

This argument becomes a closure invariant only after ruling out other
decrements in the zero-producing halfcommand. The following source induction
does that; the claim is not true for an arbitrary vector of counter operations.

### Memory horizon without a circular assumption

At an epoch entrance every memory has its initial combined vector `a`. Assume
the previous halfcommands of that epoch were normal. Their local memory
alignments were `p=r=0`, so the proved memory recurrence applies with whatever
Command forcing actually occurred. Its observation theorem then supplies the
prescribed `v_b(t)` whenever `0 <= t < W`. Equations (1)–(3) and the counter
lemma determine the **current** halfcommand. It either continues normally,
resets every memory exactly to `a`, or enters the halt event. Thus using the
memory theorem to derive current alignments does not assume those alignments
for the current update.

Count observations from zero at the first half of `^`:

```text
^                         t=0,1
source command i (0-based) t=2i+2,2i+3
$a                        t=2L+2,2L+3.
```

The last needed observation satisfies `2L+3 <= 2N-3 = W-3`. An epoch cannot
exhaust the protected `W` observations: either it resets during a source
decrement, or it reaches the designated event during `$a`. A reset starts a
new epoch with `t=0`, `a` restored, and no residual forcing from the old epoch.
Neither the disturbance at observation `W` nor any later periodic behavior is
being used.

## 5. Initialization, source steps, and restart

Initially each ordinary and halt counter is `C(1)`. Processing the leading
19 takes one microstep, appends nothing, and leaves the phase skip at `M_1`.
Hence the component word begins with effective global Command alignment one.
There is no leading 19 on later resets; equation (3) supplies the same alignment.

The first `^` half has width vector `F`, so all counters decrement and global
Parity is zero. Each `C(1)` becomes `C(0)` without a zero decrement. The second
half increments all, restoring `C(1)`. The source is now at command zero with
all values zero, global Command zero, and memory time two.

At any ordinary source-command boundary maintain:

- Memory time `t=2i+2` for the source program counter `i` in the current epoch.
- Ordinary counter `k` is `C(2x_k+1)` and the halt counter is `C(1)`.
- Global Command alignment is zero.
- No selected 18 has occurred, and the queue is nonempty.

For `+x`, the first half increments every exponent, giving even exponents at
least two. The second increments target `x` and decrements every other counter.
No zero decrement is possible, so Reset stays even. The target's exponent
increases by two, while every other exponent returns to its old value. The halt
counter returns to `C(1)`. This is exactly the source increment.

For `-x`, the first half decrements every odd exponent, all at least one. It
is safe and gives exponent `2x_k` for each ordinary counter, and zero for the
halt counter. In the second half **only target `x` decrements**; every other
counter, including the halt counter, increments.

- If `x_x>0`, its exponent is at least two, so all Parity components are even.
  The target finishes at exponent `2x_x-1`; all other source values are
  unchanged. This is exactly the source nonzero decrement.
- If `x_x=0`, its singleton 15 is produced from at local `p=0`. Global Reset
  is odd. The target becomes `D`, every other counter is an increment and so
  remains ordinary with its original odd exponent, and the halt counter is
  `C(1)`. Every memory resets, and the following Command alignment is one.

In the second case there are **no nonzero decrements under odd Reset**, resolving
the otherwise dangerous `T(n)` branch of the counter lemma. The source step
sets its target to one and jumps to command zero; the target is represented
temporarily by `D` until the restarted `^` completes.

In that `^` first half, the ordinary odd exponents safely decrement, but `D`
increments despite its requested decrement, becoming `C(2)`. No singleton 15
is generated, hence no additional reset occurs. The second half increments
all counters. The protected target is now `C(3)`, every other source value is
unchanged, and the halt counter is `C(1)`. The boundary invariant is restored
at command zero with precisely the source post-restart state. There is exactly
one protected counter, so this also proves closure through arbitrarily many
source restarts.

The initial dummy and each restart dummy take finitely many additional passes.
This is a stuttering source simulation: a zero-decrement source step has its
ordinary next-boundary representation after the dummy, rather than immediately
at the intervening `D` state.

## 6. First selected 18 and exact output stage

When the source falls off the end with tuple `x`, the same boundary invariant
holds just before `$a`. Its first half safely decrements all counters:
ordinary counter `k` is now `C(2x_k)`, and the halt counter is `C(0)`.

The second half increments every ordinary counter but decrements the halt
counter. It deliberately makes global Parity odd. During that Parity pass:

- Every memory and ordinary-counter component before `K_H` has even length,
  so its local Parity alignment is one.
- Each ordinary counter is a constant 14-word and produces the Reset word
  `[16]^(2^(2x_k+2)) = [16]^(4^(x_k+1))`, independent of that alignment.
- The halt counter is the lone 15. Its local Parity alignment is one, so it
  is skipped and produces nothing.
- The final memory has local Parity alignment zero, because the singleton
  has changed the prefix parity.

The total Parity word is odd, so global Reset is `1 XOR 1 = 0`. Every cell in
the first memory has produced `[18,10]`; every inverter there, if present,
has produced `[18,4]`. The very first cell exists (`W >= 1`), so the **first
symbol of the entire Reset queue is 18 in take phase**. The event is therefore
at this Reset entrance, before even one of its symbols has been consumed.
All ordinary counter words above remain intact in the same queue.

There cannot have been an earlier selected 18. Command and Parity words contain
no 18s. Counters never produce one. In a normal Reset all memory local Parity
alignments were zero, so no memory 18 was produced. On a source zero decrement,
18s may be produced after the singleton, but their Reset alignment is odd and
they are skipped. Those exhaust all earlier cases by the source induction.

After entering `$a`, the event is reached after **five complete passes**: the
three of its first half, then Command and Parity of its second. `$b` and the
padding have not executed. Continuing the literal production `18 -> [18]`
would not itself be a native stop; the theorem concerns the designated event.

### No premature exhaustion, and the converse

Every finite Command pass produces at least two symbols from each memory cell;
the same is true from each Parity pass. A normal/reset Reset pass also produces
at least two symbols per cell. Thus the next complete queue is nonempty before
the halt event. Within a pass, unprocessed original symbols remain until the
last original symbol, after which the nonempty output remains. Each pass is
finite because its entrance word is finite, and every production is finite.

Consequently a nonhalting source execution yields indefinitely many finite,
nonempty, event-free simulated steps. A halting source execution reaches the
event after finitely many such passes. Conversely the induction allows an
event only in `$a`, which is reached only by source fall-through. This proves
both directions of the theorem, rather than inferring nonhalting from a
bounded unsuccessful event search.

## 7. Structural output language and one-hot event offset

For each memory `b`, let `a_(b,i)` be its fixed initializer bits. Immediately
before the first event, each memory before the deleted halt counter is exactly

```text
R_b = product_(i=0..W-1) ([18,10] [18,4]^(a_(b,i))).
```

The final memory has the form

```text
T = product_(i=0..W-1) ([z_i,10] [4,4]^(a_(H+1,i))),
    where each z_i is 10 or 11.
```

The final event queue, with phase take, is therefore

```text
R_1 16^(4^(x_1+1)) R_2 16^(4^(x_2+1)) ...
R_C 16^(4^(x_C+1)) R_H T.                           (4)
```

Each `R_b` and `T` is nonempty and contains no 16; every displayed counter run
has length at least four. The halt counter contributes no run. Thus the maximal
16-runs are exactly the `C` source counters, in label order, even though the
last two memory blocks are adjacent without a counter between them.

A uniform result decoder scans the event word once, records those run lengths,
checks that each is a power of four with exponent at least one, and returns
`log_4(length)-1` for each. Integer repeated division by four suffices; floating
logarithms are unnecessary. The decoder uses neither source execution nor a
history search. A decoder can validate (4) against the supplied program for a
more restrictive structural language; a simple run decoder alone is not a
reachability certificate for arbitrary words.

For the fixed 38-phase one-hot CTS, use published-label code
`E(s)=0^(s-1) 1 0^(19-s)`. The
[exact one-hot event lemma](alternating-tag.md#selected-symbol-event-and-exact-offset)
places the event at phase 17 with a leading one. By then exactly 17 zeroes
of the initial `E(18)` have been consumed and no appendant has yet been added
in that block. If `y` is the CTS word at the event, then

```text
E(the whole tag event word) = 0^17 y.
```

The event word `y` starts `10`; it is not a block-boundary representation.
Restore the fixed zero prefix, validate and decode 19-bit one-hot blocks,
then apply the counter-run decoder. Calling a phase-zero boundary decoder
directly on the phase-17 word would be wrong. By the one-hot lemma, the first
tag event is also the first corresponding CTS event. None of this supplies an
S-level event selector or an S-level output reader.

## 8. Independent bounded checks

[`tests/test_ut19_counter_kernel.py`](../tests/test_ut19_counter_kernel.py)
contains its own literal production dictionary. Its kernel and integration
checks execute no external compiler, source interpreter, or production encoder.
An explicit FIFO pass is cross-checked against componentwise concatenation;
memory vectors are independently derived from desired counter alignments by
equation (2), using a direct subset-sum initializer. A separate test compares
those vectors with the production implementation.

The suite covers:

- Every exterior Parity/Reset alignment for ordinary increments through
  exponent 10 and positive decrements through exponent 10.
- All four singleton-decrement cases, including the exceptional saturation,
  protected restart, and deleted halt-counter branches.
- Both Command alignments and all exterior alignments of protected counters
  through exponent eight; the `D -> C(2) -> C(3)` restart.
- Width telescoping for all targets and signs with one through eight source
  counters, including both halves of every marker.
- 204 complete legal instruction boundary cases with one through three
  counters initially valued zero through two, including 34 reset/dummy cases.
- 39 halt-stage cases with one through three counters: exact first-head event,
  skipped halt singleton, preserved result runs, memory alphabets, and the
  17-bit one-hot restoration.
- Canonical all-zero starts that increment then decrement one through three
  counters, checking four-symbol result runs for final source value zero.
- The initial 19's exact effect on both component alignment and pass output.

Run this bounded suite from the repository root:

```sh
timeout 180s sh -c 'ulimit -v 524288; python -B -m unittest discover -s tests -p test_ut19_counter_kernel.py -v'
```

Verified 6 October 2026: all ten tests passed under the stated 180-second,
512-MiB limits. The finite tests check implementations and edge cases; the
algebra and induction above establish the stated all-input result.
