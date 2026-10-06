# A uniform finite-input counter-machine front end for BP2

This is a written mathematical reduction, with independent finite checks in
[`tests/test_universal_bp2_frontend.py`](../tests/test_universal_bp2_frontend.py).
It supplies the previously separate **standard counter machine/input → BP2**
obligation. The construction is explicit, with its quantified invariants and
fixed output convention stated below. The separate native S controller premises
are tracked in [the proof roadmap](proof-dependencies.md).

## 1. The interface and theorem

A source machine has finitely many registers `r_1,...,r_d` in the natural
numbers, with `d >= 1`, finitely many labeled instructions, an entry label,
and these instructions:

* `INC(i,t)`: increment `r_i`, then go to `t`;
* `DEC(i,t_plus,t_zero)`: if `r_i > 0`, decrement it and go to `t_plus`;
  otherwise leave it zero and go to `t_zero`;
* `HALT`.

The finite input is a tuple of natural initial register values. The result of
a halting computation is `r_1`. Multiple halt labels can be merged. Register
and instruction identifiers can be effectively renumbered, and unreachable
instructions need not be removed.

**Front-end theorem.** There is a total computable construction `B(M,a)` of a
nonempty finite numerical BP2 program, using exactly the dense positive labels
`1,...,C`, such that, from **all-zero** BP2 counters:

1. `B(M,a)` falls off its end if and only if `M` halts on `a`.
2. If the source halts with result `n`, the first BP2 counter is `2n+3` at
   termination.
3. Consequently the fixed, source-independent arithmetic reader
   `D(x_1,...,x_C) = (x_1-3)/2` recovers `n` on every compiled halting run.
   A defensive reader rejects an empty tuple, or a first value below 3 or even.

This is the repository's precise BP2 semantics: increment adds one; decrement
at a positive value subtracts one and continues; decrement at zero sets that
counter to one and restarts the entire program, retaining all other counters.
No initially nonzero register, implicit input channel, optional output
extension, tie-breaking convention, or interpreter trace is part of the
interface. Code size may depend on both `M` and `a`; no efficiency claim is made.

The source is a standard universal finite-register model. For completeness,
its connection to Turing machines is described in section 7, rather than
assuming that an esolang's “Turing complete” category is a proof.

## 2. Source attribution and the exact gap being filled

The three primary author pages below were checked on 6 October 2026. They
explicitly release their text under CC0. Their constructions are credited to
ais523; the Waterfall page also credits zzo38 for an independent earlier model.

* [Brainpocalypse II, revision 172507](https://esolangs.org/w/index.php?title=Brainpocalypse_II&oldid=172507),
  Numerical version and Computational class: the restart semantics,
  marker-and-cancellation initialization, two-cell clock simulation, and halt
  marker.
* [The Waterfall Model, revision 193038](https://esolangs.org/w/index.php?title=The_Waterfall_Model&oldid=193038),
  Semantics and Computational class: uniform downward clock motion,
  nonnegative trigger rows, undefined simultaneous zeroes, and the idea of
  removing signed trigger changes by a uniform offset.
* [The Amnesiac From Minsk, revision 173298](https://esolangs.org/w/index.php?title=The_Amnesiac_From_Minsk&oldid=173298),
  level 1, Implementation in and of other languages: increment chains and
  the paired decrement chains/control counters.

The explicit transition tables, recovery-clock normal form, fixed output
coordinate, proofs, and local test code here were derived for this repository.
No external interpreter or compiler code was copied or executed. In particular,
the Waterfall page's informal state-number sketch is not treated as a complete
compiler: this document supplies its own full rows and intermediate invariants.

## 3. General counter programs to amnesiac positive counters

### 3.1 A normalized intermediate model

An amnesiac machine has finitely many positive counters `c_i >= 1`. Each counter
has three fixed successor actions `p_i,s_i,f_i`. Actions are `+i`, `-i`, or
`H`. Executing `+i` increments `c_i` and continues at `p_i`. Executing `-i`
decrements when `c_i > 1` and continues at `s_i`; at `c_i = 1` it leaves the
counter unchanged and continues at `f_i`. `H` halts. Initial values and initial
action are finite parts of the description.

This is a normalized tail-call presentation of the level-1 construction. We
prove the needed simulation directly, so no literal-format start/stop rule is
assumed. To obtain the article's literal conventions one can add a first boot
counter whose increment enters the chosen action, and implement `H` using a
fresh counter whose increment trigger increments itself. The compiled reachable
chain operations below never rely on an accidental self-trigger halt.

### 3.2 Complete chain construction

Keep a data counter `D_i = r_i+1` for each original register, in that order.
All additional counters start at 1. Let `E(q)` denote the action entering
source instruction `q`; define it as follows:

* an increment instruction `q` gets a counter `I_q` and `E(q)=+I_q`;
* a decrement instruction `q` gets counters `S_q,F_q,U_q,V_q` and
  `E(q)=+S_q`;
* a halt instruction has `E(q)=H`.

List the increment instructions in any effective order, and the decrement
instructions likewise. A chain's “next” means the next counter in that list;
the last failed-decrement successor can be `H`. That last edge is unreachable
in every chain scan used in the proof. If a chain is empty, all references
that would scan it are unreachable and can be `H` too.

Use the following three-successor table. A dash means an unused successor,
which is assigned `H` to make the program total.

| Counter | After increment | After successful decrement | After failed decrement |
|---|---|---|---|
| original `D_i` | `-I_first` | `-S_first` | `-F_first` |
| `I_q`, for `INC(i,t)` | `+D_i` | `E(t)` | `-I_next` |
| `S_q`, for `DEC(i,t_plus,t_zero)` | `+F_q` | `-V_q` | `-S_next` |
| `F_q` | `-D_i` | `-U_q` | `-F_next` |
| `U_q` | `-F_first` | `E(t_plus)` | `+V_q` |
| `V_q` | `-S_first` | `E(t_zero)` | `+U_q` |

In the `F_q` row, `i` is the register decremented by instruction `q`.
The initial action is `E(q_start)`.

### 3.3 Invariant and proof

At an instruction-entry boundary, every auxiliary counter is 1, the original
data counters are `r_i+1`, and the next action is `E(q)`. A scan of a chain
containing exactly one 2 and otherwise 1s walks over the 1s by failed
decrements, changes the unique 2 to 1, and takes its successful successor.
It cannot reach the end-of-chain fallback. Counters preceding and following
the selected counter remain 1.

For `INC`, entering `+I_q` marks `I_q=2`, then increments `D_i`, then scans
the `I` chain. That scan restores `I_q=1` and enters `E(t)`. Thus precisely one
source increment is performed and all auxiliary values are restored.

For `DEC`, entering `+S_q` marks `S_q=2`, then `F_q=2`, and attempts `-D_i`.
If successful, the `S` scan resets `S_q`, then `-V_q` fails, causing `+U_q`.
Its increment starts the `F` scan; this resets `F_q`, then successfully
decrements the now-2 `U_q` and enters `E(t_plus)`. The sequence of nontrivial
auxiliary changes is

```text
(S_q), +(F_q), -(S_q), +(U_q), -(F_q), -(U_q).
```

If the data decrement fails, the symmetric sequence is

```text
(S_q), +(F_q), -(F_q), +(V_q), -(S_q), -(V_q),
```

ending at `E(t_zero)`. Again all auxiliaries are 1. The control counter that
is tested unsuccessfully remains 1; failed decrements do not create a zero.

Every source step therefore has a finite nonempty simulation, there is no
internal divergence, and `H` is reached exactly for source `HALT`. The data
counter `D_1` is `r_1+1` at a halting boundary. Shared source registers and
multiple decrement call sites cause no ambiguity: the paired chains preserve
the call site explicitly.

## 4. Amnesiac counters to tie-free integer Waterfall

### 4.1 Exact Waterfall convention

Use finitely many integer clocks, initially strictly positive. At an event,
subtract their common minimum. Exactly one clock must be zero. If its trigger
row is zero, signal the distinguished halt event; otherwise add its fixed
nonnegative row and continue. Every nonhalt diagonal entry must be positive.

The author page permits treating the zero-row case as infinitely many zero-time
triggers instead of detecting halt. Our theorem uses the explicit **first
zero-row event**. BP2 compiles that event into actual falling-off termination;
it does not depend on an implementation electing to terminate that loop.

### 4.2 Clock layout and full trigger formulas

For `k` positive amnesiac counters create:

* data clocks `X_i`, with `X_1` corresponding to original output register `r_1`;
* action clocks `Q_a` for all actions `a` in `{+i,-i : 1<=i<=k} union {H}`;
* recovery clocks `T_i`, one per amnesiac counter.

There are `N=4k+1` clocks. Put `X_1` first; the remaining order is arbitrary
but effective and fixed throughout compilation. At a normalized action event
with amnesiac values `c` and action `a`, the desired vector `V(c,a)` is

```text
X_i = 2c_i;
Q_a = 0, all other Q clocks = 4;
all T clocks = 4.
```

Start the actual Waterfall machine at `V(c_initial,a_initial) + 1` in every
coordinate. Thus all initial values are positive and the first unique event
is the desired action.

Write `e_Z` for the unit vector of clock `Z`, and `1` for the all-ones vector.
For each nonhalt clock define the following **signed** row `b`:

```text
b[Q_(+i)] =  2 e_Xi + 4 e_Q(+i) - 4 e_Q(pi)
b[Q_(-i)] = -2 e_Xi + 4 e_Q(-i) - 3 e_Ti
b[X_i]    =  2 e_Xi + 3 e_Ti    - 4 e_Q(fi)
b[T_i]    =  1      + 3 e_Ti    - 4 e_Q(si).
```

Coincident terms are added, rather than overwritten. In particular an increment
self-loop cancels its two action-coordinate terms. The actual trigger row is

```text
A[Z] = b[Z] + 5 * 1                 for Z != Q_H;
A[Q_H] = 0.
```

Every nonhalt entry lies in `1,...,9`, hence every nonhalt self-reset is
positive; `Q_H` is an allowed all-zero halt row. There are no other zero rows.

### 4.3 Why the uniform offset is valid, including the branch

If `y` is the normalized event vector, adding `b+5*1` followed by subtracting
the new minimum produces

```text
y + b - min(y+b)*1.
```

In the cases below `min(y+b)` is 0 or 1, so the actual post-trigger vector
is strictly positive. The same unique clock minimizes both vectors. The
uniform offset therefore preserves the next event, not necessarily the
elapsed time. We make no output claim about elapsed time.

For `+i`, adding its signed row to `V(c,+i)` gives exactly
`V(c+e_i,p_i)`: the target action is uniquely zero, data remain at least 2,
and all inactive action/recovery clocks are 4. This also covers `p_i=+i`.

For `-i`, adding its signed row gives `Q` clocks all 4, `T_i=1`, other
recovery clocks 4, and `X_i=2c_i-2` (all other data unchanged).

* If `c_i=1`, `X_i=0` is the unique minimum, with `T_i=1` second. Its
  trigger restores `X_i=2`, restores `T_i=4`, and puts `Q_(f_i)=0`.
  This is `V(c,f_i)`.
* If `c_i>1`, `T_i=1` is the unique minimum, since every data value is at
  least 2. Subtracting 1 to reach its event leaves `T_i=0`, all other
  control clocks 3, and data values one below their required even values.
  Its signed row first restores that common 1, adds a further 3 at `T_i`,
  and subtracts 4 at `Q_(s_i)`. The result is `V(c-e_i,s_i)`.

Thus an increment uses one Waterfall trigger and a decrement uses two.
All reachable minima are unique, every between-event vector is positive,
and `Q_H` is reached precisely for `H`. In particular, the generic language's
undefined simultaneous-zero behavior is never invoked. At halt the normalized
data clock `X_1` is `2(r_1+1)`.

## 5. Tie-free Waterfall to all-zero BP2

This stage applies to any finite positive-initial integer Waterfall program
with unique reachable minima, positive nonhalt diagonal entries, and one
all-zero halt row `h`. Let it have `N` clocks, initial values `w_i`, and rows
`A_ij`. Use BP2 cells

```text
v_i = label i;
z_i = label N+i;
m   = label 2N+1.
```

All `2N+1` labels occur. Each `v_i` stores a clock. At a program restart after
initialization, all `z_i` are 1 except possibly one zero identifying the event
whose trigger has not yet been applied. At the entrance to a steady sweep, all
`z_i` are 1. At these restart and sweep boundaries, `m` is 1 in ordinary
execution and 2 during the halt exit. Intermediate guard/cancellation
instructions may temporarily change those marker values; the final marker
pair leaves `m=0` on termination.

For a vector of nonnegative constants `b`, write `Add(b)` for all its literal
increments and `Sub(b)` for the matching literal decrements, in the same fixed
cell order. This notation expands to ordinary finite BP2 source. Empty
components emit no commands. Crucially **all increments precede the guard,
and all matching decrements follow it**.

### 5.1 Restart-safe initializer

Let `a` give `v_i=w_i` and `z_i=1`, excluding `m`. Emit

```text
Add(a); -m; +m; Sub(a).
```

On the first visit, `Add(a)` creates the intended values, and `-m` on zero
sets `m=1` and restarts before the cancellation. On every later visit with
any nonnegative working vector `x` and `m>=1`, it goes through

```text
(x,m) -> (x+a,m) -> (x+a,m-1) -> (x+a,m) -> (x,m).
```

No cancellation can underflow: each cell was increased by exactly the amount
subsequently subtracted, so its successive pre-decrement values are positive.
This is true even when some working `z` or `v` is zero, or `m=2` in the exit.
Thus the initializer runs once effectively and is thereafter an exact no-op.
A bare increment prefix would run again after every zero test and is invalid.
For a concrete halting counterexample, the initialized program `-1 -1` with
counter 1 initially 1 repeats the same state every two steps. Its tempting
all-zero compilation `+1 -1 -1` instead halts after six steps with value 0.

### 5.2 Guarded trigger blocks

For each nonhalt clock `i`, define a nonnegative increment vector on BP2 cells:

```text
b_i(v_j) = A_ij - [i=j],
b_i(z_j) = 0,
b_i(m)   = 0.
```

Nonnegativity of the diagonal adjustment uses `A_ii>=1`. For the halt clock
use instead

```text
b_h(v_j) = 2 - [h=j],
b_h(z_j) = 0,
b_h(m)   = 1.
```

In clock order emit the blocks

```text
Add(b_i); -z_i; +z_i; Sub(b_i).
```

If `z_i=1`, the block is a no-op and cannot restart. If `z_i=0`, its guard
sets `z_i=1` and restarts, preserving `Add(b_i)`. The other pending indicators
are unchanged. Cancellation in an inactive block is safe even if a clock value
is zero. In the halt block the marker increment is before the guard, and its
cancelling decrement is after the guard, exactly like the value increments.

### 5.3 A tick, zero tests, and the loop exit

After all trigger blocks, emit the steady decrement sweep

```text
-v_1; ...; -v_N;
```

then, for each clock in order, emit

```text
-z_i; -v_i; +v_i; +z_i;
```

and finally

```text
-m; -m.
```

There is no other code after that pair.

At the entrance to a steady sweep in ordinary execution, all `v_i` are
positive, all `z_i=1`, and `m=1`. The sweep therefore succeeds without a
restart and subtracts 1 from every clock. If no clock reaches zero, each test
cancels itself, and the final marker pair restarts, restoring `m=1`.

If clock `i` reaches zero, it is the only zero by the Waterfall invariant.
Tests before it cancel. Its `-z_i` sets `z_i=0`; its `-v_i` on zero sets
`v_i=1` and restarts. The untouched tests after it are irrelevant. At the
restart the initializer and preceding inactive trigger blocks cancel. The
active block for `i` then adds `b_i`, resets `z_i` to 1, and restarts again.
For a nonhalt row the resulting clock tuple is precisely

```text
(Waterfall tuple immediately at zero) + A_i.
```

The subtraction of one from `b_i(v_i)` compensates exactly for the zero test's
automatic setting of `v_i` to 1. All clocks are now positive: the triggered
clock was raised by its positive diagonal, and all others were positive
already. The subsequent pass resumes ordinary ticks. Each complete Waterfall
event and each finite integer interval to the next event takes finitely many
BP2 instructions. No scan or initializer can diverge internally.

### 5.4 Halting and the exact final tuple

Let `y` be the unique-zero Waterfall tuple at its halt event, so `y_h=0` and
all other entries are positive. The zero tester first replaces the zero by 1.
The active halt block then leaves all `v_j=y_j+2`, all `z_j=1`, and `m=2`,
and restarts. Initialization and every inactive trigger block remain no-ops.
One final sweep makes `v_j=y_j+1`, so all zero tests succeed. The final
marker decrements take `m=2` to 0 without a restart, and the program falls off.

At a program restart or steady-sweep boundary after initialization, `m` can
first be 2 only because an active halt block preserved its increment across
the guard-induced restart. Inactive halt blocks cancel their marker increment
before reaching either boundary. Until then every visit to the ending marker
pair restarts and no other location can fall off the program. Hence BP2 terminates exactly when the Waterfall halt event
occurs. Its final tuple has

```text
v_j = y_j+1, every z_j=1, m=0.
```

In the composed construction, `v_1=X_1+1=2(r_1+1)+1=2r_1+3`, which proves
the output assertion without clearing the source output or rerunning it.

### 5.5 Exact syntax-only compiler bounds

Let `I` and `J` count the source's increment and decrement instructions, and
let `s` be the sum of its input registers. The construction has

```text
k = d + I + 4J       amnesiac counters;
N = 4k+1            Waterfall clocks;
C = 8k+3            dense BP2 counter labels;
L = 168k^2 + 124k + 19 + 4s    literal BP2 commands.
```

The initial amnesiac counts sum to `s+k`, and the initial Waterfall values sum
to `2s+18k+1`. The initializer therefore contributes `4s+44k+6` commands.
The four nonhalt row sums per amnesiac counter are respectively `5N+2`,
`5N-1`, `5N+1`, and `6N-1`. Their guarded blocks contribute
`42kN+2k = 168k^2+44k` commands after diagonal compensation. The halt block
contributes `4N+2 = 16k+6`; the final sweep, tests, and marker pair contribute
`5N+2 = 20k+7`. Their sum gives `L`.

These bounds depend only on the finite machine syntax and input values.
Construction expands explicitly bounded lists and literal increment/decrement
blocks; it never evaluates the source. Every label occurs in the initializer
or final sweep/tests, and the resulting program is nonempty.

## 6. Composition with the fixed 38-phase CTS

The BP2 program just constructed satisfies every source premise of
[`ut19-simulation-invariants.md`](ut19-simulation-invariants.md): finite,
nonempty, dense positive labels, all counters initially zero. Its code and
input occur in the encoded initial queue. The 19 tag productions and their
38 ordinary CTS appendants do **not** vary with the machine or input.

Consequently that theorem, composed with the present front end, gives a first
designated CTS event exactly for source termination. Apply the current-state
structural reader in [`ut19-readout.md`](ut19-readout.md) and then the fixed
arithmetic map `(first_value-3)/2` to obtain the source result. This is a
genuine computable output convention; it is not merely preservation of a
yes/no halt fact. It does not require the source, expected answer, execution
history, or program-dependent counter index at readout time.

The mathematical encoders are total on finite descriptions. A concrete
implementation may refuse to materialize an enormous unary prefix or queue,
and a bounded evaluator may stop before a halt event. Such refusals do not
decide nontermination. The test helper implementing these formulas is not
presented as a production API or as a resource-unbounded physical simulator.

No Cook/UTM tag-system fallback is needed for this front-end theorem. That
would be another source route requiring its own finite-input and output
conventions; it would not repair a downstream S-controller proof obligation.

## 7. Why the chosen source suffices for arbitrary effective computation

One does not need a two-register universality theorem as an extra premise.
A direct finite-register simulation of a Turing machine suffices:

1. Fix a tape alphabet and encode its symbols, including blank, by digits
   `1,...,B-1`. Store each of two finite stacks in a register as a base-`B`
   number whose least significant digit is the top. Zero denotes an empty
   stack. Store the head symbol and Turing state in finite control.
2. Pushing digit `d` is `x := B*x+d`. Transfer `x` one unit at a time to a
   zero scratch register, adding `B` units for every successful decrement;
   transfer back and add the fixed `d`. Both loops expand into finitely many
   `INC`/`DEC` states.
3. Popping uses a finite-control residue `j` modulo `B`. Decrement `x` to
   zero; every `B` successful decrements increment a zero scratch register.
   At the end the control residue is the popped digit and scratch is the
   quotient. Transfer the quotient back into `x`. Empty pop returns blank.
   Valid stack encodings have nonzero residue when nonempty.
4. A head move pushes the old head symbol onto one stack and pops the other;
   a tape write changes the finite-control head symbol. A finite input word
   has a computable finite pair of stack encodings. All macro loops terminate
   on their finite register values, so simulation neither invents a halt nor
   loses an infinite source computation.

Unconditional control transfers, when needed by an expansion, can test a
dedicated permanently-zero scratch register and take its zero edge. The
construction uses finitely many registers, all describable by the source
syntax. Standard finite-output transducers may first gather their marked
output region using the same stack operations, accumulating an integer result
in register 1, and then halt; this is effective finite code, not an oracle.

For an explicit binary-word convention use the bijection
`code(w)=2^|w|+value_binary(w)-1`, including `code(empty)=0`. Appending a bit
`b` updates the accumulator by `n := 2n+1+b`, another fixed counter macro.
At termination decode by writing `n+1` in binary and dropping its leading 1.
Thus the fixed final BP2 readout can return words as well as natural numbers.
This establishes computational universality of the stated source without
depending on optional Waterfall or Amnesiac I/O extensions.

## 8. Finite verification and limits of the evidence

The independent standard-library test file directly implements the source,
amnesiac actions, Waterfall event arithmetic, and literal BP2 steps. It imports
no repository source compiler or evaluator and no external implementation.
It checks initialization with ordinary and exit markers; complete chain
restoration for shared-register call sites; all one-step Waterfall branch
cases in its declared finite domain including self-successors; literal BP2
halt output and a closed nonhalting cycle; and small end-to-end source cases.

The universal claims rest on the quantified invariants above. Finite tests
check transcription and selected boundary cases; they do not replace those
invariants, establish the downstream S simulation, or imply that a finite
timeout proves nontermination.

Validation on 6 October 2026: all eight test methods passed, including 4,500
Waterfall macro cases, 1,485 initializer cases, 54 source-chain cases, 34
immediate Waterfall halt cases, two nonhalt-trigger-then-halt cases, eight
end-to-end counter-machine cases, and exact literal cycle/prefix checks.
The focused suite was run with a hard 180-second wall limit and 512 MiB
virtual-memory limit:

```sh
ulimit -v 524288
timeout --signal=KILL 180s python -m unittest discover -s tests \
  -p 'test_universal_bp2_frontend.py' -v
```

No complete repository suite or S trajectory was run for this proof-only
change; no existing source files were changed.
