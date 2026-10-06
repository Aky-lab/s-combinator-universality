# Independent adversarial review of the uniform BP2 front end

## Verdict and scope

**Final scoped signoff: the stated standard-register-machine/input to all-zero
BP2 reduction is sound.** The three marker-boundary wording issues identified
in the initial review are resolved in the reviewed final document, and its
new section 5.5 correctly derives the exact syntax-only compiler bounds.
No counterexample to halting equivalence, finite compilation, tie-freedom, or
the fixed output map was found. The original instruction-level marker
counterexample is retained below to explain why those boundaries matter;
it is not a counterexample to the corrected theorem or construction.

This is an independent written algebraic audit, supported by new checks in
[`test_universal_bp2_frontend_review.py`](../tests/test_universal_bp2_frontend_review.py).
It is not machine verification, a proof of the downstream CTS/S controller,
or a claim that standard S evaluation is universal.

Reviewed and rechecked after corrections on 6 October 2026. The final reviewed
files have these SHA-256 values:

```text
docs/universal-bp2-front-end.md
9505ff4cfed814e77f80dffc133b28010da29af1cfc4b44840cf14dd04dbeb27
tests/test_universal_bp2_frontend.py
7389ae3f4888b3f553f2d83cade588061e0691a9065968f918437ef15a2dfdb0
```

## Resolved wording issue and retained counterexample

The original document, SHA-256
`c64f8adfa3e513410225f5a4a7192d64120fdafc96cfedc67eb7e5c06d376052`,
contained these three sentences in section 5 without sufficient observation
boundaries. The final document has corrected all three:

1. “`z_i=0` means its zero event has been noticed but its row not yet applied;
   otherwise `z_i=1`.” This is true at program restarts after initialization,
   not between every pair of BP2 instructions. Inactive trigger guards and
   ordinary positive-value zero tests temporarily make a `z_i` zero.
2. “The marker `m` is 0 only before initialization or at final termination,
   1 in ordinary execution, and 2 during the halt exit.” At individual
   instructions, the initializer guard and loop-exit pair temporarily make
   it zero; an inactive halt block temporarily raises it to 2, or to 3 during
   an actual halt exit.
3. “Conversely only an active halt block can raise `m` from 1 to 2.” An
   inactive halt block also executes `Add(b_h)`, which raises `m` temporarily.
   Only the active guard preserves that increment across a restart.

The corrected section-5 introductory description now states:

> At a program restart after initialization, all `z_i` are 1 except possibly
> one zero identifying the event whose trigger has not yet been applied.
> At the entrance to a steady sweep, all `z_i` are 1. At these restart and
> sweep boundaries, `m` is 1 in ordinary execution and 2 during the halt exit.
> Intermediate guard/cancellation instructions may temporarily change those
> marker values; the final marker pair leaves `m=0` on termination.

The corrected converse statement in section 5.4 now states:

> At a program restart or steady-sweep boundary after initialization, `m`
> can first be 2 only because an active halt block preserved its increment
> across the guard-induced restart. Inactive halt blocks cancel their marker
> increment before reaching either boundary.

The smallest generic example has one halt clock initially 1. Once initialized,
its inactive halt block begins with `+v; +m`, temporarily producing `m=2`, then
later cancels it back to 1. The smallest composed source example is the
one-register program `HALT` with input zero. The review test suite preserves
this counterexample to the original wording without mistaking it for a
reduction failure. The explicit final boundary qualifications exclude it.

## All-input algebraic audit

### Source control and complete amnesiac chains

Assume a well-formed finite source: natural initial registers, valid register
indices, an entry instruction, and valid jump targets. The instruction-entry
invariant is sufficient for induction: data are `r_i+1`, every auxiliary is 1,
and the action is `E(q)`.

For an increment instruction at zero-based position `j` in the increment
chain, the macro has exactly `j+3` actions. The unique marker is raised,
the data is incremented, and exactly `j` unsuccessful scan decrements precede
the successful decrement restoring that marker.

For a decrement instruction at zero-based position `j` in the decrement
chains, **either branch has exactly `2j+8` actions**. The common prefix marks
`S_q,F_q` and tests the data. On the positive branch the `S` scan restores
`S_q`, the failed `-V_q` raises `U_q`, and the `F` scan restores `F_q` before
the successful `-U_q` selects the positive target. On the zero branch the
roles are reversed: restore `F_q`, fail `-U_q`, raise `V_q`, restore `S_q`,
then successfully decrement `V_q` to select the zero target.

Thus auxiliary control never leaks across a source step. A scan cannot pass
its selected marker; the end-of-chain `H` edge is unreachable. Empty chains
cannot be entered. Shared data registers, arbitrary forward/backward jumps,
multiple halt labels, and instructions never reached in the source all fit
the same induction. In particular, a source with no reachable halt does not
reach an unused `H` fallback. No action loop can silently diverge inside one
source step.

### Signed Waterfall rows, including recovery

For arbitrary positive amnesiac counts, use the normalized vector `V(c,a)`.
All rows in the document are coordinate sums, including coincident targets.

- Increment: `V(c,+i)+b[Q_(+i)] = V(c+e_i,p_i)`. If `p_i=+i`, the two action
  terms cancel; this does not remove the positive actual self-reset.
- Decrement at `c_i=1`: the first signed row leaves `X_i=0`, `T_i=1`, every
  action clock 4, other recovery clocks 4, and all other data at least 2.
  `X_i` is uniquely first. Its row restores `X_i=2,T_i=4` and selects `f_i`.
- Decrement at `c_i>=2`: after the first signed row, `T_i=1` is uniquely
  least and all data are at least 2. After subtracting 1, the recovery row's
  all-ones term restores *every* other coordinate's lost unit. Its additional
  `3 e_Ti` and `-4 e_Q(si)` restore the recovery clock and select `s_i`.
  The final vector is exactly `V(c-e_i,s_i)`.

Every intermediate minimum is unique for all counts, not only small ones.
The signed-row normalization minima are respectively 0, 0, and 1 for the
first increment/zero-decrement/positive-decrement stage, and 0 for either
recovery stage. Adding 5 to every row entry changes actual elapsed intervals
to 5 or 6 without changing the resulting normalized event vector. Every
nonhalt row entry is between 1 and 9. The halt action is a separate clock
with an all-zero row, so it cannot accidentally be a data/recovery clock.

Initialization by `V+1` is strictly positive and has the desired unique first
minimum, including when the source starts at `HALT`. All later events are
covered by the induction, so no implicit tie-breaking semantics is needed.

### Literal BP2 behavior and the corrected boundary invariant

The cancellation fact used everywhere is valid for **arbitrary nonnegative**
working counters: after adding `b`, subtracting exactly `b` in the same cells
cannot attempt a zero decrement. Guards do not change any cancellation cell
except the stated marker; the initializer excludes its own marker from `a`.
An inactive halt block also has safe marker cancellation, since its prior
addition supplies the unit subsequently subtracted.

At an ordinary steady-sweep boundary, clocks are positive, all `z_i=1`, and
`m=1`. The sweep is therefore a sequence of successful decrements. If no
clock becomes zero, every tester cancels and the ending pair restarts with
`m=1`. If a unique clock becomes zero, precisely its tester leaves a pending
`z_i=0` and sets `v_i=1` while restarting. No later tester runs first. At the
next restart all earlier inactive blocks cancel, the unique active block
preserves its addition, and another restart clears the pending indicator.
The `-1` diagonal compensation is exactly necessary and sufficient.

Positive nonhalt diagonals make every clock positive again. Integer waiting
times and finite literal blocks give finite progress from one event to the
next; there is no hidden internal divergence. The documented BP2 operation
is essential here: a zero decrement **sets the counter to 1 and restarts**.
A saturating decrement or a restart that resets other counters would not
justify these arguments.

At the unique halt event with zero-normalized tuple `y`, the tester and halt
block together produce `y+2`, all indicators 1, and marker 2 at a restart.
The final sweep produces `y+1`, no zero tester restarts, and the final marker
pair reaches zero and falls off the program. The converse uses the corrected
boundary invariant above: no ordinary ending pair can fall through.

### Fixed output and source universality

The first data counter remains `D_1=r_1+1`; no initialization, scratch
allocation, source input sharing, or output cleanup changes its identity.
At the halt event `y_1=2(r_1+1)`, hence the first final BP2 cell is `2r_1+3`.
The reader needs only that first value. Its input arity can vary with the
source; its formula and chosen coordinate do not. It does not rerun the
source or need the source text, input, trace, or expected result. The generic
Waterfall-to-BP2 theorem alone does not guarantee this odd first coordinate;
the composed layout does.

The source is the ordinary finite-control, unbounded-register INC/DECJZ
model, not a bounded machine or an undecidable macro language. Section 7's
two-stack argument supplies a direct universality justification: multiplying
by fixed `B`, adding a fixed digit, and quotient/remainder by fixed `B` use
terminating transfer loops and finite control. The scratch counter is zero
again after each transfer-back. A zero test on a dedicated zero register
supplies unconditional jumps. Nonzero alphabet digits distinguish empty
stacks from stored blanks. Finite-output word coding is computable by the
same arithmetic macros, with a fixed decoding convention.

## Exact syntax-only compiler size

Let `d` be the source register count, `I` its number of INC instructions,
`J` its number of DECJZ instructions, and `s` the sum of its finite input.
For the documented literal compiler, put

```text
k = d + I + 4J
N = 4k+1
C = 2N+1 = 8k+3.
```

The initial amnesiac counts sum to `s+k`, and the initial Waterfall values
sum to `2s+18k+1`. Consequently the initializer has `4s+44k+6` commands.
For each of the `k` counters the four nonhalt row sums are

```text
Q_(+i): 5N+2; Q_(-i): 5N-1; X_i: 5N+1; T_i: 6N-1.
```

Their total is `k(21N+1)`. Subtracting one diagonal compensation per nonhalt
row and adding each block's two guard commands yields `42kN+2k`, or
`168k^2+44k`, nonhalt-block commands. The halt block has `4N+2=16k+6`
commands. The sweep, tests, and final pair have `5N+2=20k+7` commands.
Therefore the **exact** source length is

```text
L = 168k^2 + 124k + 19 + 4s.
```

All dense positive labels occur: every `v_i` and `z_i` occurs in the tail,
and the marker occurs in its final pair. The program is nonempty. None of
these allocation or length formulas uses source execution, a halting test,
a result bound, or a simulation-derived constant. Very large unary output
may be impractical to materialize, but is mathematically finite and effective.

## New verification and limitations

The review suite imports the three candidate compiler helpers as systems
under test. Its BP2 interpreter, amnesiac action step, symbolic normalization,
and expected boundary transitions are independently written. It does not
call the candidate interpreters or rerun the author's eight test methods.

Five review tests passed:

- 10,368 source macro cases over all two-callsite/two-register programs with
  a common halt target, checking exact macro lengths and full restoration;
- 12,666 affine-symbolic Waterfall cases, covering all active counter and
  successor choices for `k=1,...,4` with independent **unbounded natural**
  data parameters and explicit positivity/unique-zero coefficient checks;
- 144 two-clock BP2 programs with every small nonhalt row, including zero
  off-diagonal entries and diagonal 1, checked at stable sweep boundaries;
- 44 direct compiler-size/label checks, including syntactically infinite
  sources and arbitrary starts, while all candidate step functions are
  patched to raise if called;
- the concrete intermediate-marker counterexample showing why the now-explicit
  boundary qualifications are necessary.

The generic two-clock traces stop at a halt, an exact literal-state cycle,
an upcoming tie outside the theorem's premise, or 30 checked sweep boundaries.
The last stopping condition is finite evidence only, never a nonhalting claim.
Symbolic tests range over unbounded counter magnitudes but finitely many
control layouts; the arbitrary-layout theorem rests on the algebra above.

Validation command and final recheck result after the boundary corrections and
addition of section 5.5:

```sh
ulimit -v 524288
timeout --signal=KILL 180s python -m unittest discover -s tests \
  -p 'test_universal_bp2_frontend_review.py' -v
# Ran 5 tests in 0.529s; OK.
```

Only Python's standard library and repository compiler helpers were executed.
No external code, Lean, installation, S trajectory, or full repository suite
was run. Only this review document and its review tests were authored or edited
by the reviewer; the front-end document corrections were independently checked.

## Primary-source cross-check

The canonical author pages were read on 6 October 2026. Their displayed
permanent links match the revisions cited by the front-end document; direct
revision-URL requests failed through the web tool, so the successful reads
used the canonical pages.

- [Brainpocalypse II](https://esolangs.org/wiki/Brainpocalypse_II): numerical
  zero-decrement/restart semantics, all-zero starting cells, and guarded
  initializer/Waterfall simulation agree with the theorem's interface.
- [The Waterfall Model](https://esolangs.org/wiki/The_Waterfall_Model): trigger
  rows are nonnegative, simultaneous zeroes are undefined by default, and a
  halt clock has an all-zero row. The document properly distinguishes the
  first zero-row event from an implementation's optional halt detection.
- [The Amnesiac From Minsk](https://esolangs.org/wiki/The_Amnesiac_From_Minsk):
  positive counters and tail triggers match the normalized model. The
  literal self-trigger/start conventions are separate, and the constructed
  reachable chain actions do not accidentally invoke those literal halt rules.
