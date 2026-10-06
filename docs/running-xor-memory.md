# Running-XOR program-memory kernel

This proves the local memory obligation used by the
[compact UT19 source encoder](compact-universal-programs.md#source-level-encoder-formulas).
The component productions and construction are from ais523's
[UT19 article, Program memory](https://esolangs.org/wiki/UT19#Program_memory),
with the adjoining Inverters and Global cycle sections; the page is dedicated
to the public domain under CC0. Source checked 6 October 2026. The proof below
makes the observation time, disturbance delay, and required exterior alignment
explicit. It does not prove the counter simulation or the whole compiler.

## 1. State and observation convention

A block has `W >= 1` cells, indexed `0,...,W-1` from left to right. Cell `i`
has a dynamic bit `h_i`, and a fixed bit `a_i` indicating an inverter placed
immediately **after** the cell. Its Command representation is:

```text
h_i = 0: [5,6]
h_i = 1: [6,5,19]
a_i = 1: append [1,1,19] after this cell
```

Let `c_i = h_i XOR a_i`. This is the parity of the combined cell-plus-inverter
width. All vector and matrix arithmetic below is over `GF(2)`.

One memory step consists of three complete passes, Command, Parity, then
Reset. Time `t` means the entry to Command pass `t`; it does not count tag
microsteps or the three passes separately. Write `c_t` for the vector then.
The output used by the surrounding components is the block's current width
parity:

```text
v_t = XOR_i c_(t,i),           observed BEFORE the memory update.
```

An incoming alignment bit `g_t=0` means the block's first Command symbol is
produced from; `g_t=1` means it is skipped. It includes both the global Command
alignment and the width parity of every component before this block. It need
not be predictable or independent of earlier memory outputs.

Let `p_t,r_t` denote the incoming alignments for this same block on Parity and
Reset. They are supplied by the surrounding queue, rather than independently
chosen inside a full UT19 execution. The local statements require:

- Normal continuation: `p_t=0, r_t=0`.
- Reset: `r_t=1`, with either value of `p_t`.
- `p_t=1, r_t=0` is a halt-signal case, not a normal memory step.

The entire containing queue must have the stated three-pass decomposition and
must reach the relevant components without halting or exhausting first. The
counter and global-cycle invariants that supply these facts are separate
obligations. In particular, an isolated block run as a complete tag queue need
not supply the required alignments by itself.

## 2. Direct check of the UT19 productions

At a component's Command entrance with alignment `q`, the cell's intermediate
state is `d=h XOR q`. Indeed, choosing the even or odd positions of its literal
word gives `[7,9]` for `d=0` and `[8,9]` for `d=1`; any selected 19 contributes
nothing. The inverter produces `[2,3]` for either Command alignment.

The next two passes follow directly from these rules:

```text
1 -> [2,3]       2 -> [4,4]       3 -> [18,4]
4 -> [1,1,19]    5 -> [7,9]       6 -> [8,9]
7 -> [10,10]    8 -> [11,10]     9 -> [18,10]
10 -> [5,6]    11 -> [6,5,19]   18 -> [18]    19 -> []
```

Every cell and every inverter has width two during Parity and Reset, so `p`
and `r` remain constant across the block. Their effects are:

| Parity alignment `p` | Reset alignment `r` | Cell after Reset | Inverter after Reset |
| --- | --- | --- | --- |
| 0 | 0 | state `d` | unchanged |
| 0 | 1 | state 0 | unchanged |
| 1 | 1 | state 0 | unchanged |
| 1 | 0 | selects 18 | selects 18 |

For example, at `p=1` a cell produces `[18,10]`, and an inverter produces
`[18,4]`. An odd Reset skips 18 and selects 10 or 4, so there is no halt event.
An even Reset selects 18 instead. Merely containing 18 in an intermediate word
is therefore not a halt event.

At Command entry, cell `i` has alignment

```text
q_i = g XOR XOR_(j<i) c_j.
```

In a normal three-pass step the fixed inverter survives and

```text
h'_i = h_i XOR q_i
c'_i = h'_i XOR a_i = g XOR XOR_(j<=i) c_j.
```

Thus, with `P_(i,j)=[j<=i]` and `1` the all-ones column vector,

```text
c_(t+1) = P c_t XOR g_t 1.                       (1)
```

On reset, every `h_i` becomes zero and each inverter survives, giving `c'=a`
regardless of the previous state, `g`, or `p`. This also explains why the
encoder can store the initial vector using only state-zero cells and fixed
inverters: `A=[5,6]`, `B=[5,6,1,1,19]`.

## 3. The output transform when W is a power of two

Assume `W=2^m`, including `m=0`. First take `g_t=0` and `c_0=a`.
Let `L` be the lower shift matrix, `L_(i,j)=[i=j+1]`. Since `L^W=0`,

```text
P = I + L + ... + L^(W-1) = (I+L)^(-1).
```

For `n>=1`, the coefficient of `L^d` in `P^n` is
`binom(n+d-1,d)` modulo two. Summing column `i` to obtain the output coefficient
and using the finite binomial-sum identity gives

```text
(1^T P^n)_i = binom(n+W-1-i, W-1-i) mod 2.        (2)
```

The same formula holds for `n=0`: both sides are one. To evaluate its parity,
the factorization `(1+x)^N = product_(b: bit_b(N)=1) (1+x^(2^b))` over
`GF(2)` shows that `binom(N,K)` is odd exactly when every set bit of `K` is
also a set bit of `N`. Equivalently, `binom(n+r,r)` is odd exactly when
`n & r = 0`, meaning the addition of `n` and `r` has no binary carries.

Here `r=W-1-i` is the `m`-bit complement of `i`. For `0<=n<W`, equation (2)
is therefore one exactly when all set bits of `n` occur in `i`. Consequently

```text
v_n = XOR_(i: (i & n)=n) a_i,       0<=n<W.        (3)
```

Define `Z_(n,i)=[(i & n)=n]`. This is the Boolean-lattice superset transform.
It is its own inverse over `GF(2)`: entry `(n,j)` of `Z^2` counts the indices
`i` whose set bits lie between those of `n` and `j`. This is zero if `n` is not
a bitwise subset of `j`; otherwise it is
`2^(popcount(j)-popcount(n))`, which is odd exactly when `j=n`.

Every desired vector `v` of length `W` therefore has the unique initializer

```text
a_i = XOR_(j: (j & i)=i) v_j.                     (4)
```

The usual butterfly algorithm implements (4): for each index bit, XOR the
upper half into the matching lower half and leave the upper half unchanged.
It uses `W log2(W)/2` bit XORs and `W` stored bits. These are initializer costs,
not a bound on tag execution.

There is also exact unforced periodicity. In characteristic two,
`(I+L)^W=I+L^W=I`, so `P^W=I`. Equation (3) consequently holds at all times
with `n` replaced by `n mod W`.

## 4. Exact disturbance delay, including the boundary

An input bit `g_k=1` in update (1) adds the all-ones vector to `c_(k+1)`.
Its contribution to the output at `t=k+1+r`, for `r>=0`, is

```text
D_r = 1^T P^r 1.
```

For `0<=r<W`, equation (3) says that `D_r` is the parity of the number of
supersets of `r`, namely `2^(m-popcount(r))`. Thus it is zero except at
`r=W-1`, where it is one. Periodicity extends this to every `r>=0`:

```text
D_r = [r = W-1 mod W].
```

A single disturbance in **update k** first affects **output k+W**, then outputs
`k+2W, k+3W,...`. Superposition gives the exact forced output formula

```text
v_t = (Z a)_(t mod W)
      XOR XOR_(ell>=1: t-ell*W>=0) g_(t-ell*W).   (5)
```

In particular, outputs `v_0,...,v_(W-1)` equal the desired vector for every
forcing history. This remains true if the actual `g_t` are chosen adaptively
by the surrounding computation: (5) is an identity for each realized bit
sequence. The guarantee is sharp. With `a=0`, `g_0=1`, and all later `g=0`,
the first changed output is `v_W=1`.

A different timing convention gives a different index: flipping `c_0` directly
*before* output `v_0` changes the first output at `v_(W-1)`, not at `v_W`.
For `W=1` a direct state flip is visible immediately, while update `g_0` first
affects `v_1`. This distinguishes state perturbation from the incoming Command
alignment in (1). The same direct-state statement applies to a flip of the
last `d=2^b` cells in any block of width at least `d`: the unaffected prefix
cannot acquire a change from the suffix, and the suffix evolves by `P_d`.
This comparison uses the same forcing sequence on both trajectories. The first
changed output is at `d-1`, then every `d` steps.

## 5. What reset and finite program length establish

A legal odd Reset restores `c=a` exactly. Relabel the following Command
entrance as time zero; equation (5) starts afresh, without contributions from
any earlier forcing history. Consequently each epoch between resets has the
prescribed first `W` width parities, assuming the earlier steps of that epoch
meet the normal-continuation alignments.

An encoder may use this result when it separately proves that each epoch
requires at most `W` Command-entry observations before resetting or halting.
There is no extra protected observation at index `W`. The compact encoder
uses `W=2N` for its `N` expanded command pairs; the command/counter invariant
must establish that this horizon is sufficient, including initialization,
restart, and halt handling. This lemma alone does not establish that invariant,
a uniform result decoder, full halt-event correspondence, empty-queue cleanup,
or S-combinator universality.

The power-of-two hypothesis cannot be dropped. For `W=3`, a single update
`g_0=1` from the zero vector already changes `v_1` because three ones have
odd parity. For `W=6`, it changes `v_2`: the all-ones vector has even parity,
but its next prefix transform is `101010`, of odd parity. Both are earlier
than the claimed width-sized delay. The supermask output formula also fails
in general: at width 3, initial vector `100` gives outputs `110` under the
unforced prefix dynamics, whereas the supermask formula would give `100`.

## 6. Independent bounded checks

[`tests/test_running_xor_memory.py`](../tests/test_running_xor_memory.py)
uses only the Python standard library and its own literal component rules.
It imports no production encoder, compiler, tag engine, or external program.
The checks cover:

- All dynamic bits, inverter bits, and both Command alignments at widths 1–4,
  for normal continuation, both legal reset alignments, and the excluded halt
  alignment; both intermediate word lengths and selected-18 events are checked.
- Every desired vector at widths 1, 2, 4, and 8; the supermask and butterfly
  initializers, unforced dynamics, and transform involution agree.
- Independent dense-matrix powers versus the binomial output coefficients,
  plus power-of-two matrix periodicity.
- Every initial vector and every `2W`-bit forcing history at widths 1, 2, and
  4, checked through the final boundary against (5).
- Every initial vector and every `W`-bit forcing history at width 8, checking
  the protected window and the first unprotected output.
- Exhaustive raw-production forced histories at widths 1, 2, and 4, plus
  delayed-boundary, direct-flip, suffix-flip, and non-power-of-two regressions.

Run only this bounded suite from the repository root:

```sh
(timeout 180s sh -c 'ulimit -v 524288; python -B -m unittest discover -s tests -p test_running_xor_memory.py -v')
```

Verified 6 October 2026: all 14 tests passed under the stated limits. These
finite checks independently exercise the formulas and timing; the algebra
above supplies the statements for all power-of-two widths.
