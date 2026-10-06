# Composing a CTS halt event with S readout

A distinguished source-halting event can be carried through an exact cyclic-tag-to-S simulation even when the cyclic-tag word remains nonempty. The following elementary composition isolates the required interfaces.

## Hypotheses

Fix a cyclic-tag program `P`, initial configuration `c0`, and totalized trajectory `c_k = δ_P^k(c0)`. Suppose a closed-S encoder, fixed selector and bounded structural reader produce a native trajectory `T_0, T_1, ...` satisfying:

1. For every `k`, some sample `n` has `D(T_n) = (k, c_k)`.
2. Whenever `D(T_n) = (k, c)`, the configuration is exactly `c_k`.
3. `D` is a total parser of the current bare S tree, with a fixed all-input operation bound.

Let `H` be a fixed, bounded predicate of a current CTS configuration. Define the S-tree detector:

```text
A_H(T) = true  exactly when D(T) returns (k, c) with H(c) = true.
```

## Event-preservation lemma

```text
there exists k with H(c_k)
    if and only if
there exists n with A_H(T_n).
```

Proof. For the forward direction, take a witnessing `k` and use hypothesis 1 to obtain an accepted S sample with configuration `c_k`. For the reverse direction, an accepted S sample supplies a decoded pair; hypothesis 2 identifies its configuration with the actual CTS iterate. In either direction the same fixed predicate is tested. No source execution occurs inside `A_H`.

If `D` uses at most `b(N)` operations on an N-node tree, its decoded fields have size at most `r(N)`, and `H` uses at most `h(m)` operations on an m-sized configuration, the composite uses at most `b(N) + h(r(N))` plus fixed dispatch overhead. All these bounds must account for actual parsing and output construction.

## Designated-production instance

For a fixed appendant index `h`, ordinary CTS semantics selects that production precisely when:

```text
current phase = h and the current word begins with 1.
```

After reading the phase and first bit, the predicate is constant-size. An event logged after CTS step `k+1` corresponds to testing `H(c_k)` before that step. If a source compiler proves that this event occurs exactly when its source machine halts, the lemma transfers that equivalence to the selected S trajectory.

The [compact fixture](neary-fixture.md) uses `h = 170`. Its source-result boundary and later production-selection event are recorded separately. The [direct encoding research](compact-encoding.md) explains how fixing one universal binary source machine would keep the CTS program and S controller fixed across varying inputs.

## Proof dependencies for a complete construction

The generic S interface is the relevant part of the candidate's [exact CTS realization](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFiniteAllInputsTraceAgreement.lean). Its bounded reader is described in the [definition inventory](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/TRUSTED_DEFINITIONS.md).

For the compact source front end, the remaining proof obligations are the exact distinguished-event equivalence on all valid encodings and structural source-configuration readback at macro boundaries. Composing bounded readers gives a bounded observer. A finite-tree-automaton characterization of this new event would require an additional language argument.
