# Finite fuel endpoint probes

The seven fuel-prefix rows have been compiled into a fixed read-only table specialized to the two-phase queue dispatcher. Run:

```sh
python -m tools.fuel_probe_report
```

The generated [report](../results/fuel_probe.json) records 4,727 finite control states, six local observations per state, and a static bound of 4,020 microticks per invocation. The runtime receives a table, finite control and a tree cursor. Pattern recursion and literal wrapper construction finish before the input tree is supplied.

## Structural rows

Write `b = S S`, `C0 = S b b`, and `E = S ((S Act) (S _))`, where `Act` is the fixed action wrapper and each `_` is an independent wildcard. Repeated appearances of `E` test the same fixed wrapper with independently varying payloads.

| Row | Pattern | Selected relative address |
|---|---|---|
| call-zero | `C0 E _` | L |
| call-positive | `b _ E _` | L |
| positive-half | `S E (_ E) _` | root |
| zero-first | `b E (b E) _` | L |
| zero-second | `S (b E) (E (b E)) _` | root |
| zero-third | `b E _ (E (b E) _)` | L |
| zero-fourth | `S _ (E _) _` | root |

Rows are tested in this order. Failed rows restore the invocation cursor before the next test. Success follows the fixed address and ends there. The [restoring pattern compiler](probe-compiler.md) supplies the finite tables and their correctness argument.

## Redex guarantee

Every instance of a root-selecting row has S head arity three. Every instance of a left-selecting row has head arity four, whose left child has head arity three. Therefore every successful row selects an exact native redex `S x y z`.

This argument holds for arbitrary replacements of every wildcard. It does not require equality between copied runtime payloads. If two rows match the same term, their head arities agree, so both select the same address: the available addresses are only root and L. The tests check this symbolic head-arity property directly, as well as varied concrete instances.

## Fixture coverage

On the certified 85-step queue path, these rows recover the specified local contraction at 25 supplied occurrences:

- Contractions 5–11
- Contractions 27–35
- Contractions 57–65

The exact origins, chosen addresses and measured microticks are in the report. Each local probe is started at the candidate fuel occurrence supplied by the test harness. The [root-reset selector](root-selector.md) supplies active-occurrence discovery and the earlier response/dispatcher priorities for the full two-phase fixture.

## Sources

The pattern family and row order follow Cinematic Strawberry's pinned [`RootResetPendingAdmissionFuelPatterns`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetPendingAdmissionFuelPatterns.lean); the selected addresses follow [`RootResetFuelFiniteRows`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFuelFiniteRows.lean). The [MIT notice](../third_party/cinematic-strawberry-MIT.txt) is retained for the derived pattern specification. The compiler, runtime and tests are independently implemented here.
