# Short technical claim

A fixed finite root-reset selector for the single rewrite
`S x y z → x z (y z)` can simulate every conventional finite-state,
finite-alphabet Turing machine on every finite input. It also computes the exact numerical output of every
finite natural-register machine.
Only the resulting closed S term persists between invocations. Halting is
recognized by one fixed regular tree language. A fixed polynomial current-tree
decoder returns the exact register result at the first accepted sample; the
TM-specific theorem identifies the stated finite left-stack code.

The conventional integer-tape simulation, literal three-register compiler,
and exact source-to-S first-event equivalences are formalized in Lean 4.33.1
and passed fresh official-kernel replay. The 67 project modules were audited
through 1,359 explicit declaration queries. The complexity argument gives a
singly exponential syntax encoder, a fixed finite event automaton, a linear-per-invocation controller
bound and polynomial occurrence-tree readout.

## Relationship to the pinned generic construction

Cinematic Strawberry's pinned construction supplies the generic CTS-to-S
encoding, scheduler, finite selector and trajectory facts. Those are imported,
attributed and independently replayed. The upstream package also already
states conventional Boolean-tape halting and output theorems for its fixed
912-phase construction.

The added formal development supplies the concrete fixed 38-phase source,
an explicit machine/input compiler, arbitrary-program UT19 halting and output,
generated descendant-event provenance, exact global first acceptance,
all-witness frozen-audit agreement and the fixed current-tree result
composition, and the conventional tape-machine compiler. The halting endpoint
is `SOnlyTuringUniversality.halting_iff_event`; the general numerical endpoint
is `SOnlyUniversality.result_iff_first_event`.

This claim concerns the stated finite-controller reduction model. It does not
assert priority, prize acceptance, or a result for every S-reduction strategy.
