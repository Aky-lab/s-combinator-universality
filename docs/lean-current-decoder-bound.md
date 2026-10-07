# The actual Lean current-tree decoder is polynomial

7 October 2026. This note closes the **mathematical polynomial-time auxiliary
readout obligation in occurrence-tree size** for the decoder used by
`SOnlyCurrentDecoder.read`. It does not claim a machine-instruction cost theorem
for the Lean compiler, or polynomial time in the number of nodes of a compressed
DAG. Those are different claims.

## Statement and representation

Fix `SOnly38.program`, `SOnly38.dispatcher.tree`, and the event pattern. Let
`m = term.size`, where `PureSFormal.PureS.Term.size` counts every leaf and
application occurrence of the supplied finite, unshared binary tree. Then
the specified current-tree algorithm computes `SOnlyCurrentDecoder.read term`
in `O((m+1)^3)` constructor/list operations with fixed code constants. Its
numeric registers and addresses have `O(log(m+2))` bits, apart from fixed code
constants. Consequently it has a polynomial bit-time and polynomial space
implementation on ordinary machines. No input-dependent source simulation
is used anywhere in this argument.

This is an all-input statement. It includes arbitrary malformed carriers,
fabricated event shells, nonaccepting trees, and the case where the first
matching shell has an invalid result payload. It is not restricted to reachable
trees or correct halting examples. On raw serialized syntax, an initial linear
validation pass establishes the finite `Term` representation, including the
otherwise opaque audit fields.

The bound is for evaluating the mathematical algorithm in the usual
constructor/list cost model, with standard structural equality. It is not a
bound on kernel normalization of a proof term or a claim about every possible
implementation of the same extensional function.

## Why structural termination alone would not suffice

A decreasing size measure permits branching recursion and can therefore coexist
with exponential time. Here the source gives the stronger facts required:

1. Every `decodeCarrier?` invocation makes **at most one** recursive invocation.
2. The chosen accumulator/predecessor is a strict occurrence descendant.
3. A successful Base terminates carrier recursion and invokes one cell-spine
   decoder on a strict descendant queue.
4. Cell-spine decoding also follows exactly one strict-descendant path.
5. Every appended output bit comes from a live cell on this path.

Thus there are at most `m` charged carrier/cell iterations and at most `m`
decoded carrier bits. Repeating a parser at each of these iterations does not
silently turn a tree walk into a source execution.

## Audit of one classifier iteration

The source inspected is the already pinned upstream
`PureSFormal/PureS/CheckpointDecoder.lean` and its imports, not the older
source-parameterized public decoder or the Python port.

Use a fixed constant `A` large enough for the finite dispatcher, all its compiled
dormant code, all action appendants, all fixed tags, and the finite code
construction performed by these functions. Such a constant exists because all
these objects and constructions are fixed, independently of `term`.
At every iteration all dynamic terms are subterms of the original input.

- `parseBase?` inspects a constant-size wrapper, compares its two continuation
  subtrees structurally, compares primitive `b`, and checks two environment
  wrappers against fixed compiled action code. The only equality between two
  arbitrary current-input terms is the continuation equality. Ordinary
  recursive tree equality visits at most the sum of their occurrence sizes,
  hence `O(m)`. Code comparisons/construction are bounded by `A(m+1)` even if
  no constant is precomputed.
- `parseLocal?` checks its finite shell and fresh/marked halt tag. Its
  `DispatchParser.parse` calls `RouteParser.parse`, `responseAt?`, and
  `ActionParser.parse`.
- `RouteParser.parse` chooses **one branch** of the fixed dispatcher at each
  node. `classifyChildren` makes at most four `exactHeadArity` tests; each
  follows a left spine of at most `m` nodes. Each dormant sibling comparison
  is against fixed code. A route has at most the fixed dispatcher's depth, so
  this costs at most `A(m+1)`. There is no search over source histories.
- `responseAt?` follows that one fixed-depth route, with constant-size
  decompositions at its nodes.
- `ActionParser.parse` invokes `result.spineArgs`, then checks the fixed
  prefix and the number of independent histories. **This is not uniformly
  linear as written.** `Term.spineArgs (.app f x) = f.spineArgs ++ [x]` copies
  the growing list. A left spine of length `h` entails a triangular number of
  list-cell visits, bounded by `(h+1)^2 ≤ m^2`. Computing the history-list
  length adds at most `m` visits. A malformed action may have an arbitrarily
  long left spine; the fixed expected history count does not remove this case.
- `CanonicalStep.parseCell?` has a fixed constructor skeleton and comparisons
  with two fixed value tags. It neither follows nor compares an audit.
- Every successful live decoder branch appends one bit to an already decoded
  list of length at most `m`. Its list cost is at most `m+1`.

Therefore **one complete iteration, including its return-side list append,**
costs at most `A(m+1)^2`. A cell-spine iteration is cheaper but can be charged
the same allowance. Combined with at most `m` iterations, carrier decoding is
bounded by `A m(m+1)^2` constructor/list operations. This intentionally loose
cubic bound avoids relying on successful-parse special cases or memoization.

## The rest of the fixed current-tree reader

`findShell` performs a preorder walk, testing the root, then the left subtree,
then the right subtree. It visits each input occurrence at most once. Each
`targetPattern.matchesBool` invocation has at most the fixed pattern's number
of recursive tests. Thus witness selection is `O(m)` with a fixed constant.
No witness is retried after a malformed numerical payload is found.

The selected `LLLR` lookup takes at most four edges. Its snapshot has size at
most `m`. Carrier decoding returns at most `m` bits, and restoring the known
deleted `true` adds one bit.

`decodeEventWord` checks the first two bits. `decodeBlocks` has fuel equal to
the remaining input-list length, and each nonempty iteration takes/drops a
fixed block of 19 bits. Its block length, count, and index tests have fixed
size. It emits at most one symbol per iteration. The emitted symbols lie in
the fixed range 1 through 19. The leading event symbol is the fixed value 18.

`firstRun` and `leadingRun` inspect one prefix and the immediately following
run. Their count is bounded by the supplied symbol-list length, hence by
`m+1`. `decodeLength` uses subtraction, a bitwise-and, integer logarithm, and
division/remainder by 2 on this count. `decodeMachineValue` performs the fixed
positive-odd test and arithmetic `(counter-3)/2`. None of these operations
constructs `4^n`; powers occur only in correctness theorem statements. Even
schoolbook arithmetic on these `O(log(m+2))`-bit integers is polynomial.

The cubic constructor/list bound dominates all these stages. For example,
assigning the deliberately excessive `O((m+1)^2)` bit cost to each elementary
operation still gives an explicit `O((m+1)^5)` bit-operation upper bound in
a random-access bit-cost model. A conventional Turing-machine simulation may
increase the exponent and remains polynomial. The result does not need any
bound involving a source running time or halting decision.

## What is kernel checked

[`formal/SOnlyDecoderBound.lean`](../formal/SOnlyDecoderBound.lean) proves:

- `parseBase_queue_size_lt`: an extracted Base queue is a strict descendant
  in size.
- `cellSpine_output_length` and `carrier_output_length`: a successful decoded
  bit list has length at most the supplied term's occurrence size.
- `carrierFuel_eq`: a structurally fuelled copy of the **same ordered
  classifier**, with fuel at least the input's size, equals upstream
  `decodeCarrier?` on every input. This includes unsuccessful parses.
- `carrierCharge_le`: the carrier recursion charge, including an allowance
  for every cell-spine frame at its single Base, is at most input size.
- `carrier_cubic_charge`: multiplying the charge by the quadratic iteration
  allowance gives the stated cubic bound.
- `spineVisits_quadratic`: the list visits of the actual append-based
  `Term.spineArgs` are bounded by the square of term size.

[`formal/SOnlyDecoderBoundCurrent.lean`](../formal/SOnlyDecoderBoundCurrent.lean)
then proves `readFuel_eq`, an all-input identity with the selected
`SOnlyCurrentDecoder.read`, and `selected_audit_size_le`. It retains exactly
the original first-preorder choice and numerical decoder. The carrier fuel is
bounded by the whole current input tree, without any source index.

The printed axioms of the exported results are only `propext` and `Quot.sound`.
There are no new axioms, `sorry`, or `native_decide`. The final isolated checks
are recorded under `artifacts/formal-decoder-bounds-2026-10-07/`.

The source-level local-parser estimates and the standard elementary-operation
to bit-cost simulation are the written proof above. They are **not** a
kernel-checked instrumented semantics for every imported parser or for Lean's
runtime/compiler. The cubic-charge theorem must not be advertised as that
stronger theorem. A fully mechanized cost model could be added without changing
the chosen decoder or universality semantics.

## Sharing and the Python reader

The theorem's input is an ordinary finite occurrence tree, exactly as upstream
`Term` is specified. If an implementation stores repeated subtrees in a DAG,
unfolded size can be exponential in distinct-node count. The proof here must
not substitute the latter count for `m`.

The memoized Python reader has a separate stronger bound in distinct validated
DAG nodes, with budget `4096(N+1)^3(c+1)^2`. Its runtime memoization and syntax
validation are useful implementation properties. A formal correspondence
between that port and Lean is not needed for the occurrence-tree polynomial
readout established here. It would be needed to transfer the Lean semantic
theorems to that specific implementation, or to claim its distinct-node
complexity bound for the Lean definition.
