# Program-parameterized structural checkpoint reader

`s_only.cts_reader` compiles a reader for any finite binary CTS program of
positive period. Its run-time input is one current bare S term. It returns
`{"horizon": h, "phase": h % period, "data": word}` or `None`.

The implementation independently transcribes the pinned public checkpoint
grammar. It does not receive an initial word, expected trajectory, source
configuration, contraction count, cursor, or previous sample. It does not
call a CTS evaluator or native reducer, read a file, hash a term, or look up
a recorded sample.

```python
from s_only.cts import Program
from s_only.encoding import encode
from s_only.cts_reader import compile_reader, decode

program = Program(("0", "10", ""))
reader = compile_reader(program)
term = encode(program, "101")
assert reader.decode(term) == {"horizon": 0, "phase": 0, "data": "101"}

# Convenience call compiles the static grammar each time.
assert decode(program, term) == reader.decode(term)
```

Use the reusable reader when inspecting many native samples. Compilation
uses the [generic encoder](cts-encoding.md) for fixed code and reconstructs
its adjacent-pairing dispatcher metadata. Leaves are phase-major,
zero-before-one, with no padding. For three phases, route depths are
`3,3,3,3,2,2`; for five phases, eight leaves have depth four and two have
depth two. Repeated action code does not identify labels: the selected
structural route determines the phase/bit label.

## Acceptance grammar

The time-zero case requires exactly `(C0 C0) E`, with the program's fixed
environment/action wrapper. The literal seed word must be composed of live
binary cells ending at `S`. Tombstones are disallowed in this initial word.

Positive acceptance requires all of the following:

1. A **nonempty** chain of completed Local shells, followed through each
   shell's literal `RL` continuation field.
2. A terminal `(Ck Ck) E` with matching carrier indices `k >= 2`. The
   horizon is `h = k - 1`. The terminal environment is checked, while its
   dormant payload remains opaque.
3. The innermost Local's route selects phase `(h - 1) % period`.
4. Its accumulator decodes as a public carrier.
5. Its halt field is fresh exactly when the resulting word is nonempty,
   or marked exactly when the word is empty.

Every Local must have a completed route and selected action. Activated
nodes are `S audit response`; selected children have head arity two and
dormant compiled calls have head arity three. The unselected branch's fixed
code is checked exactly. The action is `PI accumulator` followed by exactly
zero history arguments for a zero-bit label, or exactly the selected
appendant's length for a one-bit label. Histories remain independent.

The public carrier parser follows this priority:

- A Base exposes its literal active queue, which must be a complete cell
  spine ending at `S`.
- A completed Local exposes its action accumulator.
- A live cell exposes its canonical predecessor and adds its bit.
- A tombstone exposes its canonical predecessor and adds no bit.

Carrier recursion does not accept a free-standing `S` as a Base. Once a Base
boundary is recognized, an invalid active cell spine rejects rather than
falling through to a different carrier production. The final result belongs
to the innermost Local; old outer Locals need not have the same phase,
word, or fresh/marked status. Shell count is not equated with horizon.

## Opaque fields and the repeated Base continuation

Route audits, dormant-call arguments, retained action histories, Local seed
payloads, seed audits, continuation audits, halt audits, tombstone audits,
dormant environment payloads, and retained Base `beta` fields are not
decoded or compared with one another.

The Base continuation is a different field. The manuscript writes:

```text
alpha_Q = (E_Q (b E_seed)) B
Base_Q(R) = (B alpha_Q) R
```

The same `B` occurs twice. Pinned `CheckpointDecoder.parseBase?` explicitly
requires equality of those two continuation terms. This implementation
preserves that equality, checking it iteratively. Different continuation
copies with equal syntax are accepted; unequal syntax rejects. These are
not the independently quantified continuation **audit** fields of a Local.
The source check and the manuscript formula agree. Dropping this check
would define a larger independent-hole Base grammar, which is not the
reader implemented here.

## Permissive actions differ from the older fixed reader

Pinned `ActionParser.parse` checks the `PI` prefix and the label-determined
history count. It does **not** require the accumulator's outer cells to have
the labels that the chosen action would have emitted. The generic reader
follows that public grammar.

The older `queue_fixture.decode` adds an emitted-label check. Consequently
the two readers need not agree on arbitrary synthetic terms. A focused test
constructs a phase-zero, bit-one response for program `("1", "")` with one
history argument but an accumulator carrying an outer `0`. The generic
reader accepts its literal queue; the fixed reader rejects it. This is an
off-path grammar difference, not evidence of a constructor defect.

All **86 actual samples** of the original 85-contraction path have identical
readout decisions in the two readers. Exactly samples 0, 22 and 85 are
accepted, yielding `101`, `011` and `11` at horizons 0, 1 and 2. In
particular sample 55 remains rejected because its completed response chain
ends at a pending job rather than a matched positive terminal.

## Term-only parsing and limits of the result

Every grammar traversal enters a strict subtree: a continuation,
accumulator, predecessor, or Base queue child. Numerals, words, continuation
chains, carrier paths and route traversal are iterative. Exact syntax
comparison is iterative too, including deep fixed appendants and repeated
Base continuations. A temporary identity-pair set avoids revisiting shared
nodes during an equality check; it is not a term hash, retained execution
state, or provenance cache. Application dataclass equality and hashing are
never required.

The accepted domain is finite immutable `s_only.terms` syntax, including
shared acyclic terms. Arbitrary foreign root values and malformed public
constructors reject safely. Deliberately breaking the immutable AST contract
to inject cycles or invalid internal children is outside this domain.

Acceptance certifies this structural grammar. Synthetic accepted terms may
be unrelated to an encoded run; source reachability and all-sample reflection
are separate proof obligations. Native integration results are recorded in
[the two-phase experiments](two-phase-programs.md).

## Empty words and verification

The paper's trajectory is totalized: once the word is empty, later source
horizons keep it empty while advancing phase. The existing ordinary
`s_only.cts.step` instead raises `StopIteration` on an empty word. The reader
does not call either evaluator, and marked empty checkpoints retain the
paper's horizon/phase interpretation. Synthetic empty-checkpoint tests
explicitly distinguish that interpretation from ordinary stopping
semantics; they do not claim native reachability.

```sh
python -m unittest discover -s tests -p 'test_cts_reader.py' -v
```

The focused tests cover initial words through five bits, periods
1/2/3/5/7/8/9, all phase/bit routes in a non-power-of-two program,
multi-bit action-history counts, nested carriers and tombstones, independent
audits, the repeated Base continuation, malformed shapes and 2,056 small
trees. Deep cases include a 3,200-bit initial word, a 2,400-bit appendant and
history spine, 2,400-level numerals, over 2,100 Local shells, and 2,500-level
continuation copies. An isolation test disables source evaluation, encoders, the old
reader, native reduction, file reads, hashes, serialization, and recursive
term equality while rechecking the native samples out of order.

## Pinned sources

The upstream commit is
[`85a867988442fc423279341200f81634a1e65582`](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582).
Only source text was inspected; the upstream implementation, Lean checker,
and package installers were not executed.

- [Paper, Sections 4.2–4.3](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/paper.md#section-4-2)
- [CheckpointDecoder.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/CheckpointDecoder.lean): open environments, Local/Base parsing, term-only carrier decoding, completed chains and checkpoint validation
- [CarrierDecoder.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/CarrierDecoder.lean): strict descendant structure and public-carrier interpretation
- [CanonicalStep.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/CanonicalStep.lean): exact live/tombstone constructors and classifier priority
- [RouteParser.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/RouteParser.lean), [DispatchParser.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/DispatchParser.lean), and [ActionParser.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/ActionParser.lean): route code, selected response and permissive action checks
- [Upstream MIT notice](../third_party/cinematic-strawberry-MIT.txt)
