# Semantic audit of the complete proof

7 October 2026. Source-level examination of the machine compiler, UT19
simulation, generated S origins and final theorem found no semantic or
circularity defect in the stated result. The main source fingerprint is
`0cfa1200ea02ebdb5e59df976c8d29301520ec3704c05853c7150684ae37374d`.

## Checked composition points

- The source instruction model is ordinary natural-register INC/DECJZ/HALT.
  Input vectors and program tables are arbitrary finite data.
- Initialization, amnesiac macros, Waterfall row arithmetic, guarded BP2
  blocks and falling-off halt execute the literal compiled programs. The
  dense Nat-counter bridge agrees with the UT19 source semantics.
- The formal compiler's uniform five-helper/+5 variant is distinct from the
  earlier selective/+1 Python variant. The new frontend report and bounds
  describe the actual formal definitions.
- Actual assembled UT19 passes cover every microstep. Positive progress
  makes the nonhalting argument cofinal, rather than a statement only at
  selected macro boundaries. Zero-decrement protection and restart are
  explicitly included.
- The temporal initializer realizes every programmed width under arbitrary
  forcing throughout its protected window. The authored published-table
  theorem separately checks all-slot width equality and initialized-memory
  identity.
- One-hot source translation covers arbitrary finite words and every CTS
  offset. Empty states cannot fabricate a designated head event.
- Whole-tree origin preservation follows actual C4, response, ancestor, job
  and stage constructors. Source permissions are discharged from earlier
  source labels; they are not an assumed global generated-trace invariant.
- Proper target-response samples retain the old target-free origin set.
  Only the final response adds the exact selected label/snapshot pair.
  The +57 count is one C4 followed by 56 FRAME/route/appender contractions.
- Every matching first-event shell has the same frozen audit. The fixed
  preorder decoder keeps its first match, including malformed payloads;
  it never chooses a convenient later witness.
- The final theorem supplies `machine_noPrematureEmpty` and the successful
  numerical read from actual compiler outputs. Those earlier interface
  conditions do not remain hypotheses of the final equivalences.
- Controller, selector, observer and decoder are independent of source
  machine/input. Only the encoder receives that data.

## Important interface distinctions

For arbitrary CTS words, `NoPrematureEmpty` is a real condition: a one-bit
zero word empties without a designated event. An arbitrary designated event
also need not encode a numerical result. The final compiler proves the
required liveness and numerical properties for its outputs; generic
interface theorems are not silently applied outside those conditions.

The observer is a finite bottom-up recognizer. Recursive evaluation may use
an input-sized stack; this does not introduce a source simulator into a
transition. The actual numerical decoder has one strict-descendant recursive
carrier call per iteration. Quadratic spine-list work must be included in
its cubic occurrence-tree bound; structural termination alone would not
establish polynomiality.

The literal functional temporal transform and list-index schedule code need
not have the exact operation count of an optimized butterfly implementation.
Their construction remains polynomial in the finite emitted dimensions,
which supports the stated singly exponential binary-input encoding bound.

The Turing-machine-to-register-machine reduction and complete bit-cost model
are written mathematical arguments. The final kernel result certifies the
register-machine simulation, exact first event and result. The audit does not
adjudicate novelty or prize acceptance.
