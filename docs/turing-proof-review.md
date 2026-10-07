# Conventional tape compiler: independent semantic review

7 October 2026. The reviewed source snapshot is identified by the hashes in
`results/formal_turing_universality.json`. No blocking semantic defect was found.

The source machine has an actual integer-indexed tape and absolute head,
finite state/alphabet types, and arbitrary finite input. Its all-cell
representation relation covers blank extension and every movement without a
space bound. Positive-digit stack coding is injective, including explicit
blank cells; empty pop and all quotient/remainder cases are proved.

The compiler constructs a literal finite INC/DECJZ/HALT table. Assembled
push/pop row identities discharge the generic macro hypotheses. Scratch is
restored and the other stack is preserved. The instruction table depends only
on the Turing machine; entry selection uses the first input symbol. Every
source transition has a positive finite target duration.

The checkpoint reflection argument covers all target microsteps. A halted
target configuration is absorbing, and a source prefix of length t supplies a
checkpoint at elapsed time at least t unless the source has already halted.
Thus target halting cannot be hidden between checkpoints. The final-state
version reconciles complete target configurations, establishing numerical
result reflection as well as halting.

The joined S theorem keeps the existing controller, selector, regular event
and current-tree decoder unchanged. Its encoder is executable and choice-free.
Its final equivalences contain no residual simulation or eventual-event
hypothesis. The checked numerical TM observable is the specified simulation's
finite left-stack code, including visited extent and retained blanks. It is
history-dependent, not an unspoken canonical final-tape output convention.

Independent bounded transcriptions additionally checked:

- 2,624 pushes and 808 pops, including exact cost, scratch restoration and unrelated registers
- 29,400 assembled transitions, totaling 1,092,420 literal microsteps
- 750 finite-label lookup roundtrips
- 135,048 tape/stack transitions and 1,755,624 absolute-cell comparisons
- 59 finite-word coding cases

All passed. These bounded checks complement the source audit; the separate
67-module fresh-kernel replay establishes the universal formal statements.
The main source hash is
`9a8b1e653f5e5f0c206a4be305deb24be51e7e1f7ae93e9e9a200862d02056a3`;
the concrete compiler hash is
`d054db00cd2f726aa380cb7290abc012634a2f4e69d4dfebd7d4a901c58e912b`.
