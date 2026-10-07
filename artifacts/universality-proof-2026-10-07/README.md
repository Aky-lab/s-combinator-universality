# End-to-end proof verification

All 56 project modules were clean-built with the verified official Lean 4.33.1
distribution against the pinned generic dependency closure. The import-only
wrapper then passed fresh official-kernel replay. The 1,142 explicit public
declaration queries reported only propext, Quot.sound and Classical.choice.

The main encoder, source compiler, observer and decoder data definitions have
no Classical.choice dependency. Executable encoder cuts are recorded in
SOnlyEncoderExecution.lean and its log.

Positive and negative controls were rerun in a separate read-only import
directory. The ordinary invalid source was refused; the injected invalidFalse
theorem compiled but fresh replay rejected its proof as Prop instead of False.
Canary sources are test inputs and are excluded from the proof import path.

Source/output manifests, final theorem types, all module build logs, resource
guards, checker logs and post-replay identity checks are preserved here.

[Final verification report](../../docs/final-verification.md)
[Exact result manifest](../../results/formal_universality.json)
