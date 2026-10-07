# Source and event interface replay

Nine project modules were compiled against the previously verified pinned
423-module dependency closure and concrete SOnly38 instance.

The import-only SOnlyBridgesReplay wrapper passed official Lean 4.33.1
`leanchecker --fresh` with exit status zero. The full declaration audit queried
242 public types, definitions and theorem declarations. Reported dependencies
were limited to propext, Quot.sound and Classical.choice.

Final build logs, inner resource-guard receipts, exact source/output manifests,
and post-replay integrity results are preserved here. The wrapper imports the
source/event stage, initial observer, provenance and counter modules; its
transitive closure includes all nine modules listed in the result manifest.

The generic source/toolchain identity and isolation controls are documented in
[the original replay](../../docs/formal-replay.md). The additional replay search
directory was read-only and contained only the frozen project outputs and
import-only wrapper. It did not include development canaries.

[The interface report](../../docs/formal-event-interfaces.md) states the proved
results and composition boundary. The [result manifest](../../results/formal_event_interfaces.json)
lists exact source identities and verification data.
