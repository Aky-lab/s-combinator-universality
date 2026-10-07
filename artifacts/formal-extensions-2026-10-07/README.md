# Extended source and event kernels

Seven additional modules were compiled against the frozen nine-module
[source/event checkpoint](../formal-interfaces-2026-10-07/). The combined
16-module project closure passed official Lean 4.33.1 fresh-kernel replay.

The extension audit queried 160 explicit public declarations; together with
the earlier 242 queries, reported dependencies are limited to propext,
Quot.sound and Classical.choice. Exact source identities, final build logs,
read-only replay wrapper, resource-guard records and before/after integrity
manifests are preserved here.

[Proof interfaces and scope](../../docs/formal-extended-kernels.md)
[Machine-readable result](../../results/formal_extended_kernels.json)
