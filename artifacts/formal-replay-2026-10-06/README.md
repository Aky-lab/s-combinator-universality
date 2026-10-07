# Captured generic proof replay evidence

The result and interpretation are in [the replay report](../../docs/formal-replay.md).
`manifest.json` hashes every captured file here except itself.

- The three-import replay helper adds no declarations.
- Type/axiom output covers the 24 named interfaces.
- Source and before/after output manifests bind the exact replay inputs.
- `toolchain-manifest.json.gz` preserves the complete 17,505-file installation
  manifest. Its decompressed SHA-256 is
  `63e9784560dabaca6ef9142ae500eff02959007fb4f96673532cc625979a1fc8`.
- `BuildClosure-resumed.py` captures the recorded retry from module 39, with
  the first-attempt checkpoint preserved alongside it. A fresh reproduction
  should compile the entire dependency-first list from an empty output tree.
- The captured launcher uses the recorded cloud working-directory layout;
  its resource guard runs inside the isolated PID/proc namespace.
  `run_isolated.py` is the generic-replay launcher;
  `run_isolated-fixed38.py` also mounts the fixed-instance output read-only
  and adds that separate directory to the Lean module search path.

## Historical resource metadata

The raw canary status records preserve their original fields. Their outer
launcher memory observations do not measure Lean or enforce a namespace-wide
RSS cap. This includes older fields named `sampled_peak_aggregate_rss_bytes`
and `sampled_aggregate_rss_cap_bytes`. Use the inner `guard-*.json` records for
the actual sampled namespace observations in the final build/replay. The
report states their 50-ms sampling limitation. Canary exit codes and kernel
messages remain the acceptance/rejection evidence.
