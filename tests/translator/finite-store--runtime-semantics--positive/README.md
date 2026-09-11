# finite-store--runtime-semantics--positive

Positive finite-store runtime-semantics benchmark for a two-variable store and cross-variable assignment.

The first nine stages execute the real source, RMC, parser, Lean export, formal-witness, LF compilation, and bounded native runtime route. The formal witness covers exactly 45 accepted obligations across six Lean modules: 13 are shared-formal evidence and 32 are source-capability evidence.

`coverage-manifest` records the canonical obligation and shared-formal metadata partition. `trust-report` records successful elaboration of all six formal modules and the shared-formal justifications. No actor or message-server priority is required by this benchmark.
