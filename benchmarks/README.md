# ReLico application benchmarks

This directory contains empirical and application-level Timed Rebeca benchmarks derived from
external corpora. They evaluate source-model acceptance, complete-model translation, generated
Lingua Franca compilation, and declared runtime observations. RMC results are independent
source-model evidence; compilation and process execution do not by themselves establish
source-target behavioral equivalence.

## RMC Assertion semantics

Benchmark-local RMC `Assertion` properties are source-level assertions checked over reachable
post-transition states of the adapted Timed Rebeca model. `TRUE` means no violating reachable state
was found; `FALSE` means RMC found a counterexample execution. Expected-`FALSE` properties use that
counterexample as a witness for an observed state or intended failure path. Such a counterexample
witness is not a liveness claim. A monitor-contract check reports that no observed event violated
the contract, but does not independently establish that the monitored event occurred. These
source-level assertions do not establish preservation through the Lean/LF translation pipeline.

These models are distinct from the purpose-built translator capability fixtures under
`tests/translator/`. Each adapted external model records its provenance and semantic changes in its
own `README.md` and, where needed, `ADAPTATION.md`.

The shared execution catalog is `evaluation/registry/benchmarks.tsv`. Rows with suite `benchmark` resolve
their source and manifest beneath this directory. Generated `actual/` and
`.expected-regeneration/` directories are never committed.

The VMCAI 2027 benchmark suite remains under active development and is not yet frozen for artifact
submission. See [`evaluation/README.md`](../evaluation/README.md) for current registry and evidence
semantics.
