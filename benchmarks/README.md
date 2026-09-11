# ReLico application benchmarks

This directory contains empirical and application-level Timed Rebeca benchmarks derived from
external corpora. They evaluate source-model acceptance, complete-model translation, generated
Lingua Franca compilation, and declared runtime observations. RMC results are independent
source-model evidence; compilation and process execution do not by themselves establish
source-target behavioral equivalence.

These models are distinct from the purpose-built translator conformance fixtures under
`tests/translator/`. Each adapted external model records its provenance and semantic changes in its
own `README.md` and, where needed, `ADAPTATION.md`.

The shared execution catalog is `evaluation/registry/benchmarks.tsv`. Rows with suite `benchmark` resolve
their source and manifest beneath this directory. Generated `actual/` and
`.expected-regeneration/` directories are never committed.

The VMCAI 2027 benchmark suite remains under active development and is not yet frozen for artifact
submission. See [`evaluation/README.md`](../evaluation/README.md) for current registry and evidence
semantics.
