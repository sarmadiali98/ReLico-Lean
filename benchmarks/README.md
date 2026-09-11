# ReLico application benchmarks

This directory contains empirical and application-level Timed Rebeca benchmarks derived from
external corpora. They evaluate complete model translation, generated Lingua Franca compilation,
runtime behavior, and, where applicable, RMC state-space behavior.

These models are distinct from the purpose-built translator conformance fixtures under
`tests/translator/`. Each adapted external model records its provenance and semantic changes in its
own `README.md` and, where needed, `ADAPTATION.md`.

The shared execution catalog is `evaluation/registry/benchmarks.tsv`. Rows with suite `benchmark` resolve
their source and manifest beneath this directory. Generated `actual/` and
`.expected-regeneration/` directories are never committed.
