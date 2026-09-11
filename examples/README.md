# Real evaluation examples

This directory holds the real-example demonstration runs of the ReLico
pipeline: the paper's own evaluation corpus, translated and compiled as
programs, separate from the application benchmark suite under `benchmarks/`.

Nothing here adds to the benchmark registry. The registry is an
infrastructure validation layer; this area exists to demonstrate
translation and compilation support for the real evaluation models
themselves. Property and specification files are out of scope.

## Structure

- `tier2/` — the upstream corpus models the current verified fragment
  accepts, run through the pipeline **unmodified**, one row per model in
  `RESULTS.tsv`.
- `tier3/` — **relocated.** The paper-named case studies now live in the
  benchmark suite itself, as `general--<name>-case-study--positive` rows
  under `benchmarks/` with the full benchmark layout plus an
  `ADAPTATION.md` before/after record. First entry:
  `general--smarthome-case-study--positive`, the RQ2 ESP32 case study.

## Source provenance

The models live in the upstream artifact archive (`examples.zip` in the
repository root, local-only), under `ReLico-main/`. Each results row names
its source by archive path. The archive is the paper's own evaluation
corpus: the Rebeca examples distribution plus the case-study models.

## Pipeline used

Identical to the benchmark pipeline and nothing else: the Java parser
bridge, the three `lean-export --family general` modes, `lfc 0.11.0` with
the C++ target, the generated binary, and -- as a recorded bonus, not a
gate -- the Rebeca model checker. See `tier2/RESULTS.tsv` for the column
meanings.
