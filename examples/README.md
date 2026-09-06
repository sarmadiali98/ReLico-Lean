# Real evaluation examples

This directory holds the real-example demonstration runs of the ReLico
pipeline: the paper's own evaluation corpus, translated and compiled as
programs, separate from the benchmark suite under `tests/benchmarks/`.

Nothing here adds to the benchmark registry. The registry is an
infrastructure validation layer; this area exists to demonstrate
translation and compilation support for the real evaluation models
themselves. Property and specification files are out of scope.

## Structure

- `tier2/` — the upstream corpus models the current verified fragment
  accepts, run through the pipeline **unmodified**, one row per model in
  `RESULTS.tsv`.
- later phases: the paper-named systems that need one minimal source
  adaptation each (`smarthome`, `TinyOSPV6-MACB`, `TinyOSPV6-TDMA`,
  `LeasingNRPFD`, `AutonomousVehicles`, and others), with the adapted
  source beside its results row.

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
