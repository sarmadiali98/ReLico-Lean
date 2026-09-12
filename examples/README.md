# External corpus validation

This directory holds the external corpus validation runs of the ReLico pipeline: the paper's own
evaluation corpus, translated and compiled as programs, separate from the application benchmark
suite under `benchmarks/`. These runs measure pipeline acceptance on unsolicited upstream models;
they are not included in the translator capability fixture or application benchmark counts.

Nothing here adds to the benchmark registry. The registry is an
infrastructure validation layer; this area exists to demonstrate
translation and compilation support for the real evaluation models
themselves. Property and specification files are out of scope.

## Structure

- `tier2/` contains 21 unmodified upstream models that passed the measured frontend screen. Twelve
  completed the recorded translation-to-runtime demonstration; the remaining nine expose documented
  translation or runtime boundaries. These runs are empirical pipeline evidence, not additional
  formal verification claims.
- `tier3/` — **relocated.** The paper-named case studies now live in the
  benchmark suite itself, as `general--<name>-case-study--positive` rows
  under `benchmarks/` with the full benchmark layout plus an
  `ADAPTATION.md` before/after record. First entry:
  `general--smarthome-case-study--positive`, the RQ2 ESP32 case study.

## Source provenance

The models live in the upstream artifact archive (`examples.zip`, a local provenance snapshot that
is not part of the distributed repository contract), under `ReLico-main/`. Each results row names
its source by archive path. The archive is the paper's own evaluation
corpus: the Rebeca examples distribution plus the case-study models.
Registered benchmark directories contain committed source copies and provenance records; rerunning
`examples/tier2` additionally requires the matching archive.

## Pipeline used

Identical to the benchmark pipeline and nothing else: the Java parser
bridge, the three `lean-export --family general` modes, `lfc 0.11.0` with
the C++ target, the generated binary, and -- as a recorded bonus, not a
gate -- the Rebeca model checker. See `tier2/RESULTS.tsv` for the column
meanings.

The non-gating RMC policy applies only to these unregistered demonstration runs. Registry-backed
translator fixtures and application benchmarks follow the mandatory stage policy in
[`evaluation/README.md`](../evaluation/README.md).
