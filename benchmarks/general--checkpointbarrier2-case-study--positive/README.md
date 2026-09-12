# `general--checkpointbarrier2-case-study--positive`

A **general**-family positive benchmark for the CheckpointBarrier2 model. A bounded `Coordinator`
advances eight epochs and accepts two delayed arrivals per epoch, while an independent `KeepAlive`
actor toggles phase on a long periodic self-loop. Two reactive classes, two instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/CheckpointBarrier2/CheckpointBarrier2.rebeca`.
- **Original property:** `CheckpointBarrier2.property` remains excluded. Benchmark-local source-level
  assertions check observed coordination bounds and provide a final-barrier counterexample witness.
- **Adaptation:** no semantic correction or timing redesign; see [`ADAPTATION.md`](ADAPTATION.md).

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm. The
expected-`FALSE` assertion provides a counterexample witness for both arrivals at the eighth epoch.
