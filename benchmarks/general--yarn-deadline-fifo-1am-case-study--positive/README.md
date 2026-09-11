# `general--yarn-deadline-fifo-1am-case-study--positive`

A **general**-family positive benchmark for the YARN deadline FIFO model with one application
master. A `ResourceManager` maintains a fixed two-job FIFO, dispatches at most one job at a time,
ages queued deadlines once per logical time unit, and records queue or execution deadline misses.
The `AppMaster` completes jobs after two units and cycles its successful-job counter through 1-5.

## Provenance

- **Original source:** `examples.zip:ReLico-main/yarn-prop/yarn-deadline-fifo-1AMs.rebeca`.
- **Original property:** the shared `yarn.property` is intentionally excluded. This fixture does not
  translate or enforce its bounded reachability assertion.
- **Adaptation:** fixed-size source normalization only. See [`ADAPTATION.md`](ADAPTATION.md).

## Preserved behavior

The two-entry FIFO is scalarized, statically bounded loops are expanded, increment syntax is made
explicit, finite delays are specialized to their proven values, and the single-sender update guard
is removed. The scheduler remains naturally live through `self.checkQueue() after(1)`; no auxiliary
heartbeat or artificial traffic is present.

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

Validation results and pinned artifact details are recorded in [`RESULTS.md`](RESULTS.md). The
runtime stage is a bounded smoke test; RMC supplies whole-model state-space evidence.
