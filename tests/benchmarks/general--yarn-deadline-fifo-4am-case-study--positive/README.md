# `general--yarn-deadline-fifo-4am-case-study--positive`

A **general**-family positive benchmark for the YARN deadline FIFO model with four application
masters. A `ResourceManager` maintains a fixed five-job FIFO, dispatches to each free application
master in order, ages queued deadlines once per logical time unit, and records queue or execution
deadline misses.

## Provenance

- **Original source:** `examples.zip:ReLico-main/yarn-prop/yarn-deadline-fifo-4AMs.rebeca`.
- **Original property:** the shared `yarn.property` is intentionally excluded.
- **Adaptation:** fixed-size source normalization and explicit application-master identity tags.
  See [`ADAPTATION.md`](ADAPTATION.md).

## Preserved behavior

The five-entry FIFO is scalarized, statically bounded loops are expanded, increment syntax is made
explicit, finite delays are specialized to their proven values, and implicit sender dispatch is
represented by fixed identity tags. The scheduler remains naturally live through
`self.checkQueue() after(1)`. The `doneJobs` counters used only by the excluded external property
are projected out to keep RMC exploration finite and relevant to the checked executable behavior;
no auxiliary heartbeat or artificial traffic is present.

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

Validation results and pinned artifact details are recorded in [`RESULTS.md`](RESULTS.md). The
runtime stage is a bounded smoke test; RMC supplies whole-model state-space evidence.
