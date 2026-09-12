# `general--yarn-deadline-fifo-3am-case-study--positive`

A **general**-family positive benchmark for the YARN deadline FIFO model with three application
masters. A `ResourceManager` maintains a fixed four-job FIFO, dispatches to each free application
master in order, ages queued deadlines once per logical time unit, and records queue or execution
deadline misses.

## Provenance

- **Original source:** `examples.zip:ReLico-main/yarn-prop/yarn-deadline-fifo-3AMs.rebeca`.
- **Original property:** the shared `yarn.property` is intentionally excluded.
- **Adaptation:** fixed-size source normalization and explicit application-master identity tags.
  See [`ADAPTATION.md`](ADAPTATION.md).

## Preserved behavior

The four-entry FIFO is scalarized, statically bounded loops are expanded, increment syntax is made
explicit, finite delays are specialized to their proven values, and implicit sender dispatch is
represented by fixed identity tags. The scheduler remains naturally live through
`self.checkQueue() after(1)`; no auxiliary heartbeat or artificial traffic is present.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Semantic properties

- **SI:** marker coherence checks that queue-expiration counts are bounded and that queue,
  execution-miss, and completion observations are mutually consistent after each transition.
- **RW:** the expected-`FALSE` completion assertion provides a counterexample witness for an
  observed successful `ResourceManager.update` event.

The markers describe only the most recently executed resource-manager handler. They are not
cumulative counters and do not establish liveness, complete scheduling correctness, or translation
preservation.

## Evidence

Validation results and pinned artifact details are recorded in [`RESULTS.md`](RESULTS.md). The
runtime stage is a bounded smoke test; RMC supplies whole-model state-space evidence.
