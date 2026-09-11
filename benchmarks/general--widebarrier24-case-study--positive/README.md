# `general--widebarrier24-case-study--positive`

A **general**-family positive benchmark for the original WideBarrier24 model. A `Coordinator`
executes 40 rounds; each round schedules 24 tokens after one time unit and starts the next round
only after all 24 arrive. An independent `KeepAlive` actor toggles every 100000 time units. Two
reactive classes, two instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/WideBarrier24/WideBarrier24.rebeca`, 93 lines.
- **Original property:** `WideBarrier24.property` is intentionally excluded. This fixture evaluates
  translation and runtime behavior only; it does not translate or enforce the property.
- **Adaptation:** none; the archived Rebeca source is preserved byte-for-byte. See
  [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- the source stage passes and the fixture source is byte-identical to the archived model;
- RMC 2.14 reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`, reaching 3,006 states
  and 39,130 transitions;
- parser JSON, decoded DTR AST, translated LF AST, and LF source export pass;
- `lfc 0.11.0` compiles the generated C++ target;
- the generated runtime exits successfully under the 5 msec logical-time budget;
- all eight pipeline artifacts are preserved and SHA-256-pinned in `manifest.json`.

The runtime stage is a bounded smoke test; RMC supplies whole-model state-space evidence.
