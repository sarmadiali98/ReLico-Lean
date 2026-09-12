# `general--processmsg-case-study--positive`

A **general**-family positive benchmark for the original ProcessMsg model. A `Source` sends zero to
a `Task`, the task schedules processing after 10 time units, and a `Checker` records a violation if
processing does not report success. An independent `KeepAlive` actor toggles every 100 time units.
Four reactive classes, four instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/ProcessMsg/ProcessMsg.rebeca`, 86 lines.
- **Original property:** `ProcessMsg.property` is intentionally excluded. This fixture evaluates
  translation and runtime behavior only; it does not translate or enforce the property.
- **Adaptation:** none; the archived Rebeca source is preserved byte-for-byte. See
  [`ADAPTATION.md`](ADAPTATION.md).

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- the source stage passes and the fixture source is byte-identical to the archived model;
- RMC 2.14 reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`, reaching 6 states
  and 7 transitions;
- parser JSON, decoded DTR AST, translated LF AST, and LF source export pass;
- `lfc 0.11.0` compiles the generated C++ target;
- the generated runtime exits successfully under the 5 msec logical-time budget;
- all eight pipeline artifacts are preserved and SHA-256-pinned in `manifest.json`.

## Semantic properties

The benchmark-local RMC source-level assertions check the adapted Timed Rebeca source. The
monitor-contract check finds no observed invalid processing result, and the consistency assertion
checks that an observed successful task state stores message zero. The expected-`FALSE` assertion
provides a counterexample witness for an observed successful task state.
