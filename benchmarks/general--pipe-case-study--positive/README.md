# `general--pipe-case-study--positive`

A **general**-family positive benchmark for the original Pipe model. A `Source` sends the value one
through a `Node`, which forwards it after 10 time units to a `Sink`; the sink reports completion to
a `Checker`. An independent `KeepAlive` actor toggles every 100 time units. Five reactive classes,
five instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/Pipe/Pipe.rebeca`, 92 lines.
- **Original property:** `Pipe.property` is intentionally excluded. This fixture evaluates
  translation and runtime behavior only; it does not translate or enforce the property.
- **Adaptation:** none; the archived Rebeca source is preserved byte-for-byte. See
  [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- the source stage passes and the fixture source is byte-identical to the archived model;
- RMC 2.14 reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`, reaching 7 states
  and 8 transitions;
- parser JSON, decoded DTR AST, translated LF AST, and LF source export pass;
- `lfc 0.11.0` compiles the generated C++ target;
- the generated runtime exits successfully under the 5 msec logical-time budget;
- all eight pipeline artifacts are preserved and SHA-256-pinned in `manifest.json`.
