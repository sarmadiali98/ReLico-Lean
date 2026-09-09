# `general--pingpong-case-study--positive`

A **general**-family positive benchmark for the original PingPong model. `Ping` starts a finite
request/reply exchange with `Pong`, with 10-time-unit delays before the request and reply. A
`Checker` observes both directions, while an independent `KeepAlive` actor toggles every 100 time
units. Four reactive classes, four instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/PingPong/PingPong.rebeca`, 97 lines.
- **Original property:** `PingPong.property` is intentionally excluded. This fixture evaluates
  translation and runtime behavior only; it does not translate or enforce the property.
- **Adaptation:** none; the archived Rebeca source is preserved byte-for-byte. See
  [`ADAPTATION.md`](ADAPTATION.md).

The model is distinct from the existing trigger and periodic ping-pong composition fixtures: this
is a finite four-actor checked exchange rather than a recurring two-node composition.

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- the source stage passes and the fixture source is byte-identical to the archived model;
- RMC 2.14 reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`, reaching 20 states
  and 43 transitions;
- parser JSON, decoded DTR AST, translated LF AST, and LF source export pass;
- `lfc 0.11.0` compiles the generated C++ target;
- the generated runtime exits successfully under the 5 msec logical-time budget;
- all eight pipeline artifacts are preserved and SHA-256-pinned in `manifest.json`.
