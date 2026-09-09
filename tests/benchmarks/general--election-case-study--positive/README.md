# `general--election-case-study--positive`

A **general**-family positive benchmark for the Election model. A `Source` sends competing values
through direct and routed paths; `Node0`, `Router`, and `Node1` select node 1, while `Checker`
records the election result. An independent `KeepAlive` actor toggles every 100 time units. Six
reactive classes, six instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/Election/Election.rebeca`.
- **Original property:** `Election.property` is excluded; this fixture evaluates translation and
  runtime behavior only.
- **Adaptation:** no semantic correction or timing redesign; see [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.
