# `general--fibonacci-case-study--positive`

A **general**-family positive benchmark for the Fibonacci model. A `Source` requests input 10,
`FibCore` reports the model's result after 10 time units, and `Checker` records an incorrect result;
an independent `KeepAlive` actor toggles phase every 100 time units. Four reactive classes, four
instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/Fibonacci/Fibonacci.rebeca`.
- **Original property:** `Fibonacci.property` is excluded; this fixture evaluates translation and
  runtime behavior only.
- **Adaptation:** no semantic correction or timing redesign; see [`ADAPTATION.md`](ADAPTATION.md).

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Semantic property

The benchmark-local RMC assertion checks that the monitor never observes a result other than 89.
It validates the benchmark monitor, but does not independently prove result delivery.
