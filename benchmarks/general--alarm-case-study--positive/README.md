# `general--alarm-case-study--positive`

A **general**-family positive benchmark for the original Alarm model. A `Controller` raises a
fault and schedules `turnOff(0)` after 1000 time units, a `Checker` observes the resulting value,
and an independent `KeepAlive` actor toggles phase every 2000 time units. Three reactive classes,
three instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/Alarm/Alarm.rebeca`, 70 lines.
- **Original property:** `Alarm.property` is intentionally excluded. This fixture evaluates
  translation and runtime behavior only; it does not translate or enforce the property.
- **Adaptation:** no semantic correction or timing redesign; see [`ADAPTATION.md`](ADAPTATION.md).

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- the source stage passes;
- RMC 2.14 reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- the generated runtime exits successfully under the benchmark runtime stage.

## Semantic property

The benchmark-local RMC assertion is expected to be false: the checker monitor records the
documented failed shutdown. This is an intentional safety counterexample, not a failed benchmark.
