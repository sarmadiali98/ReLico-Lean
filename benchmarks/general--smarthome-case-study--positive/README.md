# `general--smarthome-case-study--positive`

A **general**-family positive case-study benchmark: the paper's RQ2 ESP32
smart-home system — eight reactive classes (`Heater`, `Light`, `Door`,
`TempSensor`, `LightSensor`, `MotionSensor`, `RoomController`,
`CentralController`) monitoring temperature, light and motion, controlling
heater and light, and coordinating door and alarm policy.

Case-study rows own no Lean obligations; their evidence is the pipeline
artifacts themselves, the same shape as the examples2 composition rows.

## Provenance

- **Original source:** `examples.zip:ReLico-main/smarthome/smarthome.rebeca`,
  359 lines, unmodified upstream.
- **Original blocker**, measured against the unmodified source:
  `unsupported by the ReLico general parser bridge: environment variable`.
- **Adaptations:** three, each forced by a measured refusal and each
  semantic-preserving — the `env` constants folded into literals (18
  declarations, 34 substitutions; forced ultimately by D9, an LF connection
  delay is static), two self-sends qualified (`report(9)` →
  `self.report(9)`), and nine marker parameters on parameterless
  external-send targets. The full before/after record, including the two
  fold shapes that were tried and refused first, is in
  [`ADAPTATION.md`](ADAPTATION.md); the measured stage results are in
  [`RESULTS.md`](RESULTS.md).

The adapted source is 341 lines against the original 359; the difference
is the removed `env` block alone.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`,
`decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`,
through the `--family general` arm. Benchmark-local source-level assertions check the configured
cold-scenario constraints. The expected-`FALSE` assertion provides a counterexample witness for
observed heater actuation; these assertions do not establish behavior through the Lean/LF pipeline.

## Evidence

- every pipeline stage exits 0;
- the generated LF carries 8 reactors;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`
  on the adapted source.

## Keep-alive

Sensors recur on delayed self-sends and the controllers react to messages,
so no zero-delay recurrence exists; the runtime terminates within its
budget.
