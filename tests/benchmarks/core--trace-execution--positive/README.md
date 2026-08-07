# `core--trace-execution--positive`

This positive core benchmark exercises trace execution and trace
correspondence over a live bounded source containing a state assignment.

## Source behavior

`Controller()` initializes `x` to `5` and schedules `tick()` after one logical
time unit. The first `tick()` changes `x` from `5` to `7`; each `tick()` then
schedules the next `tick()` with the same delay. The recurring send preserves
liveness for the configured deadlock-freedom model-checking property.

The `5` to `7` assignment deliberately mirrors the assignment trace used by
the mapped formal evidence.

## Formal evidence boundary

Formal evidence is exactly 4 accepted obligations from
`Relico/Tests/TraceSimulation.lean`:

- `assignmentSourceTrace` establishes the DTR assignment trace;
- `assignment_trace_has_matching_lf_trace` establishes a matching LF trace;
- `assignmentTargetTrace` establishes the LF assignment trace;
- `assignment_trace_has_matching_dtr_trace` establishes a matching DTR trace
  and resulting runtime well-formedness.

These obligations cover the trace-level forward and backward correspondence
for the assignment step.

## Runtime scope

The terminal runtime stage executes the generated `V0Controller` binary using
bounded execution with `--timeout "5 msec" --fast`.

A passing runtime artifact is an execution observation. It is not presented as
a proof of termination or as a replacement for the mapped formal obligations.

## Route

`source,rmc,parser-json,decoded-dtr-ast,formal-witness,translated-lf-ast,lf-source,lfc,runtime`

The tracked package is designed to contain thirteen files: this README,
`coverage.json`, `manifest.json`, one source model, and nine deterministic
expected artifacts. Generated `actual/` and work products remain ignored.
