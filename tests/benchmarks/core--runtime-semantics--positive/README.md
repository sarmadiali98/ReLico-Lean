# `core--runtime-semantics--positive`

This positive core benchmark exercises runtime semantics over a live bounded
source containing both state assignment and recurring delayed self-send.

## Source behavior

`Controller()` initializes `x` to `0` and schedules `tick()` after one logical
time unit. Each `tick()` assigns the bounded value `1` and schedules the next
`tick()` with the same delay. The recurring send preserves liveness for the
configured deadlock-freedom model-checking property.

## Formal evidence boundary

Formal evidence is exactly 21 accepted obligations across:

- `Relico/Tests/BackwardSimulation.lean` — 4 obligations;
- `Relico/Tests/RuntimeInvariant.lean` — 4 obligations;
- `Relico/Tests/SmallStep.lean` — 13 obligations.

These obligations cover assignment and scheduling small-step behavior,
backward matching, and runtime well-formedness invariants.

## Runtime scope

The terminal runtime stage executes the generated `V0Controller` binary using
bounded execution with `--timeout "5 msec" --fast`.

A passing runtime artifact is an execution observation. It is not presented as
a proof of termination or as a replacement for the mapped formal obligations.

## Route

`source,rmc,parser-json,decoded-dtr-ast,formal-witness,translated-lf-ast,lf-source,lfc,runtime`

The tracked package contains thirteen files: this README, `coverage.json`,
`manifest.json`, one source model, and nine deterministic expected artifacts.
Generated `actual/` and work products remain ignored.
