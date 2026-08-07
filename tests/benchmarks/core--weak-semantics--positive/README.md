# `core--weak-semantics--positive`

This positive core benchmark exercises the weak-semantics evidence boundary
over a live timed source and the complete generated LF/C++ runtime route.

## Source behavior

`Controller()` initializes `phase` to `0` and schedules `tick()` after one
logical time unit.

The single `tick()` message server executes `phase = 1`, then `phase = 2`,
and schedules itself again after one logical time unit. The recurring delayed
self-send keeps the model live while producing an executable path containing
statement execution, logical-time advance, and message-consumption phases.

The source intentionally contains exactly one message server. The prototype
diagnostic reproduced rejection of the prior two-message-server design by the
executed ReLico v0 parser bridge and confirmed that this single-message-server
form passes the canonical `parser-json` stage.

## Formal evidence boundary

Formal evidence remains exactly 47 accepted obligations across three modules:

- 10 obligations from
  `Relico/Tests/DirectLFDetailedBackwardWeakSimulation.lean`;
- 16 obligations from
  `Relico/Tests/DirectLFDetailedPhaseWeakBisimulation.lean`;
- 21 obligations from
  `Relico/Tests/WeakTransitionFoundation.lean`.

The mapped evidence covers tau closure, weak tau steps, weak visible steps,
tau stuttering, observable projection, forward and backward phase matching,
detailed backward matching for statements, time advance, microsteps and
consumption, and source correspondence.

The source model is an executable exemplar for that evidence boundary. The
runtime artifact does not itself prove the 47 formal obligations.

## Runtime scope

The terminal runtime stage executes the generated `V0Controller` binary using
bounded execution with `--timeout "5 msec" --fast`.

A passing runtime artifact is a bounded execution observation. It is not
presented as a proof of termination, weak bisimulation, or backward
simulation; those claims remain grounded in the mapped Lean obligations.

## Route

`source,rmc,parser-json,decoded-dtr-ast,formal-witness,translated-lf-ast,lf-source,lfc,runtime`

The tracked package is designed to contain thirteen files: this README,
`coverage.json`, `manifest.json`, one source model, and nine deterministic
expected artifacts. Generated `actual/` and work products remain ignored.
