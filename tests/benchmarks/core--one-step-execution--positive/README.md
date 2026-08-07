# `core--one-step-execution--positive`

This positive core benchmark witnesses one-step execution over a live bounded source.

## Source behavior

`Controller()` initializes `x` to `0` and schedules `step`. Each `step` assigns the bounded value `1` and schedules the next `step`. The source remains live so the required RMC deadlock-freedom property is preserved. Whole-program termination is not claimed.

## Formal evidence boundary

Formal evidence is exactly the four accepted theorem obligations in `Relico/Tests/MachineTraceForward.lean`:

- `assignmentForwardExecutionCompatible`
- `assignment_machine_trace_forward`
- `dispatchForwardExecutionCompatible`
- `dispatch_machine_trace_forward`

The one-step claim is the formal single-step/machine-trace witness. Source, parser, exporter, LFC, and runtime outputs are route evidence and do not broaden the formal boundary.

## Runtime scope

The recurring source is observed through bounded runtime execution. Runtime success is not a termination claim.

## Package contract

The tracked package contains thirteen files: this README, `coverage.json`, `manifest.json`, one source model, and nine expected artifacts.

Required route:

`source,rmc,parser-json,decoded-dtr-ast,formal-witness,translated-lf-ast,lf-source,lfc,runtime`

The terminal stage is `runtime`; all stage commands are list-form. Generated `actual/` and `work/` content remains ignored. Wrapper receipt directories are not required.

## Exclusions

No production, formal, toolchain, or paper changes are part of this benchmark. Exemplar evidence is not inherited.
