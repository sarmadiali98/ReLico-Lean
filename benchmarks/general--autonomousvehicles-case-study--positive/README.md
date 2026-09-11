# `general--autonomousvehicles-case-study--positive`

A **general**-family positive benchmark: the paper-named AutonomousVehicles model — a ring of 33 segment chains connecting six facilities (`DecisionStation`, `PrePoint`, `WheelLoader`, `PrimaryCrusher`, `SecondaryCrusher`, `CrossController`), on which vehicles circulate through loading, unloading, charging and a mutex-protected crossing; `DecisionStation` observes when every vehicle has completed the required traversal.

## Provenance

- **Original source:** `examples.zip:ReLico-main/AutonomousVehicles.rebeca`, 517 lines, 10 classes.
- **Original blockers:** environment variables (12); rebec-typed state variables (A1); dynamic sender capture (`segRequestingCross`); 34 `sender`/`instanceof` reply-dispatch sites; null-encoded topology (~40 null constructor arguments and 7-way null-chain forwarding); computed delays; `assertion(false)` x8.
- **Redesign:** the approved category-3 redesign — tag routing over full static bindings, per the mapping in [`ADAPTATION.md`](ADAPTATION.md). 409 lines, 7 classes, 39 instances (33 segments + 6 facilities).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`.

## Scenario note

`NUMBER_VEHICLES` is folded to 2 (the original model's own designed range is 1-8): the 4-vehicle state space exceeds the pipeline's fixed 60-second model-checker budget (measured timeout). Two vehicles preserve the contested behaviors — segment contention, the crossing mutex, PrePoint route alternation, and resend retries.
