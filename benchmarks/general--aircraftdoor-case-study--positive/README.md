# `general--aircraftdoor-case-study--positive`

A **general**-family positive benchmark: the paper's RQ1 AircraftDoor model — a `Controller` starts a `Vision` component and a `KeepAlive` heartbeat, the `Vision` commands the `Door` from ramp state, and a `Monitor` observes the door for safety violations. Five reactive classes, instance priorities on four of them.

## Provenance

- **Original source:** `examples.zip:ReLico-main/AircraftDoor/AircraftDoor.rebeca`, 110 lines, one of the paper's RQ1 verification benchmarks.
- **Original blocker:** `translation failed: message server `KeepAlive`.`kick` takes no parameters, so the port that would carry it has no payload`.
- **Adaptation:** exactly one — the marker parameter. `kick()` gains `int unit` and its single send site passes `0`; no server body reads it, so no behaviour changes. See [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`.

## Keep-alive

The `KeepAlive` heartbeat recurs on a 1000-time-unit delayed self-send with a single bounded state variable, so logical time advances and the runtime terminates within its budget.
