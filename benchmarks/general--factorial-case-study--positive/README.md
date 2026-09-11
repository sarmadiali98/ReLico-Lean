# `general--factorial-case-study--positive`

A **general**-family positive benchmark: the paper's RQ1 Factorial model — a `Source` starts a `FactorialCore` and a `KeepAlive` heartbeat, the core computes 4! on a 10-time-unit delay and reports to a `Checker`, which raises a violation if the result is not 24. Four reactive classes, instance priorities on three of them.

## Provenance

- **Original source:** `examples.zip:ReLico-main/Factorial/Factorial.rebeca`, 84 lines, one of the paper's RQ1 verification benchmarks.
- **Original blocker:** the parameterless external-send target `KeepAlive.kick` (its LF port would carry no value).
- **Adaptation:** exactly one — the marker parameter. `kick()` gains `int unit` and its single send site passes `0`; no server body reads it. See [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`.

## Keep-alive

The `KeepAlive` heartbeat recurs on a 100-time-unit delayed self-send with one bounded state variable, so logical time advances and the runtime terminates within its budget.
