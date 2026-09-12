# `general--safesend-case-study--positive`

A **general**-family positive benchmark: the paper's RQ1 SafeSend model — a `Client` sends a request to a `Server` on a 10-time-unit delay, the `Server` forwards non-zero values back to the `Client` and routes zero to an error path, and a `Checker` records violations from both the reply and the error channels. Four reactive classes, a `KeepAlive` heartbeat on a 100-time-unit loop.

## Provenance

- **Original source:** `examples.zip:ReLico-main/SafeSend/SafeSend.rebeca`, 99 lines, one of the paper's RQ1 verification benchmarks.
- **Original blocker:** the parameterless external-send target `Checker.errorIn` (its LF port would carry no value).
- **Adaptation:** exactly one — the marker parameter. `errorIn()` gains `int unit` and its single send site passes `0`; no server body reads it. See [`ADAPTATION.md`](ADAPTATION.md).

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`.

## Keep-alive

The `KeepAlive` heartbeat recurs on a 100-time-unit delayed self-send with one bounded state variable; the client/server exchange resolves on 10-time-unit delays. Logical time advances and the runtime terminates within its budget.

## Semantic property

The benchmark-local RMC assertion checks that the monitor observes neither the explicit error path
nor an invalid reply. It does not independently prove that the reply is delivered.
