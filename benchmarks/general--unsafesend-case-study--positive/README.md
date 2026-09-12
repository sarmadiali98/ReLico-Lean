# `general--unsafesend-case-study--positive`

A **general**-family positive benchmark: the paper's RQ1 UnsafeSend model — the unsafe counterpart of SafeSend. The `Client` sends the value `0` to the `Server`, which takes the error path and reports to the `Checker`, whose violation latch then fires: the unsafe scenario playing out to its expected observable end state. Four reactive classes, a `KeepAlive` heartbeat on a 100-time-unit loop.

## Provenance

- **Original source:** `examples.zip:ReLico-main/UnsafeSend/UnsafeSend.rebeca`, 87 lines, one of the paper's RQ1 verification benchmarks (the deliberately unsafe member of the SafeSend/UnsafeSend pair).
- **Original blocker:** the parameterless external-send target `Checker.errorIn` (its LF port would carry no value).
- **Adaptation:** exactly one — the marker parameter. `errorIn()` gains `int unit` and its single send site passes `0`; no server body reads it. See [`ADAPTATION.md`](ADAPTATION.md).

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed` — the violation latch firing is the model's designed observable outcome, not a safety failure.

## Keep-alive

The `KeepAlive` heartbeat recurs on a 100-time-unit delayed self-send; the send/error/latch chain resolves on 10- and 1-time-unit delays. Logical time advances and the runtime terminates within its budget.

## Semantic property

The benchmark-local RMC safety assertion is intentionally expected to be false. Its counterexample
witnesses the error path setting `chk.violation`; this is the benchmark's documented outcome.
