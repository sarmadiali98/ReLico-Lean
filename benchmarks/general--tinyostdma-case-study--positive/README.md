# `general--tinyostdma-case-study--positive`

A **general**-family positive benchmark: the paper-named TinyOSPV6-TDMA sensing node. A `Sensor` samples periodically, the `CPU` handles sensor and misc events, and a `CommunicationDevice` transmits through a shared `WirelessMedium` with TDMA slot gating and collision handling. Five reactive classes, six instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/tinyos-prop/TinyOSPV6-TDMA.rebeca`, 253 lines.
- **Original blockers:** environment variables; rebec-typed message and state parameters; sender capture; nondeterministic first-tick delays; computed delays; `currentMessageWaitingTime`; assertions; delay statements; `byte`; compound assignment.
- **Redesign:** device tags, static tag dispatch, fixed delays, completion-coupled drivers, and a demand-driven TDMA lifecycle; see [`ADAPTATION.md`](ADAPTATION.md).

## TDMA adaptation

The autonomous constructor-started clock is removed because RMC 2.14 collapses delayed messages and the original repeated polling grows queues before medium responses stabilize state. A send starts one active-slot attempt; `checkPendingData()` remains the transmission gate. A medium result releases the sender, while a busy or failed attempt schedules one future slot after the 50-unit inactive interval. Absolute global TDMA phase is intentionally not retained while idle.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm. Source-level assertions check the observed send-while-pending latch and use an expected-`FALSE` counterexample to witness an accepted medium transmission.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`;
- the generated runtime exits successfully under the benchmark runtime stage.
