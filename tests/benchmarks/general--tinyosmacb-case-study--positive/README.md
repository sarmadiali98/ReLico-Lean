# `general--tinyosmacb-case-study--positive`

A **general**-family positive benchmark: the paper-named TinyOSPV6-MACB model — a TinyOS sensing node at worst-case task lengths. A `Sensor` samples periodically (period 40), the `CPU` handles sensor and misc interrupts (task delays 2 and 10), buffers each sample into a radio packet, and a `CommunicationDevice` transmits through a shared `WirelessMedium` with collision detection. Five reactive classes, six instances.

## Provenance

- **Original source:** `examples.zip:ReLico-main/tinyos-prop/TinyOSPV6-MACB.rebeca`, 215 lines.
- **Original blockers:** environment variables (10); rebec-typed message parameters (`send`, `broadcast`, `receiveData` carry `CommunicationDevice` values); rebec-typed state variables with runtime reassignment and `null`; sender capture in the medium; nondeterministic first-tick delays; computed delays; `currentMessageWaitingTime` (a Rebeca built-in); `assertion(false)` x4; `delay` statements; `byte`; compound assignment.
- **Redesign:** the approved category-3 redesign — device tags, tag-parameterised dispatch over static bindings, latch observables, and completion-coupled drivers; per the mapping in [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`.

## Keep-alive

The sensor and misc loops recur forever, each round gated on the consumption of everything it produced (the radio round closes only when both the sender's result and the receiver's delivery ack have arrived), so every queue stays bounded while the node samples and transmits periodically.
