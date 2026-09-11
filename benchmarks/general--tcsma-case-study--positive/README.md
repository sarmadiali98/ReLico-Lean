# `general--tcsma-case-study--positive`

A **general**-family positive benchmark: the paper-named TCSMA model — a `Controller` polls two stations round-robin through a broadcast `Medium`, the polled station's data returns through the same medium to the other station. Four reactive classes (Controller, Medium, two Interface/User pairs), seven message servers.

## Provenance

- **Original source:** `examples.zip:ReLico-main/benchmarks/tcsma.rebeca`, 215 lines, the paper-named TCSMA model (which the paper derives from the Rebeca examples for its generator suite).
- **Original blockers:** translation refused on the parameterless external-send targets `User.sendData` and `Interface.getAckFromUser`; the model checker reported `queue overflow` on the unmodified model.
- **Adaptations:** two marker parameters; poll gating on round completion; removal of the never-read bookkeeping layer. All three are measured and documented in [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`.

## Keep-alive

The poll cycle recurs forever (one round in flight, re-armed after round completion), so the model never terminates while every queue stays bounded.
