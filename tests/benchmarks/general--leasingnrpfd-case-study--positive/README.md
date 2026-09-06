# `general--leasingnrpfd-case-study--positive`

A **general**-family positive case-study benchmark: the LeasingNRPFD
leasing-NRP failover protocol — two data-center networks (`DCN1`,
`DCN2`), six switches in relay chains, primary-election by ping
round-trips, heartbeat monitoring, and scheduled switch failure at
t = 2500.

Case-study rows own no Lean obligations; their evidence is the pipeline
artifacts themselves.

## Provenance

- **Original source:**
  `examples.zip:ReLico-main/LeasingNRPFD/LeasingNRPFD.rebeca`, 359 lines.
- **Original blocker:** `unsupported by the ReLico general parser
  bridge: environment variable`.
- **Adaptations:** the approved category-1 mechanical set (env fold,
  array flattening, byte widening, self-send qualification, operator and
  statement rewrites the pipeline itself names: R16, D5, switch→if) plus
  the **approved category-2 transformation** — the constructor-assigned
  rebec-typed routing variables replaced by knownrebec bindings, with
  the exact proof obligation documented. The complete before/after
  record, including every intermediate measured refusal (A1, A2, R14,
  R16, D5, D9, the `mode`/`nodeMode` target-keyword collision) is in
  [`ADAPTATION.md`](ADAPTATION.md); the ruling evidence for the
  transformation is in
  [`ROUTING-COMPARISON.md`](ROUTING-COMPARISON.md).

## Stages

7 stages, terminal `runtime`: `source`, `parser-json`,
`decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`,
through the `--family general` arm. The `rmc` stage is deliberately
absent: the model checker reports `queue overflow` on this model (the
unfair-interleaving accumulation shape; see `ADAPTATION.md`), and
case-study rows record model-checker verdicts as bonuses rather than
gates, per the tier-2 policy.

## Evidence

- every pipeline stage exits 0;
- the generated LF compiles under `lfc 0.11.0` and the binary runs
  within its budget;
- RMC verdict recorded in `ADAPTATION.md` and `RESULTS.md`.

## Keep-alive

`runMe` recurs on a 1000-time-unit self-delay and the heartbeat flows
are periodic with literal delays, so no zero-delay recurrence exists.
