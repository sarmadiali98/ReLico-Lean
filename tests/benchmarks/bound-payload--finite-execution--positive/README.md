# `bound-payload--finite-execution--positive`

## Purpose

This benchmark records finite-step and finite-trace formal evidence for the
bound-payload execution route, together with a bounded runtime observation of
the corresponding recurring translated program.

## Source behavior

The source sends the positive payload `1` after one logical time unit. The
`dispatch` message server stores the received payload and schedules the same
payload again after one logical time unit.

The source is intentionally recurring. It is not a self-termination example.

## Evidence route

The required stages are:

1. source;
2. RMC;
3. parser JSON;
4. decoded DTR AST;
5. formal witness;
6. translated LF AST;
7. LF source;
8. LFC;
9. runtime.

RMC checks `Deadlock-Freedom and No Deadline Missed` and records
`result = "satisfied"`.

The formal-witness stage covers 44 accepted obligations across three Lean
modules. Every coverage entry includes the canonical
`original_benchmark_candidate`, `final_benchmark_id`, and `mapping_status`
fields.

Runtime executes with:

```text
--timeout 5 msec --fast
```

This is a bounded logical-time observation. It is not a direct no-timeout run.

## Claim boundary

Supported:

- finite-step or finite-trace formal execution evidence;
- positive payload binding within the observed execution prefix;
- successful bounded runtime observation.

Not claimed:

- source self-termination;
- universal program termination;
- general scheduler liveness;
- priority selection;
- actor-priority semantics.

No new frontend syntax, actor-priority implementation, Java change, or exporter
change is required.
