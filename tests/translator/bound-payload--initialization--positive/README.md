# `bound-payload--initialization--positive`

## Purpose

This benchmark records constructor-initialization and invocation-entry formal
evidence for the bound-payload route, together with a bounded runtime
observation of the corresponding recurring translated program.

## Source behavior

The constructor initializes `x` to `0` and schedules `dispatch(1)` after one
logical time unit. The message server stores the received payload and schedules
the same payload again after one logical time unit.

The source is recurring. It is not a self-termination example.

## Formal scope

The formal-witness stage covers 53 accepted obligations across:

- `Relico/Tests/DetailedBoundPayloadInitialization.lean`;
- `Relico/Tests/DetailedBoundPayloadInvocationEntry.lean`.

The obligations establish the selected initialization and invocation-entry
interfaces. Registry line numbers are metadata; obligation identity is carried
by the canonical IDs and names.

## Route

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

RMC is expected to record `satisfied`.

Runtime uses:

```text
--timeout 5 msec --fast
```

This is a bounded logical-time observation.

## Claim boundary

Supported:

- constructor-initialization formal evidence;
- invocation-entry formal evidence;
- positive initial payload within the observed execution prefix;
- successful bounded runtime observation.

Not claimed:

- source self-termination;
- universal program termination;
- general scheduler liveness;
- priority selection;
- actor-priority semantics.

No new frontend syntax, actor-priority implementation, Java change, or exporter
change is required.
