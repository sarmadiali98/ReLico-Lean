# `multi-store-payload--dispatch--positive`

A **multi-store-payload**-family positive benchmark: a rotating-slot payload dispatch: each dispatch shifts the previous payload through state and forwards it on.

## Provenance

### 1. Original purpose

This row carries the family's evidence for its capability: 124 obligations across `DetailedMultiStorePayloadSemantics`, `DetailedMultiStorePayloadWeakSemantics`, `MultiStorePayloadBackwardDispatchRuntime`, `MultiStorePayloadDetailedDispatchWeakMatches`, `MultiStorePayloadDetailedRuntimeLabelCorrespondence`, `MultiStorePayloadDispatch`, `MultiStorePayloadForwardDispatchRuntime`, `MultiStorePayloadRuntimeDispatchSupport`, `MultiStorePayloadSelectionRemoval`.

### 2. Removed features and semantic changes

None. This is a purpose-written single-class source inside the verified multi-store-payload fragment, using only constructs the fourteen implemented benchmarks of this arm already exercise: int state variables, assignments, delayed self-sends, message-server parameters and `@priority` annotations.

### 3. Preserved behavioural property

Two state variables rotate: the incoming payload is stored while the previous one is forwarded, so the dispatched value is one round behind the received one.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store-payload` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
