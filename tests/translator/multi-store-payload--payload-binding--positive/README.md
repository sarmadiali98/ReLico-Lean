# `multi-store-payload--payload-binding--positive`

A **multi-store-payload**-family positive benchmark: a two-server payload relay: ping binds the payload into one variable and chains to pong, which binds it into the other.

## Provenance

### 1. Original purpose

This row carries the family's evidence for its capability: 128 obligations across `MultiStorePayloadCppBackend`, `MultiStorePayloadDetailedInvocationFiniteObservable`, `MultiStorePayloadDetailedObservableWeakExecution`, `MultiStorePayloadDetailedRuntimePhaseWeakBisimulation`, `MultiStorePayloadDetailedStatementBackwardWeakMatch`, `MultiStorePayloadDetailedStatementForwardWeakMatch`, `MultiStorePayloadFrontend`, `MultiStorePayloadSemantics`.

### 2. Removed features and semantic changes

None. This is a purpose-written single-class source inside the verified multi-store-payload fragment, using only constructs the fourteen implemented benchmarks of this arm already exercise: int state variables, assignments, delayed self-sends, message-server parameters and `@priority` annotations.

### 3. Preserved behavioural property

The payload alternates between two message servers, each binding it into its own state variable before handing it back.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store-payload` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
