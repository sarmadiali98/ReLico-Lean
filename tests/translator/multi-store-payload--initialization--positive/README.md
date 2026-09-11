# `multi-store-payload--initialization--positive`

A **multi-store-payload**-family positive benchmark: a three-variable initialization and rotation cycle.

## Provenance

### 1. Original purpose

This row carries the family's evidence for its capability: 90 obligations across `MultiStorePayloadCppPrinter`, `MultiStorePayloadDetailedInitialization`, `MultiStorePayloadDetailedInvocationEntry`, `MultiStorePayloadDetailedStartupCompletion`, `MultiStorePayloadDetailedStartupEntry`.

### 2. Removed features and semantic changes

None. This is a purpose-written single-class source inside the verified multi-store-payload fragment, using only constructs the fourteen implemented benchmarks of this arm already exercise: int state variables, assignments, delayed self-sends, message-server parameters and `@priority` annotations.

### 3. Preserved behavioural property

Three state variables are initialized to distinct values in the constructor, and each step rotates them through a copy chain.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store-payload` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
