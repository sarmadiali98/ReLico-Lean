# `multi-store--priority-selection--positive`

A **multi-store**-family positive benchmark for priority selection: two ranked message servers enabled together, so declared priority decides which runs first.

## Provenance

### 1. Original purpose

This row carries the multi-store family's evidence: 72 obligations across `DetailedExecutableTranslation`, `DetailedInvariantCarryingBackwardMatch`, `DetailedInvariantCarryingForwardMatch`, `MessageServerPriority`, `MultiStoreCppBackend`, `MultiStoreFrontendDecoder`, `PriorityTiming`.

### 2. Removed features and semantic changes

None. A purpose-written single-class source inside the multi-store fragment: one actor, multiple message servers, a finite store, no message parameters and no external sends.

### 3. Preserved behavioural property

Both servers are armed in the same round and recur on the same period, so they are enabled together every period; the declared priorities rank their selection, and each writes to its own store variable so both selections are observable.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 72 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
