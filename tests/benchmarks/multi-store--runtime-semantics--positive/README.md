# `multi-store--runtime-semantics--positive`

A **multi-store**-family positive benchmark for runtime semantics: two servers on staggered periods, so the runtime's time-ordering of their executions is the property.

## Provenance

### 1. Original purpose

This row carries the multi-store family's evidence: 2 obligations across `DetailedInvariantMatches`.

### 2. Removed features and semantic changes

None. A purpose-written single-class source inside the multi-store fragment: one actor, multiple message servers, a finite store, no message parameters and no external sends.

### 3. Preserved behavioural property

The two servers recur on the same period but are armed at different times, so the runtime executes them in a fixed interleaving over logical time: one at every third period starting from the first, the other starting from the third.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 2 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
