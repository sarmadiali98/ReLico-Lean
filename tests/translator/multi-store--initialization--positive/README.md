# `multi-store--initialization--positive`

A **multi-store**-family positive benchmark for initialization: the constructor establishes a three-variable store that the message servers then rotate.

## Provenance

### 1. Original purpose

This row carries the multi-store family's evidence: 12 obligations across `MultiStoreExecutableTranslation`, `MultiStoreInitialization`.

### 2. Removed features and semantic changes

None. A purpose-written single-class source inside the multi-store fragment: one actor, multiple message servers, a finite store, no message parameters and no external sends.

### 3. Preserved behavioural property

The constructor writes three distinct values into the store, and the two servers rotate the store through those values, so every later step reads the initialization's result.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 12 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
