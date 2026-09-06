# `multi-store--finite-execution--positive`

A **multi-store**-family positive benchmark for finite execution: a three-step cycle, so any bounded window is a finite execution that repeats exactly.

## Provenance

### 1. Original purpose

This row carries the multi-store family's evidence: 29 obligations across `DetailedFiniteWeakExecution`, `DetailedInitialFiniteWeakExecution`, `DetailedInvariantCarryingFiniteWeakExecution`, `DirectLFDetailedFiniteWeakExecution`.

### 2. Removed features and semantic changes

None. A purpose-written single-class source inside the multi-store fragment: one actor, multiple message servers, a finite store, no message parameters and no external sends.

### 3. Preserved behavioural property

The model walks a three-step cycle of distinct dispatches, each delayed by one period, so every bounded window of observation is a finite execution, and the next window repeats the same three steps in the same order.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 29 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
