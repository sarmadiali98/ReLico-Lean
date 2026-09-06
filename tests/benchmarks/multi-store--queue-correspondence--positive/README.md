# `multi-store--queue-correspondence--positive`

A **multi-store**-family positive benchmark for queue correspondence: three staggered servers keep up to three self-messages pending at once, so the queue's contents are the property.

## Provenance

### 1. Original purpose

This row carries the multi-store family's evidence: 26 obligations across `DirectLFStatementForward`, `MultiStoreSemantics`.

### 2. Removed features and semantic changes

None. A purpose-written single-class source inside the multi-store fragment: one actor, multiple message servers, a finite store, no message parameters and no external sends.

### 3. Preserved behavioural property

The constructor arms three servers at staggered times and each recurs on the same period, so the queue holds up to three pending self-messages in steady state, each addressed to a different server, and the correspondence between what is queued and what executes is observable in the three store variables.

## Stages

8 stages, terminal `lfc`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, through the `--family multi-store` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 26 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
