# `multi-store--well-formedness--positive`

A **multi-store**-family positive benchmark for well-formedness: a ranked two-server chain, exercising the structural surface the well-formedness predicate checks.

## Provenance

### 1. Original purpose

This row carries the multi-store family's evidence: 25 obligations across `DirectLFStatementBackward`, `MultiStoreModelTranslation`.

### 2. Removed features and semantic changes

None. A purpose-written single-class source inside the multi-store fragment: one actor, multiple message servers, a finite store, no message parameters and no external sends.

### 3. Preserved behavioural property

Two message servers carry distinct declared priorities and hand off in a chain, so the model exercises every structural obligation the family's well-formedness and translation-correctness evidence is about: multiple ranked servers, a finite store, and a single actor holding them.

## Stages

8 stages, terminal `lfc`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, through the `--family multi-store` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 25 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
