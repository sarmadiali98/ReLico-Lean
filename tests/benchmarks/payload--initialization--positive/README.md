# `payload--initialization--positive`

A **payload**-family positive benchmark for initialization.

## Provenance

### 1. Original purpose

This row carries the payload family's initialization evidence: 12 obligations across `PayloadStatementTranslation`.

### 2. Removed features and semantic changes

None. A purpose-written single-server source inside the store fragment; the v0 message server carries no parameters, so the initialized values are the store.

### 3. Preserved behavioural property

The constructor seeds two distinct values into the store, and every execution propagates the seed forward, so all later behaviour is the initialization's result.

## Stages

7 stages, terminal `lfc`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, through the `--family payload` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 12 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
