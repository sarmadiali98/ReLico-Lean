# `payload--payload-binding--positive`

A **payload**-family positive benchmark for payload binding.

## Provenance

### 1. Original purpose

This row carries the payload family's binding evidence: 55 obligations across `PayloadBinding`, `PayloadFoundation`, `PayloadQueueFoundation`, `PayloadSemantics`.

### 2. Removed features and semantic changes

None. The v0 message server carries no parameters, so this family's binding is store-to-store: the payload is bound from one store slot into another, distinct from the bound-payload family's message-carried payloads.

### 3. Preserved behavioural property

A true two-way exchange: each execution holds the left payload in a temp slot, binds the right payload into the left slot, and binds the held payload into the right slot, so both slots end up carrying the other's payload and both bindings are observable in the store.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family payload` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 55 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
