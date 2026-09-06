# `multi-store--weak-semantics--positive`

A **multi-store**-family positive benchmark for weak semantics: a chain of state-only steps, all internal, which the observable projection quotients away.

## Provenance

### 1. Original purpose

This row carries the multi-store family's evidence: 37 obligations across `DetailedObservableWeakExecution`, `DetailedPhaseWeakBisimulation`, `DetailedWeakSemantics`, `DirectLFDetailedForwardWeakSimulation`, `DirectLFDetailedObservableWeakExecution`.

### 2. Removed features and semantic changes

None. A purpose-written single-class source inside the multi-store fragment: one actor, multiple message servers, a finite store, no message parameters and no external sends.

### 3. Preserved behavioural property

Every message server only writes the store and chains to the next server, so each step is a tau step invisible to any observer; the observable projection of the whole three-step cycle collapses to a single stutter, which is exactly the material the family's weak-semantics evidence reasons about.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 37 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
