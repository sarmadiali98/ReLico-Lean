# `general--periodic-fork-composition--positive`

A **general**-family positive benchmark. General-family benchmark for a periodic fork with heterogeneous branches: per-branch payloads and stored per-worker state.

## Provenance

### 1. Original purpose

One actor fans a periodic message out to several consumers (examples2 Periodic_Fork_Composition).

### 2. Why the original fails

An uncoupled timer-driven producer overflows the model checker's queue at any bound -- the same measured defect as the other periodic compositions.

### 3. Differentiation

Its near-twin is already implemented as `general--arbitrary-rebec-ordering--positive` (a uniform fan-out with uniform acknowledgements, from the byte-similar Arbitrary_Ordering_Rebec corpus model). This source instead forks heterogeneous payloads -- round + 1, round, round - 1 -- to three workers that each store the value they received, so the branches are individually observable rather than interchangeable.

### 4. Preserved behavioural property

One producer, several consumers, one message per branch per round, producer re-armed by the last consumer's acknowledgement.

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`. This row owns no Lean obligations; its evidence is the pipeline artifacts.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- runtime observation included: every recurrence is delayed, so the runtime terminates within its budget.
