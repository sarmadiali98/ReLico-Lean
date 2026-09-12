# `general--trigger-circular-composition--positive`

A **general**-family positive benchmark. General-family benchmark for a trigger-activated ring: one circulation per firing, ring at rest between rounds.

## Provenance

### 1. Original purpose

A ring of actors held quiet until a trigger fires, then circulating (examples2 Trigger_Activated_Circular_Composition).

### 2. Why the original fails

The corpus source is byte-identical to Deterministic_Circular_Ordering_Rebec, whose redesigned form is already implemented as `general--circular-rebec-ordering--positive` -- implementing the twin verbatim would be duplicate evidence.

### 3. Differentiation

This source adds a Trigger actor and changes the shape: each firing circulates the message exactly once around the ring, the last node reports the return, and only then does the Trigger re-arm -- so the ring rests between rounds instead of circulating perpetually, and arming comes from a message rather than a constructor.

### 4. Preserved behavioural property

A ring activated by a trigger, circulating its message node to node in order.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `rmc-properties`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`. Source-level assertions check observed ring order and use an expected-`FALSE` counterexample to witness one full trigger-activated circulation.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- runtime observation included: every recurrence is delayed, so the runtime terminates within its budget.
