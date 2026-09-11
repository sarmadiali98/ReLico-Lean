# `payload--priority-selection--positive`

A **payload**-family positive benchmark for priority selection.

## Provenance

### 1. Original purpose

This row carries the payload family's selection evidence: 28 obligations across `DirectLFPayloadSelectionCompatibility`, `DirectLFPayloadSelectionRemoval` -- the LF-side selection compatibility and selection removal theorems for the single reaction.

### 2. Removed features and semantic changes

One, forced by a measured boundary: the finite-store parser bridge refuses message-server annotations, so the annotated-server draft was refused and the source carries the unannotated server -- the only shape this fragment admits. Under the fragment's ordering rule an unannotated server is ordered after every explicitly prioritized server, and with exactly one server the selection is unambiguous; the priority-selection surface at this family's width is that rule, and the LF-side selection theorems carry the evidence.

### 3. Preserved behavioural property

The single server recurs on a one-period delay and writes the store, so every execution is a selection of the one reaction, dispatched and executed to completion, with the selection's LF-side ordering pinned by the family's compatibility and removal theorems.

## Stages

8 stages, terminal `lfc`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, through the `--family payload` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 28 obligations;
- the recurrence is delayed by one period, so the runtime terminates within its budget.
