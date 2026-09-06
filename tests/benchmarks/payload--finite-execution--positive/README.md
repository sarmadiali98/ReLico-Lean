# `payload--finite-execution--positive`

A **payload**-family positive benchmark for finite execution.

## Provenance

### 1. Original purpose

This row carries the payload family's finite-execution evidence: 9 obligations across `PayloadTrace`.

### 2. Removed features and semantic changes

One, forced by a measured boundary: the finite-store parser bridge refuses conditional statements, so an earlier draft that branched on a step counter was replaced by a branchless three-variable rotation that achieves the same property -- distinct steps in a fixed order -- through store copies alone.

### 3. Preserved behavioural property

The single server rotates the store through a fixed sequence of copies each execution, so every bounded window of observation is a finite execution and the next window repeats the same steps in the same order.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family payload` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 9 obligations;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
