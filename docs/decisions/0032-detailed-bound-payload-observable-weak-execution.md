# Detailed bound-payload observable weak execution

Status: accepted

Date: 2026-07-27

## Problem

The detailed bound-payload finite weak-execution layer related representative
source and generated-LF labels pointwise and preserved final detailed states.

It did not yet expose the paper-level observable consequence of that label
correspondence.

The observable theorem must retain payload information rather than collapsing
consumption into only a name and timestamp.

## Observable correspondence

Introduce:

`DetailedBoundPayloadObservableCorresponds`.

It relates one source paper-level observable to one generated-LF paper-level
observable.

Metric-time advancement preserves both endpoints.

Payload-bearing consumption preserves:

- generated action naming;
- logical occurrence time;
- the complete ordered payload.

The consumption constructor is discharged from
`PendingPayloadCorresponds`.

## Optional observable correspondence

Introduce:

`DetailedBoundPayloadObservableOptionCorresponds`.

This relation captures projection at one label:

- source `tau` and target `tau` both project to `none`;
- source `tau` and generated-LF `microstepAdvance` both project to `none`;
- metric-time advancement projects to corresponding visible observables;
- consumption projects to corresponding payload-aware visible observables.

`DetailedBoundPayloadLabelCorresponds.observableOption` proves this property
for every corresponding detailed label.

## Observable trace correspondence

Introduce:

`DetailedBoundPayloadObservableTraceCorresponds`.

It relates finite source and generated-LF observable traces pointwise.

The relation includes:

- length equality;
- closure under trace concatenation.

## Projection theorem

`DetailedBoundPayloadWeakLabelTraceCorresponds.observableProjection` proves
that corresponding representative weak-label traces induce corresponding
paper-level observable traces.

The proof removes:

- source `tau`;
- target `tau`;
- generated-LF microstep administration.

It retains:

- metric-time advancement;
- payload-bearing consumption.

## Observable-enhanced finite execution

Introduce:

- `detailedBoundPayloadSteps_forward_observable_of_compatible`;
- `detailedBoundPayloadSteps_backward_observable_of_compatible`.

These theorems extend the finite weak-execution results with observable trace
correspondence.

They retain the existing conclusions:

- finite weak execution;
- representative weak-label correspondence;
- final detailed state correspondence.

No compatibility predicate or semantic assumption is strengthened.

## Payload guarantee

For each corresponding observable consumption event, the target event contains:

- `Translation.actionNameFor` applied to the source message name;
- the same logical arrival time;
- the same ordered payload list.

This connects the execution trace directly to the parameter values installed
during dispatch.

## Scope

This checkpoint proves conditional finite observable correspondence for one
payload message server and its generated LF payload reaction.

It does not yet prove:

- canonical initial-state correspondence;
- automatic discharge of forward execution compatibility;
- public translator execution theorems;
- multiple payload message servers;
- raw exact trace equality including internal or microstep labels.
