# Detailed bound-payload finite weak execution

Status: accepted

Date: 2026-07-27

## Problem

The payload-aware detailed development established phase-indexed weak
simulation for individual transitions.

Finite exact executions still needed to be lifted recursively to sequences of
weak transitions while preserving:

- representative-label correspondence;
- payload-bearing consumption events;
- phase-indexed state correspondence at every recursive boundary;
- final detailed state correspondence.

## Weak execution aliases

Introduce:

- `DTR.DetailedBoundPayloadWeakSteps`;
- `LF.DetailedBoundPayloadWeakSteps`.

Both specialize `Common.WeakSteps` to the respective detailed bound-payload
transition relation and internal-label predicate.

The representative-label sequence records one label per weak transition.
Internal prefixes and suffixes contained inside a weak transition are not
inserted into that sequence.

## Weak-label trace correspondence

Introduce:

`DetailedBoundPayloadWeakLabelTraceCorresponds`.

It relates source and target representative-label lists pointwise through
`DetailedBoundPayloadLabelCorresponds`.

The relation therefore retains:

- metric-time endpoints;
- generated-LF microstep stuttering as source `tau`;
- selected message/action occurrence correspondence;
- exact ordered payload equality.

The module also proves length equality and closure under list concatenation.

## Forward phase compatibility

`DetailedBoundPayloadForwardPhaseCompatible` admits exactly the five source
phase combinations covered by the forward phase weak-bisimulation interface.

Compatibility is trivial for:

- statement execution;
- consumption after time advancement;
- consumption from dispatch-ready.

Future and same-time dispatch from stable states retain
`BoundPayloadForwardDispatchCompatible`.

All unsupported phase combinations reduce to `False`.

## Backward phase compatibility

`DetailedBoundPayloadBackwardPhaseCompatible` admits exactly the eight target
phase combinations covered by the backward phase weak-bisimulation interface.

Every admitted backward combination is propositionally `True` beyond:

- the exact target transition;
- current detailed state correspondence.

In particular, the payload-aware backward development requires neither:

- source-body well-formedness;
- a target pending-microsteps-zero premise.

## Generic single-step lifting

The phase package gains:

- `DetailedBoundPayloadPhaseWeakBisimulation.forwardStep`;
- `DetailedBoundPayloadPhaseWeakBisimulation.backwardStep`.

These theorems eliminate the exact transition constructor and current phase,
reject unsupported combinations through the compatibility predicate, and
invoke the appropriate field of the thirteen-obligation phase interface.

## Recursive execution compatibility

Introduce:

- `DetailedBoundPayloadForwardLabelsCompatible`;
- `DetailedBoundPayloadForwardStepsCompatible`;
- `DetailedBoundPayloadBackwardLabelsCompatible`;
- `DetailedBoundPayloadBackwardStepsCompatible`.

The recursive predicates supply:

1. compatibility for the current exact transition;
2. compatibility for every corresponding weak match and resulting related
   intermediate state.

This makes the finite lifting independent of a particular existential witness
chosen by the single-step theorem.

## Finite forward lifting

`detailedBoundPayloadSteps_forward_of_compatible` converts an exact finite
source execution into a generated-LF finite weak execution.

It returns:

- generated-LF representative labels;
- a generated-LF final detailed state;
- a finite generated-LF weak execution;
- pointwise weak-label trace correspondence;
- final detailed state correspondence.

## Finite backward lifting

`detailedBoundPayloadSteps_backward_of_compatible` reconstructs a finite source
weak execution from an exact finite generated-LF execution.

It returns the symmetric package:

- source representative labels;
- a source final detailed state;
- a finite source weak execution;
- pointwise weak-label trace correspondence;
- final detailed state correspondence.

## Scope

This checkpoint does not yet prove correspondence between observable
projections of the representative-label traces.

That projection theorem is separated into the next checkpoint so the finite
execution recursion and the observable alphabet proof remain independent.

The checkpoint also does not yet establish:

- canonical initial-state correspondence;
- premise discharge from model-level invariants;
- public translator execution theorems;
- multiple payload message servers.
