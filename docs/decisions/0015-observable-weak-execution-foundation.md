# Observable weak-execution foundation

Status: accepted

Date: 2026-07-27

## Purpose

This checkpoint introduces the finite weak-execution and observable-trace
infrastructure required to lift phase-local weak simulation to finite
execution correspondence.

## Generic weak executions

`Common.WeakSteps` is the finite reflexive-transitive sequencing relation for
`Common.WeakStep`.

Its label list records one representative label per weak transition. Internal
prefixes and suffixes embedded inside a weak transition are not duplicated in
that list.

The foundation proves:

- singleton weak execution;
- composition by label-list concatenation;
- observable projection over concatenated traces.

## Detailed semantic instances

The checkpoint defines:

- `DTR.DetailedWeakSteps`;
- `LF.DetailedWeakSteps`.

Both exact detailed finite-step relations embed into the corresponding weak
finite-step relation. Weak executions compose on both sides.

## Observable correspondence

`ConcreteDetailedObservableCorresponds` relates:

- equal metric-time advancement;
- message consumption to the generated LF action consumption at the same
  logical time.

For consumption, the target action name is
`Translation.actionNameFor sourceName`.

## Label projection

`ConcreteDetailedLabelCorresponds.observableOption` proves that every
corresponding detailed label pair has corresponding optional observable
projections.

The internal cases are:

- DTR `tau` with LF `tau`;
- DTR `tau` with LF `microstepAdvance`.

Both project to `none`.

## Trace projection

`ConcreteDetailedWeakLabelTraceCorresponds` is pointwise correspondence over
representative weak labels.

`ConcreteDetailedObservableTraceCorresponds` is pointwise correspondence over
paper-level observable events.

The main theorem proves:

```text
corresponding weak-label traces
  =>
corresponding observable projections

This deliberately compares observable projections rather than raw detailed
label lists.

Scope

This checkpoint supplies infrastructure only. It does not yet derive a finite
forward or backward execution theorem from the phase-indexed weak-bisimulation
interface.

That induction is the next checkpoint.

Semantic boundary

The detailed weak-execution layer remains specialized to:

DTR.StoreState
LF.StoreState

Payload-aware and parameter-bound detailed executions remain outside this
checkpoint.
