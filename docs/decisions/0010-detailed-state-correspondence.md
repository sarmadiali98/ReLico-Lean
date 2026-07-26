# Detailed cross-language state correspondence

Status: accepted

Date: 2026-07-26

## Purpose

The detailed DTR and generated-LF semantics contain intermediate states that
do not exist in the executable macro semantics.

Weak simulation therefore requires a phase-aware state relation rather than
only a relation between stable runtime states.

## Parameterized relations

The detailed relation is parameterized by three existing proof obligations:

- correspondence between stable DTR and LF runtime states;
- correspondence between a pending DTR message and pending LF action;
- correspondence between a DTR message server and generated LF reaction.

This separates the weak-semantics structure from the concrete translation
lemmas.

Subsequent checkpoints instantiate these parameters with the existing store,
queue, payload, parameter, priority, and executable-translation
correspondence predicates.

## Dispatch witness

`DetailedDispatchWitnessCorresponds` records:

- correspondence of the states before dispatch;
- correspondence of the selected pending occurrences;
- correspondence of the selected handlers;
- correspondence of the states after dispatch.

The DTR and LF intermediate-state constructors independently retain their
macro-dispatch witnesses.

## Stable states

A stable detailed DTR state corresponds to a stable detailed LF state exactly
when the supplied stable-state relation holds.

No intermediate phase corresponds to two stable states.

## Future dispatch

After matching observable metric-time transitions:

```text
DTR dispatchReady
LF  afterTime

These states correspond through the futureAfterTime constructor.

When the LF destination has a positive microstep, LF performs an internal
microstep transition:

DTR dispatchReady
LF  dispatchReady

These states correspond through the futureReady constructor.

The DTR side stutters during that internal LF transition.

Same-time later-microstep dispatch

For a same-metric-time LF dispatch to a later microstep, LF first performs an
internal microstep transition while DTR has not yet consumed its message:

DTR stable
LF  dispatchReady

These states correspond through sameTimeMicrostepAhead.

The next visible consumption or reaction-firing transition returns both sides
to corresponding stable post-dispatch states.

Scope

This checkpoint defines the invariant required for weak simulation.

It does not yet prove:

forward weak simulation;
backward weak simulation;
weak bisimulation;
observable trace preservation;
execution-space preservation.

The positive-delay restriction for priority-sensitive correspondence remains
unchanged.

The zero-delay priority counterexample remains outside the unrestricted
verified fragment.

Actor-level priority, global priority, and unrestricted equal-priority ties
remain outside scope.

Next checkpoint

The next checkpoint instantiates the parameterized stable, pending-event, and
handler relations with the existing executable translation correspondence
predicates.

It then proves preservation of the detailed relation across internal
statement and LF microstep transitions.
