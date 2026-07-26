# Detailed phase-indexed weak bisimulation

Status: accepted

Date: 2026-07-26

## Purpose

This checkpoint packages the proved detailed forward and backward
weak-simulation obligations into one phase-indexed interface.

## Interface design

`ConcreteDetailedPhaseWeakBisimulation` contains thirteen fields:

- five forward phase obligations;
- eight backward phase obligations.

Every state, label, dispatch witness, and reaction witness is explicitly bound
in the field type. This avoids hiding phase data behind implicit elaboration.

## Forward obligations

The interface includes matching for:

- statement execution;
- future metric-time advancement;
- consumption while LF is in `afterTime`;
- consumption while both sides are dispatch-ready;
- same-time consumption from stable states.

The two stable-state dispatch cases retain
`StoreForwardDispatchCompatible`.

## Backward obligations

The interface includes reconstruction for:

- statement execution;
- future metric-time advancement;
- future LF microstep advancement;
- same-time LF microstep advancement;
- consumption from `afterTime` at microstep zero;
- consumption from future dispatch-ready states;
- consumption from same-time dispatch-ready states;
- direct stable-state `consumeNow`.

Statement reconstruction retains
`DTR.Body.MultiStoreWellFormed`.

Stable-state dispatch reconstruction retains
`LF.StoreState.PendingMicrostepsZero`.

## Result

`concreteDetailed_phaseWeakBisimulation` constructs the interface from the H2E
and H2F theorem families.

For each represented phase transition:

- the other semantic layer admits a weak matching transition;
- the detailed labels correspond;
- the resulting states satisfy
  `ConcreteDetailedStateCorresponds`.

LF-only microstep advancement is matched by DTR weak internal stuttering.

## Deliberate limitation

This is a complete phase-indexed interface, not an unconditional global
coinductive bisimulation theorem.

The interface does not establish that the scheduler compatibility,
well-formedness, and zero-microstep premises automatically hold for every
arbitrary related state.

## Semantic boundary

The interface remains specialized to:

```text
DTR.StoreState
LF.StoreState

Payload-aware and parameter-bound machines are outside this checkpoint.

Priority boundary

This result does not remove restrictions concerning:

priority-sensitive zero-delay scheduling;
equal-priority ties;
actor-level priorities;
global priorities.
Next checkpoint

The next checkpoint derives finite observable-execution correspondence using
observable label projection. Raw detailed label lists cannot be equated
because LF microstep advancement is internal and has no visible DTR
counterpart.
