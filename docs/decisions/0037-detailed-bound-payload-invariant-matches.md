# Detailed bound-payload invariant-carrying phase matches

Status: accepted

Date: 2026-07-27

## Context

The runtime-level bound-payload invariant establishes:

- strictly positive delays for internal source self-sends;
- zero microsteps for queued generated-LF internal actions;
- a disjunction between a zero current microstep and a strictly future queue;
- automatic source-to-target dispatch compatibility;
- preservation across matched statement and dispatch transitions.

The detailed semantics introduces administrative phases around runtime dispatch.
The runtime invariant must therefore be lifted from concrete runtime states to
phase-indexed detailed states.

## Source phase invariant

`DetailedBoundPayloadSourceRuntimeInvariant` inspects the concrete source state
represented by each detailed phase.

For `stable`, it requires timing well-formedness of the stored active body.

For `dispatchReady`, it requires timing well-formedness of the embedded
post-dispatch active body. Dispatch has already removed the selected occurrence
and loaded the payload message-server body.

## Target phase invariant

`DetailedBoundPayloadTargetRuntimeInvariant` inspects the concrete target
runtime state represented by each detailed phase.

For `stable`, it requires the runtime invariant of the stored LF state.

For both `afterTime` and `dispatchReady`, it requires the runtime invariant of
the same embedded post-dispatch LF state.

Target `dispatchReady` is not rejected. A zero-delay external invocation can
legitimately dispatch to a positive microstep and pass through this phase before
consumption.

## Forward canonical phase alignment

Runtime invariance alone does not determine whether a corresponding detailed
phase is suitable as the endpoint of recursive forward execution.

`DetailedBoundPayloadStateCorresponds.sameTimeMicrostepAhead` permits a stable
source state to correspond to a target `dispatchReady` state. This relation is
necessary for backward simulation of LF's internal same-time microstep.

It is not a valid recursive forward endpoint. At that phase, generated LF has
already committed to a selected occurrence while the stable source has not yet
made its next dispatch choice.

`DetailedBoundPayloadForwardCanonicalPhase` therefore admits only:

- source `stable` with target `stable`;
- source `dispatchReady` with target `afterTime`;
- source `dispatchReady` with target `dispatchReady`.

It excludes source `stable` with target `dispatchReady`.

## Automatic forward phase compatibility

`detailedBoundPayloadForwardPhaseCompatible_of_canonicalRuntimeInvariant`
derives the existing forward compatibility predicate from:

- one exact source detailed step;
- detailed state correspondence;
- the target phase runtime invariant;
- forward canonical phase alignment.

For source time advancement and same-time consumption, stable state
correspondence exposes concrete runtime correspondence. The target invariant
then invokes the runtime-level automatic dispatch-compatibility theorem.

The remaining canonical phase combinations require no scheduler premise.

## Premise-free backward phase compatibility

`detailedBoundPayloadBackwardPhaseCompatible_of_correspondence` derives the
existing backward compatibility predicate from:

- one exact target detailed step;
- detailed state correspondence.

Backward matching intentionally retains the same-time stable-source,
dispatch-ready-target combination because it represents LF's administrative
microstep while the source stutters.

## Phase weak-match wrappers

`detailedBoundPayloadForwardMatch_of_canonicalRuntimeInvariant` invokes the
existing detailed phase weak bisimulation after deriving forward
compatibility automatically.

`detailedBoundPayloadBackwardMatch_of_correspondence` invokes the existing
backward phase weak bisimulation after deriving backward compatibility
automatically.

These wrappers eliminate external per-step compatibility premises at the
phase-matching boundary.

## Scope

This checkpoint defines phase-aware invariants, canonical forward phase
alignment, and automatic one-step weak matches.

It does not yet prove that the endpoints extracted from every weak match carry
the phase invariants and canonical alignment required for recursive finite
forward execution. That invariant-carrying endpoint package is the next
checkpoint.
