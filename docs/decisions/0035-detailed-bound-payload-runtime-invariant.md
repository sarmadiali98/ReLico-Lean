# Detailed bound-payload runtime invariant

Status: accepted

Date: 2026-07-27

## Problem

Parameter-aware source self-sends currently permit arbitrary delays, including
zero.

DTR orders pending messages by logical time only. Generated LF orders pending
actions by complete tags consisting of logical time and microstep.

Consequently, two source messages at the same logical time may both be
DTR-earliest while their corresponding generated actions have different
microsteps. An arbitrary fixed DTR choice is then not necessarily LF-earliest.

The conditional forward-dispatch premise cannot therefore be discharged for
every unrestricted source execution.

## Internal timing restriction

Introduce:

- `DTR.BoundPayloadStmt.PriorityTimingWellFormed`;
- `DTR.BoundPayloadBody.PriorityTimingWellFormed`.

Every parameter-aware internal self-send must have a strictly positive delay.

This restriction ensures that generated internal schedules:

- advance logical time;
- reset the scheduled action microstep to zero;
- do not create new same-time microstep refinements.

## External invocation scope

The external invocation delay remains unrestricted.

The direct invocation boundary contains only one pending occurrence. Its
scheduler compatibility is already proved directly, including the zero-delay
case.

After dispatching a zero-delay invocation, the generated current tag may have a
positive microstep. The residual pending queue is empty, so this does not create
a scheduler conflict.

## Target pending-queue properties

Introduce:

- `LF.BoundPayloadState.PendingMicrostepsZero`;
- `LF.BoundPayloadState.PendingStrictlyFuture`.

`PendingMicrostepsZero` requires every queued action to have microstep zero.

`PendingStrictlyFuture` requires every queued action to have logical time
strictly greater than the current logical time.

## Target runtime invariant

Introduce `LF.BoundPayloadState.RuntimeInvariant`.

It requires:

1. every queued action has microstep zero; and
2. either:
   - the current tag has microstep zero; or
   - every queued action is strictly later in logical time.

The second disjunct is necessary after a zero-delay external invocation.

It is weaker than requiring the current microstep always to be zero, while
remaining strong enough to establish that a selected corresponding action is
not in the generated scheduler's past.

## Scheduling facts

`boundPayloadSchedule_positive_microstepZero` proves that positive-delay
generated scheduling creates an action at microstep zero.

`boundPayloadSchedule_zero_microstepPositive` records why unrestricted
zero-delay internal sends are excluded: they create a strictly positive
microstep.

## Invocation base

`boundPayloadInvocationDispatched_targetRuntimeInvariant` proves the target
runtime invariant immediately after dispatching the canonical external
invocation.

The proof is independent of the invocation delay because the residual queue is
empty.

## Automatic forward compatibility

`boundPayloadForwardDispatchCompatible_of_runtimeInvariant` derives the
conditional forward-dispatch premise from:

- one exact source dispatch;
- payload-aware runtime-state correspondence;
- the target runtime invariant.

Payload queue correspondence transports removal and identifies the matching
generated action.

Source earliest-time selection becomes target complete-tag earliest selection
because all queued target actions have microstep zero.

The not-past obligation follows by cases:

- if the current microstep is zero, source metric-time order lifts to complete
  tag order;
- otherwise every pending action is strictly later in logical time.

## Runtime boundary package

`boundPayloadInvocation_runtimeBoundary_package` combines:

- direct singleton invocation compatibility; and
- the target runtime invariant after invocation dispatch.

This connects the external invocation boundary to the positive-delay internal
execution fragment.

## Scope

This checkpoint establishes:

- the positive-delay internal timing predicate;
- the target runtime invariant;
- the invocation base case;
- automatic forward dispatch compatibility.

It does not yet prove preservation of the invariant across:

- parameter-aware statement scheduling;
- payload dispatch;
- detailed phase transitions;
- weak matches;
- recursive finite executions.

Those preservation results belong to the next checkpoint.
