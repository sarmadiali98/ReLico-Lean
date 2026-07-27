# Detailed bound-payload end-to-end correctness

Status: accepted

Date: 2026-07-27

## Context

The invariant-carrying finite theorem requires four properties at its starting
detailed states:

1. source/target detailed-state correspondence;
2. the source timing invariant;
3. the generated-LF runtime invariant;
4. canonical forward phase alignment.

This checkpoint discharges those premises for canonical initialization and
connects external invocation entry to finite observable execution.

## Canonical idle initialization

The canonical source and target states are stable wrappers around empty runtime
states.

The source active body is empty, so its timing invariant follows from
`priorityTimingWellFormed_nil`.

The generated-LF queue is empty and the initial tag has microstep zero.
Therefore both fields of `LF.BoundPayloadState.RuntimeInvariant` hold.

`detailedBoundPayloadInitialStates_runtimeBoundary` packages:

- detailed-state correspondence;
- the source runtime invariant;
- the target runtime invariant;
- stable/stable canonical phase alignment.

`detailedBoundPayloadInitialSteps_forward` applies the invariant-carrying finite
theorem directly from this boundary.

## Positive-delay invocation-ready states

The source invocation-ready active body is empty for every external delay.

For a positive external delay, the singleton generated-LF invocation action is
scheduled at microstep zero. The target invocation-ready state therefore
satisfies the generated-LF runtime invariant.

`detailedBoundPayloadInvocationStates_runtimeBoundary_of_positive` packages the
four generic boundary premises.

`detailedBoundPayloadInvocationSteps_forward_of_positive` then applies the
generic finite theorem directly from the stable invocation-ready states.

## Zero-delay obstruction

A zero-delay action scheduled from `LF.initialTag` has a positive microstep.

The invocation-ready generated-LF state contains that action in its pending
queue. Consequently, its `pendingMicrostepsZero` property is false.

`detailedBoundPayloadInvocationTargetRuntimeInvariant_zero_impossible` proves
that the stable zero-delay invocation-ready target state cannot satisfy the
target runtime invariant.

This is a property of the scheduler semantics, not a proof artifact.
Therefore unrestricted external invocation cannot invoke the generic finite
theorem directly from the stable invocation-ready target state.

## Invocation prefix labels

`DetailedBoundPayloadInvocationPrefixLabels` records the exact source prefix
needed to cross the external invocation boundary:

- zero delay: one `consume` label;
- positive delay: one `timeAdvance` followed by one `consume` label.

## Arbitrary-delay invocation

`detailedBoundPayloadInvocationTailSteps_forward` accepts any external delay.

Its source-tail premise begins at the stable state obtained after the singleton
invocation has been dispatched and consumed.

### Zero delay

The source performs `consumeNow`.

Generated LF performs:

1. a same-time microstep transition, treated as internal;
2. the visible invocation consumption.

These transitions are combined into one generated-LF weak visible step.

The dispatched source and target runtime states correspond. The source active
body is `server.body`; the target queue is empty. Thus the declared body timing
premise and the established dispatched-target invariant supply the recursive
invariants.

### Positive delay

The source performs:

1. `timeAdvance`;
2. `consumeReady`.

This complete source execution starts at the invocation-ready state and reaches
the stable dispatched state.

The already established positive-delay invocation theorem constructs the
corresponding generated-LF weak execution and recursively handles the tail.

## Result

The arbitrary-delay theorem constructs:

- the complete source execution from invocation entry;
- the generated-LF finite weak execution;
- detailed weak-label trace correspondence;
- final detailed-state correspondence;
- observable trace correspondence;
- the final source runtime invariant;
- the final target runtime invariant;
- final canonical phase alignment.

The only semantic timing restriction is
`server.body.PriorityTimingWellFormed`, requiring strictly positive delays for
internal payload self-sends.

External invocation delays remain unrestricted.

No `DetailedBoundPayloadForwardStepsCompatible` premise is required.

## Scope

This checkpoint closes the single-server, parameter-aware detailed
bound-payload forward execution result from canonical initialization and
external invocation entry.

It does not claim correctness of the Java translator, generated textual LF
code, downstream LF tooling, compilation, deployment, or distributed runtime
behavior.
