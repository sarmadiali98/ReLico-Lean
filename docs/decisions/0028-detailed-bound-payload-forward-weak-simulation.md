# Detailed bound-payload forward weak simulation

Status: accepted

Date: 2026-07-27

## Problem

The detailed bound-payload semantic and correspondence layers supplied:

- exact parameter-aware transitions;
- phase-indexed state correspondence;
- weak-transition closure;
- payload-preserving detailed label correspondence.

A forward simulation theorem was still needed for every source detailed
transition.

## Forward-match package

`DetailedBoundPayloadForwardMatch` packages:

- a generated-LF detailed label;
- a generated-LF destination phase;
- a weak generated-LF transition;
- detailed label correspondence;
- detailed state correspondence at the destination.

The package is indexed by one source payload message server and its generated
LF payload reaction.

## Statement execution

A source bound-payload statement step is translated using
`boundPayloadStep_forward`.

The resulting generated-LF statement is internal at the detailed level. The
destination states preserve:

- persistent state;
- activation-local parameter bindings;
- ordered payload queues;
- translated remaining body.

## Future metric-time advancement

A compatible future source dispatch is reconstructed in generated LF using
`boundPayloadDispatch_forward_of_compatible`.

The source and target metric-time endpoints are equal through
`BoundPayloadStateCorresponds`. The visible time-advance labels therefore
correspond exactly.

The destination phase relation is `futureAfterTime`.

## Consumption after time advancement

Generated LF may consume immediately when the destination microstep is zero.

When the destination microstep is positive, generated LF first performs one
internal microstep transition. That transition forms the internal prefix of
one weak visible consumption transition.

Both cases preserve the selected payload-bearing occurrence and finish in
stable corresponding states.

## Dispatch-ready consumption

When both sides are dispatch-ready, generated LF directly performs the
corresponding visible payload-bearing consumption transition.

## Same-time dispatch

A generated-LF bound-payload dispatch preserves complete-tag order.

At equal metric time, the target microstep is therefore either:

- strictly later than the current microstep; or
- equal to the current microstep.

For a later microstep, LF first performs an internal microstep transition and
then consumes. The two transitions form one weak visible consumption match.

For an equal microstep, equality of metric time and microstep establishes
complete tag equality, allowing direct consumption.

## Payload preservation

Consumption label correspondence uses `PendingPayloadCorresponds`, preserving:

- translated action name;
- logical arrival time;
- the complete ordered payload.

The dispatch witness additionally preserves the resulting activation-local
parameter store.

## Forward compatibility

Forward dispatch remains conditional on
`BoundPayloadForwardDispatchCompatible`.

This premise supplies the target occurrence, residual queue correspondence,
LF earliest-selection evidence, and target not-in-the-past evidence.

## Scope

This checkpoint proves single-server detailed forward weak matches. It does
not yet prove:

- backward detailed weak matches;
- a combined phase weak bisimulation;
- finite weak-execution correspondence;
- observable-trace correspondence;
- initial-state or public translator packaging;
- multiple payload message servers.
