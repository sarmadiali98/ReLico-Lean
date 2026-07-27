# Detailed bound-payload backward weak simulation

Status: accepted

Date: 2026-07-27

## Problem

The detailed bound-payload layer had forward weak simulation, but it did not
yet reconstruct source behavior from generated-LF detailed transitions.

Backward simulation must retain:

- exact payload-bearing occurrence correspondence;
- activation-local parameter bindings;
- stable and dispatch phase correspondence;
- generated-LF microstep administration as source stuttering.

## Backward-match package

`DetailedBoundPayloadBackwardMatch` packages:

- a source detailed label;
- a source destination phase;
- a source weak transition;
- payload-aware detailed label correspondence;
- detailed state correspondence at the destination.

## Statement execution

A generated-LF parameter-aware scheduling statement is inverted by
`boundPayloadStep_backward`.

The reconstructed source statement preserves:

- expression evaluation;
- scheduled logical time;
- payload value;
- persistent state;
- activation-local parameters;
- the remaining active body.

Both detailed labels are internal.

## Future time advancement

A generated-LF payload dispatch is reconstructed by
`boundPayloadDispatch_backward`.

Stable-state correspondence identifies both metric-time endpoints and proves
that the reconstructed source dispatch is also future.

Unlike the ordinary finite-store backward dispatch theorem, this reconstruction
requires no separate `PendingMicrostepsZero` premise.

## Microstep after future time advancement

When generated LF advances from `afterTime` to `dispatchReady`, the source is
already dispatch-ready.

The source therefore performs a reflexive weak-`tau` transition. The phase
relation changes from `futureAfterTime` to `futureReady`.

## Same-time microstep progression

A same-time LF microstep from a stable state reconstructs the corresponding
source payload dispatch.

The source does not consume yet. It stutters at the stable state while the
target moves to `dispatchReady`.

The resulting relation is `sameTimeMicrostepAhead`.

## Consumption after future time advancement

When LF consumes directly from `afterTime` at microstep zero, the source
performs `consumeReady`.

The selected source message and target action retain exact
`PendingPayloadCorresponds`.

## Future dispatch-ready consumption

When both layers are dispatch-ready after a future dispatch, source
`consumeReady` directly matches LF consumption.

## Same-time dispatch-ready consumption

In `sameTimeMicrostepAhead`, the source remains stable while LF is
dispatch-ready.

LF consumption is therefore matched by source `consumeNow`.

## Direct same-tag consumption

A direct generated-LF consumption from stable state reconstructs a source
dispatch.

Equality of complete target tags implies equality of target metric times.
State correspondence then proves equal source metric times, permitting source
`consumeNow`.

## Payload and parameter preservation

Every consumption case uses the dispatch witness’s
`PendingPayloadCorresponds`, which preserves:

- the generated action name;
- logical arrival time;
- the complete ordered payload.

The witness’s final-state correspondence also preserves the parameter store
created by binding that payload to the server’s ordered formal parameters.

## Scope

This checkpoint proves single-server detailed backward weak matches. It does
not yet prove:

- the combined phase weak-bisimulation package;
- finite detailed weak-execution correspondence;
- observable-trace correspondence;
- canonical initialization;
- public translator theorems;
- multiple payload message servers.
