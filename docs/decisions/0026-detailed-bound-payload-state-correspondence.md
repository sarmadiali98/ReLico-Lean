# Detailed bound-payload phase-state correspondence

Status: accepted

Date: 2026-07-27

## Problem

The detailed bound-payload semantic foundation introduced explicit source and
generated-LF phases, but no relation connected those phases.

Correctness proofs require a relation that preserves:

- persistent state;
- activation-local parameter environments;
- exact ordered payload queues;
- translated active bodies;
- the selected payload-bearing occurrence;
- before- and after-dispatch runtime states.

## Architectural choice

A dedicated payload-specific phase relation is introduced instead of
generalizing the ordinary detailed relation completed in Phase H.

The ordinary relation is specialized to:

- `DTR.StoreState`;
- `LF.StoreState`;
- `DTR.MessageServer`;
- `LF.Reaction`;
- ordinary multi-store dispatch witnesses.

Changing those types would unnecessarily destabilize the completed
parameterless proof chain.

## Dispatch witness correspondence

`DetailedBoundPayloadDispatchWitnessCorresponds` records:

- bound-payload state correspondence before dispatch;
- exact payload-aware correspondence of the selected source message and target
  action;
- bound-payload state correspondence after dispatch.

The surrounding detailed state indices fix the source payload message server
and its compiled generated-LF payload reaction.

## Supported phase configurations

`DetailedBoundPayloadStateCorresponds` supports four configurations.

1. Stable source and target states correspond directly.
2. After matching future metric-time transitions, the source is
   dispatch-ready while generated LF is in its after-time phase.
3. After generated LF performs any required internal microstep transition,
   both sides are dispatch-ready.
4. For same-time dispatch to a later LF microstep, the source remains stable
   while generated LF internally reaches dispatch-ready.

The fourth configuration represents weak-simulation stuttering.

## Preserved payload facts

Stable correspondence exposes:

- equality of activation-local parameter stores;
- complete ordered payload-aware queue correspondence.

The same facts are retained inside every dispatch witness through
`BoundPayloadStateCorresponds`.

## Scope

This checkpoint defines phase-state correspondence only. It does not yet prove:

- detailed label correspondence;
- forward weak matches;
- backward weak matches;
- finite detailed execution correspondence;
- initial-state or public translator theorems;
- multiple payload message servers.
