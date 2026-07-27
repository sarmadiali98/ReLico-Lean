# Detailed bound-payload initialization

Status: accepted

Date: 2026-07-27

## Problem

The detailed bound-payload semantics had no canonical source or generated-LF
entry states.

Finite execution correspondence therefore required callers to supply arbitrary
related states, and the development could not state an initial execution
theorem.

The current single-server payload fragment also has no enclosing model that
declares or initializes persistent state variables. The initial persistent
integer must consequently remain an explicit argument.

## Source initialization

Introduce:

- `DTR.PayloadMessageServer.initialBoundPayloadState`;
- `DTR.PayloadMessageServer.initialDetailedBoundPayloadState`.

The source runtime begins with:

- logical time `0`;
- the supplied persistent state value;
- `ParameterStore.empty`;
- no pending messages;
- no active body.

The detailed state is the stable wrapper around this idle runtime state.

## Generated-LF initialization

Introduce:

- `LF.PayloadReaction.initialBoundPayloadState`;
- `LF.PayloadReaction.initialDetailedBoundPayloadState`.

The target runtime begins with:

- `LF.initialTag`;
- the same supplied persistent state value;
- `ParameterStore.empty`;
- no pending actions;
- no active body.

The detailed state is the stable wrapper around this idle runtime state.

## Runtime-state correspondence

`boundPayloadInitialStates_correspond` proves correspondence between the
canonical source state and the canonical state of the compiled payload
reaction.

The scalar obligations are definitional:

- target logical time is source logical time;
- persistent values are equal;
- parameter stores are equal;
- target active body is the compiled source active body.

The only non-reflexive field uses `payloadQueueCorresponds_nil`.

## Detailed-state correspondence

`detailedBoundPayloadInitialStates_correspond` lifts runtime-state
correspondence through the stable constructor of
`DetailedBoundPayloadStateCorresponds`.

## Idle-state characterization

`boundPayloadInitialStates_idle` records explicitly that both initial states
contain:

- no active activation;
- no pending environmental event.

The initialization boundary is therefore quiescent.

## Scheduler base

`boundPayloadInitialTargetSchedulerBase` records:

- target logical time is zero;
- target microstep is zero;
- the target pending-action queue is empty.

These properties are intended as the base case for a later payload invocation
or environment-injection invariant.

## Architectural consequence

The idle initialization state cannot begin a nontrivial execution by itself.

Statement steps require an active body. Dispatch steps require a pending
payload-bearing occurrence. Both are absent initially.

A subsequent checkpoint must therefore define one of the following before
premise-free nontrivial execution correspondence is exposed:

1. a canonical payload invocation-entry state containing corresponding pending
   source and target occurrences; or
2. an explicit environment-injection relation that transitions the idle states
   into corresponding invocation-ready states.

## Scope

This checkpoint establishes initialization only.

It does not yet establish:

- environmental payload injection;
- invocation-entry correspondence;
- payload scheduler invariants;
- invariant-carrying chosen weak matches;
- nontrivial premise-free initial executions;
- public translator execution theorems.
