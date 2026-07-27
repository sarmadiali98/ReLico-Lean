# Detailed bound-payload runtime-invariant preservation

Status: accepted

Date: 2026-07-27

## Context

The preceding checkpoint introduced:

- a strictly positive delay restriction for internal parameter-aware self-sends;
- a generated-LF runtime invariant requiring zero-microstep queued actions;
- a disjunction covering either a zero current microstep or a strictly future
  pending queue;
- automatic forward-dispatch compatibility.

Recursive weak-execution correctness additionally requires these properties to
survive every matched runtime transition.

## Source statement preservation

A source bound-payload statement state has an active body whose head is the
executing self-send.

`boundPayloadStep_preserves_priorityTimingWellFormed` proves that one statement
step preserves timing well-formedness by retaining the well-formed body tail.

## Compiled schedule positivity

`compiledBoundPayloadScheduleHead_positive` extracts the delay from the head of
a compiled LF bound-payload body.

Executable body translation preserves the source self-send delay exactly.
Therefore, source body timing well-formedness proves that the generated LF
schedule delay is strictly positive.

## Target statement preservation

`targetBoundPayloadStep_preserves_runtimeInvariant` proves preservation across
one generated payload scheduling step.

For the pending queue:

- existing actions retain microstep zero;
- the newly appended positive-delay action has microstep zero.

For the disjunctive current-tag condition:

- statement execution leaves the current tag unchanged;
- if its microstep was zero, the first disjunct remains true;
- otherwise all existing actions were strictly future, and the new
  positive-delay action is also strictly future.

## Target dispatch preservation

`targetBoundPayloadDispatch_preserves_runtimeInvariant` proves preservation
across generated payload dispatch.

Occurrence removal preserves zero microsteps in the residual queue.

The selected action belonged to the original queue and therefore had
microstep zero. Dispatch changes the current tag to that selected action tag,
so the post-dispatch state satisfies the zero-current-microstep disjunct.

## Source dispatch timing

Source dispatch replaces the empty active body with the declared payload
server body.

`boundPayloadDispatch_establishes_priorityTimingWellFormed` therefore requires
the declared server body itself to satisfy the positive-delay timing
restriction. Under that assumption, the post-dispatch active body is timing
well formed.

## Matched statement package

`boundPayloadStep_forward_preserves_runtimeInvariants` combines:

- existing forward correctness for one payload statement;
- label correspondence;
- state correspondence;
- source timing preservation;
- target runtime-invariant preservation.

Its result contains all data required for the next recursive match.

## Matched dispatch package

`boundPayloadDispatch_forward_preserves_runtimeInvariants` combines:

- automatic scheduler compatibility from the target runtime invariant;
- existing conditional forward dispatch correctness;
- selected payload occurrence correspondence;
- post-dispatch state correspondence;
- source server-body timing;
- target runtime-invariant preservation.

This eliminates the external dispatch-compatibility premise for invariant
states.

## Scope

This checkpoint establishes runtime-level preservation for exact source/target
statement and dispatch transitions.

It does not yet define phase-aware invariants for detailed bound-payload states
or construct invariant-carrying weak matches and finite executions. Those
results belong to the next checkpoint.
