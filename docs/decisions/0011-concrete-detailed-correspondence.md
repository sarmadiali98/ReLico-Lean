# Concrete detailed-state correspondence

Status: accepted

Date: 2026-07-26

## Purpose

Decision 0010 introduced a parameterized phase-aware relation.

This checkpoint instantiates that relation with the concrete correspondence
predicates already used by the executable multi-store translation proofs.

## Concrete relations

Stable runtime states use:

```text
StoreStateCorresponds

Selected pending occurrences use:

PendingCorresponds

Selected handlers use:

targetReaction =
  Translation.compileMessageReaction sourceServer

The target detailed state space is indexed by:

Translation.compileMessageReactions messageServers

Therefore the detailed relation is directly tied to the executable translator
rather than to a separately defined abstract mapping.

Statement transitions

The checkpoint reuses:

multiStore_step_forward
multiStore_step_backward

to establish preservation of the concrete detailed relation across internal
statement execution.

Each executable statement transition is represented by a detailed tau
transition.

Backward statement reconstruction retains the established source-body
well-formedness premise.

Dispatch transitions

The checkpoint wraps:

multiStore_dispatch_forward_of_compatible
multiStore_dispatch_backward

and packages their results as concrete detailed dispatch witnesses.

Forward dispatch retains the existing scheduler compatibility premise.

Backward dispatch retains the existing requirement that pending target
microsteps are zero.

Neither condition is weakened at this checkpoint.

Internal LF microsteps

For a future dispatch with a positive destination microstep, LF advances
internally from afterTime to dispatchReady. DTR remains in its
dispatchReady phase.

For a same-metric-time dispatch to a later microstep, LF advances internally
from a stable state to dispatchReady. DTR stutters in its stable
pre-dispatch state.

Both phase changes preserve concrete detailed-state correspondence.

Observable data

A concrete dispatch witness proves:

metric-time equality before dispatch;
metric-time equality after dispatch;
generated action-name correspondence;
selected occurrence logical-time correspondence;
exact generated reaction correspondence.

These facts will drive the visible-label matching proofs.

Payload and parameter boundary

The current detailed semantics is defined over:

DTR.StoreState
LF.StoreState

Consequently, this checkpoint covers the executable finite-store,
multiple-message-server semantic layer.

The repository contains separate payload-aware relations:

PayloadStateCorresponds
BoundPayloadStateCorresponds
PendingPayloadCorresponds
PayloadQueueCorresponds

Those relations are not definitionally part of StoreStateCorresponds.

No detailed weak-bisimulation claim for payload or parameter execution is
made by this checkpoint.

Before the final paper theorem, the development must either:

generalize the detailed semantics to the bound-payload state machines; or
prove a refinement from the bound-payload machines to a generalized
detailed semantic layer.

This is now an explicit proof obligation, not an implicit claim.

Non-claims

This checkpoint does not prove:

forward weak simulation;
backward weak simulation;
weak bisimulation;
observable finite-trace equivalence;
payload-aware weak bisimulation;
unrestricted zero-delay priority preservation;
unrestricted equal-priority preservation.
Next checkpoint

The next checkpoint defines concrete correspondence between detailed visible
labels and proves forward weak simulation for internal statement steps,
observable time progression, observable consumption, and LF microstep
stuttering in the current finite-store multi-server layer.
