# Phase 4D1 Source-Semantics Implementation Contract

## Exact selector interface

The production source dispatch relation is:

`Relico.DTR.GlobalMultiStorePayloadDispatch.Step`

Its actor selector is:

`actorName : ActorName`

It is not a numeric actor index.

The relation is parameterized by the global model and selected actor name, then
relates:

- the global state before dispatch;
- the selected pending message;
- the selected payload message server;
- the global state after dispatch.

## Existing dispatch constructor

`Step.lift` performs the existing chosen-actor transition.

Its premises establish:

1. lookup of the selected actor model by `actorName`;
2. lookup of the selected actor state by `actorName`;
3. the existing local payload dispatch;
4. synchronized replacement of that actor's local state in the global state.

This relation must remain unchanged.

## Phase 4D1B module

Create:

`Relico/DTR/GlobalMultiStorePayloadActorPriority.lean`

Namespace:

`Relico.DTR.GlobalMultiStorePayloadActorPriority`

Import:

`Relico.DTR.GlobalMultiStorePayloadDispatch`

## Required source semantics

The module must define:

- `ActorPriorityAssignment`;
- `ActorPriorityRequest`;
- `ReadyActor`;
- `lookupPriority`;
- `requestCoversReadyActors`;
- `simultaneouslyReady`;
- `actorPriorityEligible`;
- `eligibleActorNames`;
- `ActorPriorityDispatchStep`.

## Wrapper relation

`ActorPriorityDispatchStep` must require both:

1. `actorName` is eligible under the actor-priority request and ready set;
2. `GlobalMultiStorePayloadDispatch.Step model actorName ...` performs the
   actual transition.

The new layer constrains actor selection. It does not duplicate or redefine
the state transition.

## Priority policy

Lower natural numbers denote higher actor priority.

All actors tied at the minimum priority remain eligible.

An absent actor-priority request imposes no additional filtering.

An incomplete assignment disables priority filtering for that ready set rather
than silently excluding uncovered actors.

Actors at different logical times are not compared by the simultaneous
actor-priority layer.

## Required tests

Phase 4D1B must mechanically test:

1. base priorities select `workera`;
2. reversed priorities select `workerb`;
3. tied priorities retain both actors;
4. absent priorities retain both actors;
5. incomplete assignment retains uncovered actors;
6. non-simultaneous actors are not priority-compared;
7. an actor absent from the ready set is ineligible;
8. an eligible actor can wrap an existing `Step`;
9. the wrapper exposes its eligibility premise;
10. the wrapper exposes its existing-dispatch premise.

## Non-regression constraints

Do not modify:

- `Relico/DTR/GlobalMultiStorePayload.lean`;
- `Relico/DTR/GlobalMultiStorePayloadDispatch.lean`;
- existing dispatch theorems;
- LF semantics;
- translation;
- correctness theorems;
- frontend behavior;
- benchmark registry.

## Conclusion status

**CONCLUSION_2_REACHED**

Actor-ordering information is necessary when actor priority changes
cross-actor selection.

Production integration remains incomplete.

## Next phase

**phase4d1b-source-global-actor-priority-semantics-implementation**
