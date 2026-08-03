# Phase 4D2A2 Exact LF Target-Step Binding

## Result

Classification:

**EXACT_TARGET_ACTOR_NAME_STEP_BOUND_NONINVASIVE_ORDER_WRAPPER_READY**

The exact production target transition is:

`Relico.LF.GlobalMultiStorePayloadDispatch.Step`

Location:

`Relico/LF/GlobalMultiStorePayloadDispatch.lean:151-201`

## Exact actor selector

The existing LF transition selects the actor with:

`actorName : ActorName`

It does not use a numeric actor index.

This matches the source-side selector representation.

## Existing transition types

The transition uses:

- `GlobalMultiStorePayloadState`;
- `PendingAction`;
- `MultiStorePayloadReaction`;
- `ActorName`.

## Existing constructors

- `Relico.LF.GlobalMultiStorePayloadDispatch.Step.lift`

Every constructor was checked and printed through Lean.

## Phase 4D2B module

Create:

`Relico/LF/GlobalMultiStorePayloadActorOrder.lean`

Namespace:

`Relico.LF.GlobalMultiStorePayloadActorOrder`

## Wrapper architecture

The new `ActorOrderDispatchStep` must require both:

1. target actor-order eligibility for `actorName`;
2. the existing `Relico.LF.GlobalMultiStorePayloadDispatch.Step` transition.

The existing target transition remains responsible for the actual state
change.

The ordering layer only constrains which actor is permitted to take that
transition.

## Ordering representation

A literal target actor-priority field is not required.

The target must contain behaviorally equivalent ordering information that
distinguishes priority-reversed source models when their eligible actors
differ.

## Contract

| ID | Subject | Required value | Status |
|---|---|---|---|
| TB1 | existing target transition | Relico.LF.GlobalMultiStorePayloadDispatch.Step | confirmed |
| TB2 | target actor selector | actorName : ActorName | confirmed |
| TB3 | numeric actor index | not used | confirmed |
| TB4 | target state | GlobalMultiStorePayloadState | confirmed |
| TB5 | selected target event | PendingAction | confirmed |
| TB6 | selected target reaction | MultiStorePayloadReaction | confirmed |
| TB7 | new wrapper module | Relico/LF/GlobalMultiStorePayloadActorOrder.lean | planned |
| TB8 | new wrapper relation | ActorOrderDispatchStep | planned |
| TB9 | wrapper premises | target actor-order eligibility plus existing GlobalMultiStorePayloadDispatch.Step | required |
| TB10 | compatibility | existing LF Step and theorems remain unchanged | required |
| TB11 | ordering representation | behaviorally equivalent actor order; literal actor-priority field optional | required |
| TB12 | next implementation | phase4d2b-target-global-actor-order-semantics-implementation | ready |

## Non-regression requirements

Do not modify:

- `Relico/LF/GlobalMultiStorePayloadDispatch.lean`;
- existing LF dispatch theorems;
- Phase 4D1 source semantics;
- translation;
- correctness proofs;
- frontend behavior;
- benchmark registry.

## Conclusion status

**CONCLUSION_2_REACHED**

Source actor-priority semantics is complete.

The exact target transition interface is bound.

Target actor-order semantics is not yet implemented.

## Next phase

**phase4d2b-target-global-actor-order-semantics-implementation**
