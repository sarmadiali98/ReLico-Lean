# Phase 4D6C Finite-Execution Correspondence

## Result

**STEP_LOCAL_FINITE_DISPATCH_CORRESPONDENCE_PRODUCTION_INSTALLED**

## Production interface

1. `ActorDispatchFrame` (structure) — Carries the step-local ready snapshot and selected ActorName.
2. `SourceActorDispatchEvent` (structure) — Retains the selected source pending message and message server.
3. `TargetActorDispatchEvent` (structure) — Retains the selected target action and reaction.
4. `ActorDispatchEventCorresponds` (structure) — Pairs compiled reactions with pending-payload correspondence.
5. `ActorDispatchEventTraceCorresponds` (inductive) — Defines pointwise finite occurrence-trace correspondence.
6. `SourceActorPriorityDispatchSteps` (inductive) — Defines finite source actor-priority dispatch closure.
7. `TargetActorOrderDispatchSteps` (inductive) — Defines finite target actor-order dispatch closure.
8. `sourceActorPriorityDispatchSteps_single` (theorem) — Embeds one source dispatch into a finite run.
9. `targetActorOrderDispatchSteps_single` (theorem) — Embeds one target dispatch into a finite run.
10. `sourceActorPriorityDispatchSteps_forward` (theorem) — Proves forward finite dispatch correspondence.
11. `targetActorOrderDispatchSteps_backward` (theorem) — Proves backward finite dispatch correspondence.
12. `actorDispatchEventTraceCorresponds_length_eq` (theorem) — Proves corresponding occurrence traces have equal lengths.

## Established semantics

- The actor-priority request is fixed for one finite run.
- Every transition carries its own ready-actor snapshot.
- Every transition retains its selected `ActorName`.
- The target compiles each ready snapshot separately.
- No fixed ready list is reused across an arbitrary execution.
- Forward and backward finite one-for-one dispatch correspondence are proved.
- Selected-message/action occurrences correspond pointwise.
- Corresponding occurrence traces have equal lengths.

## Validation

- Production structures: **4/4**
- Production inductive relations: **3/3**
- Production theorems: **5/5**
- Exported API regression checks: **12/12**
- Full `lake build`: **474 jobs passed**
- `sorryAx`: **absent**
- Original repository mutation: **none**
- Staging, commit, and push: **none**

The correspondence theorems depend only on Lean's standard `propext` and
`Quot.sound` axioms where inherited from the one-step theorem stack.

## Remaining Phase 4D6 boundary

This module proves strong finite closure for actor dispatch. It does not yet
identify or prove the weak/observable execution layer that may include
statement steps, time advancement, microsteps, or observation projection.

## Progress

- Before: **78%**
- After: **82%**
- Remaining: **18%**

## Next phase

**phase4d6d-observable-and-weak-execution-interface-audit**
