# Phase 4D6F Actor-Dispatch Observable Correspondence

## Result

**ACTOR_DISPATCH_OBSERVABLE_CORRESPONDENCE_PRODUCTION_INSTALLED**

## Production interface

1. `actorDispatchFrameTrace` (definition) — Projects the selected ActorName from each step-local dispatch frame.
2. `sourceActorDispatchObservableTrace` (definition) — Defines the source actor-dispatch observable trace.
3. `targetActorDispatchObservableTrace` (definition) — Defines the target actor-dispatch observable trace.
4. `actorDispatchObservableTrace_eq` (theorem) — Proves source and target selected-actor traces are equal.
5. `sourceActorPriorityDispatchSteps_actorTrace` (theorem) — Binds a source finite execution to the shared frame projection.
6. `targetActorOrderDispatchSteps_actorTrace` (theorem) — Binds a target finite execution to the shared frame projection.
7. `sourceActorPriorityDispatchObservable_forward` (theorem) — Proves forward actor-dispatch observable correspondence.
8. `targetActorOrderDispatchObservable_backward` (theorem) — Proves backward actor-dispatch observable correspondence.

## Established result

- The selected-actor trace is the shared projection of the finite frame list.
- Source and target selected-actor traces are equal.
- Forward actor-dispatch observable correspondence is proved.
- Backward actor-dispatch observable correspondence is proved.
- Pointwise selected-message/action event correspondence is retained.
- The actor-dispatch wrapper introduces no stuttering.

## Validation

- Production definitions: **3/3**
- Production theorems: **5/5**
- Exported API checks: **8/8**
- Full `lake build`: **474 jobs passed**
- `sorryAx`: **absent**
- Original repository mutation: **none**
- Staging, commit, and push: **none**

The forward and backward observable theorems inherit only Lean's standard
`propext` and `Quot.sound` dependencies from the finite and one-step theorem
stack.

## Scope limitation

This is actor-dispatch observable trace correspondence. It is not yet full
detailed-runtime weak equivalence. Statement execution, startup, time
advancement, and microstep integration remain outside this theorem.

## Progress

- Before: **85%**
- After: **88%**
- Remaining: **12%**

## Next phase

**phase4d7a-frontend-actor-priority-interface-audit**
