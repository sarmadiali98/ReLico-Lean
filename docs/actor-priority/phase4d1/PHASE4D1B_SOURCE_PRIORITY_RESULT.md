# Phase 4D1B Source Actor-Priority Semantics Result

## Result

The production-layer source actor-priority semantics has been implemented.

Classification:

**SOURCE_ACTOR_PRIORITY_ELIGIBILITY_AND_DISPATCH_WRAPPER_IMPLEMENTED**

## Repairs

Two fixture/API issues were resolved:

1. `ActorName` is nominal, so fixtures use `Relico.ActorName.mk`.
2. `ActorPriorityEligible` now has the named instance
   `instDecidableActorPriorityEligible`.

The instance unfolds eligibility to its executable Boolean equality, allowing
`decide` to verify positive and negative eligibility propositions.

## New source module

`Relico/DTR/GlobalMultiStorePayloadActorPriority.lean`

## Selection semantics

Logical time is applied before actor priority.

Lower natural numbers denote higher priority.

Minimum-priority ties remain nondeterministic.

Absent and incomplete requests impose no priority filtering.

## Dispatch wrapper

`ActorPriorityDispatchStep` combines:

1. eligibility for the selected `actorName`;
2. the unchanged `GlobalMultiStorePayloadDispatch.Step`.

## Mechanical validation

All ten source and wrapper tests passed.

The source module, test module, API surface, decidability instance, and theorem
dependencies were probed successfully.

The full 474-job baseline build passed.

## Non-regression status

No existing DTR, LF, translation, correctness, frontend, or registry file was
modified.

## Conclusion status

**CONCLUSION_2_REACHED**

The source actor-ordering layer is complete.

Production integration remains incomplete until target ordering, translation,
selection correspondence, and dispatch correspondence are implemented.

## Next phase

**phase4d2-target-global-actor-order-semantics**
