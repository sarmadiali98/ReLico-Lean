# Phase 4D4B Selection Correspondence

## Result

**SELECTION_CORRESPONDENCE_PRODUCTION_INSTALLED**

The source actor-priority selector and compiled LF actor-order selector now
have a production correctness module.

## Proven theorem package

1. `lookupActorOrder_compileActorPriorityAssignment_eq` — priority/order lookup preservation.
2. `lookupReadyTargetActor_compileReadyActors_eq` — ready-actor lookup preservation.
3. `all_compileReadyActors_eq` — generic List.all transport.
4. `targetEarliestReady_compileReadyActors_eq` — earliest logical-time preservation.
5. `filter_compileReadyActors_eq` — generic List.filter transport.
6. `sameTimeReadyTargetActors_compileReadyActors_eq` — same-time ready-set preservation.
7. `targetOrderCoversReadyActors_compile_eq` — priority-assignment coverage preservation.
8. `selectedHasMinimalActorOrder_compile_eq` — minimal actor-order preservation.
9. `actorSelectionEligibleBool_compile_eq` — Boolean eligibility equality.
10. `actorSelectionEligible_compile_iff` — propositional eligibility equivalence.
11. `actorSelectionEligible_forward` — source-to-target eligibility.
12. `actorSelectionEligible_backward` — target-to-source eligibility.
13. `eligibleActorNames_compile_eq` — eligible actor-name list equality.

## Validation

- Correctness theorems: **13/13 elaborated**
- Regression examples: **14/14 passed**
- Full `lake build`: **passed**
- `sorryAx`: **absent**
- Original repository mutation: **none**
- Staging, commit, and push: **none**

The proof package may depend on Lean's standard `propext` and `Quot.sound`
axioms. It has no admitted theorem dependency.

## Scope

Selection correspondence is complete.

Dispatch-step correspondence, finite execution lifting, frontend integration,
and final actor-priority-bearing equivalence remain incomplete.

## Progress

- Before: **60%**
- After: **64%**
- Remaining: **36%**

## Next phase

**phase4d5a-dispatch-correspondence-interface-audit**
