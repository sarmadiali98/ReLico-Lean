# Phase 4D4A Actor-Selection Correspondence Audit

## Result

Classification:

**SELECTION_CORRESPONDENCE_INTERFACES_BOUND_GENERIC_PROOF_READY**

The audit passed after correcting one probe-validator identifier.

## Probe-validator repair

The failed validator expected:

`sourceEligibleActorNames`

That declaration does not exist.

The exact bound source function is:

`Relico.DTR.GlobalMultiStorePayloadActorPriority.eligibleActorNames`

The corrected Lean interface probe passed.

## Exact source interface

Ready actor:

`Relico.DTR.GlobalMultiStorePayloadActorPriority.ReadyActor`

Boolean eligibility:

`Relico.DTR.GlobalMultiStorePayloadActorPriority.actorPriorityEligibleBool`

Propositional eligibility:

`Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityEligible`

Eligible actor-name list:

`Relico.DTR.GlobalMultiStorePayloadActorPriority.eligibleActorNames`

## Exact target interface

Ready actor:

`Relico.LF.GlobalMultiStorePayloadActorOrder.ReadyTargetActor`

Boolean eligibility:

`Relico.LF.GlobalMultiStorePayloadActorOrder.targetActorOrderEligibleBool`

Propositional eligibility:

`Relico.LF.GlobalMultiStorePayloadActorOrder.TargetActorOrderEligible`

Eligible actor-name list:

`Relico.LF.GlobalMultiStorePayloadActorOrder.eligibleTargetActorNames`

## Exact translation interface

Request compiler:

`Relico.Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest`

Ready-actor compiler:

`Relico.Translation.GlobalMultiStorePayloadActorOrder.compileReadyActor`

Ready-list compiler:

`Relico.Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors`

## Required Phase 4D4B theorems

Phase 4D4B must prove:

1. equality of source and compiled-target eligibility Booleans;
2. equivalence of source and compiled-target eligibility propositions;
3. equality of source and compiled-target eligible-name lists;
4. the forward eligibility implication;
5. the backward eligibility implication.

## Required examples

The theorem package must cover:

- base priorities;
- reversed priorities;
- tied priorities;
- absent metadata;
- incomplete metadata;
- logical-time precedence.

## Existing correctness conventions

The audit found **483** correctness declarations using
correspondence, forward/backward, compilation, preservation, reflection, or
equivalence naming conventions.

## Implementation contract

| ID | Subject | Required value | Status |
|---|---|---|---|
| SC1 | new correctness module | Relico/Correctness/GlobalMultiStorePayloadActorSelectionCorrespondence.lean | planned |
| SC2 | source ready actor | Relico.DTR.GlobalMultiStorePayloadActorPriority.ReadyActor | bound |
| SC3 | target ready actor | Relico.LF.GlobalMultiStorePayloadActorOrder.ReadyTargetActor | bound |
| SC4 | source Boolean | Relico.DTR.GlobalMultiStorePayloadActorPriority.actorPriorityEligibleBool | bound |
| SC5 | target Boolean | Relico.LF.GlobalMultiStorePayloadActorOrder.targetActorOrderEligibleBool | bound |
| SC6 | Boolean correspondence | source and compiled-target eligibility Booleans are equal | required |
| SC7 | propositional correspondence | Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityEligible iff Relico.LF.GlobalMultiStorePayloadActorOrder.TargetActorOrderEligible after compilation | required |
| SC8 | eligible-name correspondence | Relico.DTR.GlobalMultiStorePayloadActorPriority.eligibleActorNames equals Relico.LF.GlobalMultiStorePayloadActorOrder.eligibleTargetActorNames after compilation | required |
| SC9 | forward implication | source eligibility implies compiled target eligibility | required |
| SC10 | backward implication | compiled target eligibility implies source eligibility | required |
| SC11 | translation inputs | Relico.Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest, Relico.Translation.GlobalMultiStorePayloadActorOrder.compileReadyActor, Relico.Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors | bound |
| SC12 | required examples | base, reversed, tied, absent, incomplete, logical-time precedence | required |
| SC13 | dispatch and trust boundary | dispatch remains out of scope; no sorry, admit, axiom, unsafe, or sorryAx | required |
| SC14 | next phase | phase4d4b-source-target-actor-selection-correspondence-implementation | ready |

## Scope boundary

Phase 4D4 concerns actor-selection eligibility.

Correspondence of the underlying source and target dispatch relations remains
Phase 4D5.

## Non-regression constraints

Existing DTR, LF, translation, and correctness modules remain unchanged.

Frontend and registry files remain unchanged.

## Trust status

The audited translation preservation theorems have no `sorryAx` dependency.

## Conclusion status

**CONCLUSION_2_REACHED**

Source semantics is complete.

Target semantics is complete.

Translation is complete.

Selection correspondence is ready for implementation but is not yet complete.

## Next phase

**phase4d4b-source-target-actor-selection-correspondence-implementation**
