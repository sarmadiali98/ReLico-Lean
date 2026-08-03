# Phase 4D5A Dispatch-Correspondence Interface Audit

## Result

**DISPATCH_CORRESPONDENCE_INTERFACES_BOUND_GENERIC_PROOF_READY**

The actor-level eligibility wrappers are now bound to the existing
actor-name-indexed source and target dispatch relations.

## Exact wrapper architecture

- Source base relation:
  `Relico.DTR.GlobalMultiStorePayloadDispatch.Step`
- Target base relation:
  `Relico.LF.GlobalMultiStorePayloadDispatch.Step`
- Source wrapper:
  `ActorPriorityDispatchStep`
- Target wrapper:
  `ActorOrderDispatchStep`
- Source eligibility transport:
  `actorSelectionEligible_forward`
- Target-to-source eligibility transport:
  `actorSelectionEligible_backward`

The selector remains `actorName`. No numeric actor index is introduced.

## Existing chosen-actor correspondence candidates

1. `Relico.Correctness.GlobalMultiStorePayloadDispatch.synchronizedGlobalDispatch_forward` — score 53, `Relico/Correctness/GlobalMultiStorePayloadDispatchCorrespondence.lean:642`.
2. `Relico.Correctness.GlobalMultiStorePayloadDispatch.synchronizedGlobalDispatch_backward` — score 53, `Relico/Correctness/GlobalMultiStorePayloadDispatchCorrespondence.lean:894`.
3. `Relico.Correctness.GlobalMultiStorePayloadDispatch.synchronized_global_metric_time_corresponds` — score 46, `Relico/Correctness/GlobalMultiStorePayloadDispatchCorrespondence.lean:21`.
4. `Relico.Correctness.boundPayloadDispatch_backward` — score 45, `Relico/Correctness/BoundPayloadDispatch.lean:283`.
5. `Relico.Correctness.concreteDetailed_dispatch_backward` — score 45, `Relico/Correctness/ConcreteDetailedStateCorrespondence.lean:475`.
6. `Relico.Correctness.concreteDetailed_consumeReadySameTime_backward_weak` — score 45, `Relico/Correctness/DetailedBackwardWeakSimulation.lean:713`.
7. `Relico.Correctness.detailedBoundPayload_timeAdvance_backward_weak` — score 45, `Relico/Correctness/DetailedBoundPayloadBackwardWeakSimulation.lean:118`.
8. `Relico.Correctness.detailedBoundPayload_consumeReadySameTime_backward_weak` — score 45, `Relico/Correctness/DetailedBoundPayloadBackwardWeakSimulation.lean:630`.
9. `Relico.Correctness.detailedBoundPayload_consumeNow_backward_weak` — score 45, `Relico/Correctness/DetailedBoundPayloadBackwardWeakSimulation.lean:727`.
10. `Relico.Correctness.directLFDetailedRuntime_consumeReadySameTime_backward_weak` — score 45, `Relico/Correctness/DirectLFDetailedBackwardWeakSimulation.lean:649`.

The ranking is an audit aid. Phase 4D5B must elaborate the exact selected
candidate before making a dispatch-correspondence claim.

## Required proof decomposition

1. Decompose a source `ActorPriorityDispatchStep`.
2. Transport source eligibility to target eligibility.
3. Reuse the existing chosen-actor dispatch correspondence.
4. Construct the matching target `ActorOrderDispatchStep`.
5. Prove the reverse direction using target-to-source eligibility.
6. Package forward, backward, and wrapper-projection theorems.
7. Audit all installed theorems for `sorryAx`.

## Non-invasive constraints

- Do not modify either existing base dispatch relation.
- Do not redefine either actor-level wrapper.
- Do not replace `actorName` with a numeric selector.
- Do not claim finite execution correspondence in Phase 4D5.
- Do not claim final actor-priority-bearing equivalence in Phase 4D5.

## Current status

- Source priority semantics: complete
- Target order semantics: complete
- Translation: complete
- Selection correspondence: complete
- Dispatch correspondence: incomplete
- Finite execution correspondence: incomplete
- Frontend integration: incomplete
- Final equivalence: incomplete

## Progress

- Before: **64%**
- After: **65%**
- Remaining: **35%**

## Next phase

**phase4d5b-dispatch-correspondence-proof-search**
