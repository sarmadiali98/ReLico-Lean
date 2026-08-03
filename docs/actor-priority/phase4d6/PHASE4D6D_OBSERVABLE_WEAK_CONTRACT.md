# Phase 4D6D Observable and Weak Interface Audit

## Result

ACTOR_DISPATCH_OBSERVABLE_PROJECTION_BOUND_FULL_WEAK_RUNTIME_INTEGRATION_SEPARATE

## Validated baseline

- Strong finite actor-dispatch correspondence is complete.
- The full build passed with 474 jobs.
- The finite production interface probe passed.
- No sorryAx dependency was found.

## Inventory

- Candidate files: 97
- Relevant declarations: 401
- Actor-specific observable declarations: 2
- Actor-specific weak declarations: 0
- Detailed weak declarations: 173
- Detailed observable declarations: 113
- Top candidate: Relico/Correctness/GlobalMultiStorePayloadActorFiniteExecution.lean, score 77

## Highest-ranked reference modules

1. Relico/Correctness/GlobalMultiStorePayloadActorFiniteExecution.lean — score 77; observable 2; weak 0; detailed 0.
2. Relico/Correctness/MultiStorePayloadDetailedFiniteWeakExecutionFoundation.lean — score 59; observable 3; weak 9; detailed 9.
3. Relico/Correctness/MultiStorePayloadDetailedObservableWeakExecution.lean — score 59; observable 15; weak 1; detailed 15.
4. Relico/Tests/MultiStorePayloadDetailedRuntimeLabelCorrespondence.lean — score 56; observable 1; weak 1; detailed 1.
5. Relico/Correctness/DirectLFDetailedFiniteWeakExecution.lean — score 49; observable 3; weak 3; detailed 5.
6. Relico/Correctness/DirectLFDetailedForwardWeakSimulation.lean — score 49; observable 1; weak 5; detailed 6.
7. Relico/Correctness/DirectLFDetailedObservableWeakExecution.lean — score 49; observable 7; weak 1; detailed 7.
8. Relico/DTR/DetailedMultiStorePayloadWeakSemantics.lean — score 46; observable 2; weak 9; detailed 10.
9. Relico/LF/DetailedMultiStorePayloadWeakSemantics.lean — score 46; observable 2; weak 12; detailed 13.
10. Relico/Correctness/MultiStorePayloadDetailedDispatchWeakMatches.lean — score 45; observable 0; weak 11; detailed 11.

## Exact observable boundary

The source and target finite relations use the same ActorDispatchFrame list.
Their selected-actor trace is therefore the shared projection
frames.map ActorDispatchFrame.actorName.

ActorDispatchEventTraceCorresponds supplies pointwise correspondence for
selected source and target dispatch occurrences.

The next proof should expose actor-dispatch observable trace correspondence
in both directions.

## Weak-semantics boundary

The current dispatch layer is one-for-one and introduces no stuttering.
Broader detailed weak semantics may include statement execution, startup,
time advancement, and microsteps. That integration remains a separate proof
obligation.

The next result must be reported as actor-dispatch observable trace
correspondence, not full detailed-runtime weak equivalence.

## Progress

- Before: 82%
- After: 83%
- Remaining: 17%

## Next phase

phase4d6e-actor-dispatch-observable-projection-proof-search
