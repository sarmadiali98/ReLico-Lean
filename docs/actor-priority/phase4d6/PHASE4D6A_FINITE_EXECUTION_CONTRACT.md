# Phase 4D6A Finite-Execution Interface Audit

## Result

**FINITE_EXECUTION_REFERENCE_INTERFACES_AUDITED_STEP_LOCAL_READY_SNAPSHOTS_REQUIRED**

## Import-prerequisite repair

The earlier audit failed because the production actor-dispatch module is
untracked and is not reachable from the tracked `lake build` root. The audit
now materializes the complete untracked dependency chain before importing the
production dispatch theorem module.

## Validated baseline

- Full build: **474 jobs passed**
- Selection correspondence: **complete**
- One-step dispatch correspondence: **complete**
- Interface probe: **passed**
- `sorryAx`: **absent**

## Inventory

- Candidate files: **101**
- Finite/weak declarations: **317**
- Exact actor-priority finite declarations: **0**
- Top candidate: `Relico/Correctness/DetailedBoundPayloadFiniteWeakExecution.lean` with score **50**
- Reuse conclusion: No exact actor-priority finite-execution declaration was found. Existing modules provide proof architecture only.

## Highest-ranked reference modules

1. `Relico/Correctness/DetailedBoundPayloadFiniteWeakExecution.lean` — score 50; finite declarations: 9; exact actor declarations: 0.
2. `Relico/Correctness/DetailedFiniteWeakExecution.lean` — score 50; finite declarations: 6; exact actor declarations: 0.
3. `Relico/Correctness/DirectLFDetailedFiniteWeakExecution.lean` — score 50; finite declarations: 7; exact actor declarations: 0.
4. `Relico/Correctness/MultiStorePayloadDetailedFiniteWeakExecution.lean` — score 50; finite declarations: 10; exact actor declarations: 0.
5. `Relico/Correctness/MultiStorePayloadDetailedFiniteWeakExecutionFoundation.lean` — score 50; finite declarations: 9; exact actor declarations: 0.
6. `Relico/Tests/DetailedBoundPayloadFiniteWeakExecution.lean` — score 47; finite declarations: 2; exact actor declarations: 0.
7. `Relico/Correctness/DetailedBoundPayloadEndToEndCorrectness.lean` — score 44; finite declarations: 3; exact actor declarations: 0.
8. `Relico/Correctness/DetailedBoundPayloadInvariantCarryingFiniteWeakExecution.lean` — score 44; finite declarations: 1; exact actor declarations: 0.
9. `Relico/Correctness/DetailedBoundPayloadObservableWeakExecution.lean` — score 44; finite declarations: 4; exact actor declarations: 0.
10. `Relico/Correctness/DetailedExecutableTranslation.lean` — score 44; finite declarations: 2; exact actor declarations: 0.

## Required finite-execution contract

- **step-local-ready-snapshot**: Every transition carries the ready-actor snapshot used to justify that transition.
- **step-local-selected-actor**: Every transition retains its selected ActorName.
- **compiled-ready-snapshot**: Each target transition uses compileReadyActors on the corresponding source snapshot.
- **request-policy**: The finite relation explicitly fixes the request for the run or carries one request per transition.
- **strong-closure-first**: Prove one-for-one finite dispatch closure before weak or observable wrappers.
- **weak-layer-separate**: Do not conflate actor dispatch closure with statement, time-advance, or microstep weak semantics.

## Semantic boundary

The current one-step theorem is parameterized by a particular request, ready
list, selected actor, and before/after states. A finite execution must not reuse
one fixed ready list for every transition. Dispatch can change the runtime
state and thereby change actor readiness and logical times.

The conservative finite foundation must therefore carry a step-local ready
snapshot. A later refinement may replace explicit snapshots with a readiness
extraction function only after proving that extraction correct.

The first execution theorem should be a strong, one-for-one finite dispatch
closure. Statement, time-advance, microstep, weak, and observable layers remain
separate proof obligations.

## Progress

- Before: **74%**
- After: **75%**
- Remaining: **25%**

## Next phase

**phase4d6b-step-local-finite-execution-foundation**
