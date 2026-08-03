# Actor-Priority Investigation and Integration

This directory is the canonical record for the ReLico actor-priority
investigation.

## Decision that must not be forgotten

**Conclusion 2 has been reached and mechanically proved.**

When actor priority changes which actor may dispatch among simultaneously
ready actors, a faithful translation must preserve that actor-ordering
distinction.

A translation that maps two priority-discriminating source systems to the same
target representation cannot preserve both source behaviors.

## What is required

The target must preserve the relevant ordering information.

A literal `actorPriority` field is **not** required. A behaviorally equivalent
mechanism is sufficient, including:

- precedence constraints;
- LF dependency edges;
- microstep ordering;
- a coordinating scheduler;
- another proved equivalent encoding.

## When ordering may be omitted

Actor-priority information may be omitted only when it is proved semantically
inert, for example when:

- only one actor is eligible;
- actors are not simultaneously ready;
- priorities are tied;
- another causal dependency already forces the same order.

## Current ReLico scope

The formal DTR model supports multiple actor instances through global
multi-store state and actor-indexed dispatch.

The existing correspondence theorem proves behavior after a particular actor
or message server has been selected. It does not yet prove that an autonomous
global scheduler selected that actor according to actor-level priority.

The current Java parser bridge is narrower than the formal model: it accepts
exactly one main actor instance and one reactive class. Actor-priority requests
remain rejected in that supported frontend profile.

These facts must not be conflated.

## Current proof and implementation status

### Completed

- official RMC semantic witness for priority reversal;
- current-profile Approach A exclusion;
- parser-entrypoint bypass audit;
- isolated actor-priority scheduler;
- base, reversed, tied, absent, and explicit-empty tests;
- generic erasure-impossibility theorem;
- concrete actor-priority theorem instantiation;
- six closed Phase 4C tests;
- full 474-job baseline build;
- API and theorem-dependency probes.

### Not completed

- production source actor-priority eligibility;
- production LF actor-order encoding;
- actor-order translation;
- forward scheduler-choice correspondence;
- backward scheduler-choice correspondence;
- finite and weak behavior equivalence for actor-priority-bearing models;
- multi-actor frontend support;
- production actor-priority benchmark registration.

## Defensible claim

> Actor priorities are not universally unnecessary. Actor-ordering
> information is necessary when it changes cross-actor selection. A literal
> priority field is optional, but a behaviorally equivalent ordering mechanism
> is not.

## Claims that are not yet defensible

Do not claim that:

- full Timed Rebeca actor-priority equivalence is already proved;
- the existing production translation preserves active actor priority;
- the existing theorem proves autonomous scheduler choice;
- the DTR formal model is single-actor;
- the one-main-actor frontend restriction is a DTR semantic restriction.

## Architecture rule

The existing actor-indexed dispatch relation remains the primitive
chosen-actor step.

Phase 4D adds actor-level eligibility as a separate layer around that primitive
rather than silently changing the meaning of existing dispatch theorems.

This preserves backward compatibility and makes the additional proof
obligation explicit.

## Phase 4D sequence

1. **4D1 — Source semantics:** define production actor-priority eligibility
   and an actor-priority-constrained dispatch relation.
2. **4D2 — Target semantics:** define an LF representation of equivalent
   cross-actor ordering.
3. **4D3 — Translation:** compile source actor priority to target ordering.
4. **4D4 — Selection correspondence:** prove eligible actors correspond in
   both directions.
5. **4D5 — Dispatch correspondence:** combine scheduler choice with the
   existing chosen-dispatch correspondence.
6. **4D6 — Finite and weak behavior:** lift the result to trace-level
   equivalence.
7. **4D7 — Benchmark/frontend:** add production tests and either extend the
   frontend or retain an explicitly documented frontend boundary.

## Evidence index

- `phase2b/PHASE2B2E_SEMANTIC_GRAPH_WITNESS.*`
- `phase3b/PHASE3B_APPROACH_A_IMPLEMENTATION.*`
- `phase3c/PHASE3C_APPROACH_A_BYPASS_AUDIT.*`
- `phase4a/PHASE4A_ISOLATED_AST_SCHEDULER_FOUNDATION.*`
- `phase4b/PHASE4B_FALSE_POSITIVE_CORRECTION.*`
- `phase4c/PHASE4C_ERASURE_IMPOSSIBILITY_THEOREM.json`
- `phase4c/PHASE4C_ERASURE_IMPOSSIBILITY_TESTS.tsv`
- `phase4c/PHASE4C_DECISION.md`
- `phase4d/PHASE4D_INTEGRATION_ARCHITECTURE.json`
- `phase4d/PHASE4D_INTEGRATION_SURFACE.tsv`
- `phase4d/PHASE4D_IMPLEMENTATION_PLAN.md`

## Phase 4D1 source selector

The exact production selector has now been audited.

`Relico.DTR.GlobalMultiStorePayloadDispatch.Step` selects an actor using:

`actorName : ActorName`

Phase 4D1 therefore adds actor-priority eligibility as a wrapper around that
actor-name-indexed relation. It does not replace the selector with a numeric
index and does not alter the existing chosen-actor dispatch semantics.

The implementation module is:

`Relico/DTR/GlobalMultiStorePayloadActorPriority.lean`

## Phase 4D1 source-semantics completion

The source actor-priority layer is implemented in:

`Relico/DTR/GlobalMultiStorePayloadActorPriority.lean`

It uses `actorName : ActorName`; fixtures construct nominal names through
`Relico.ActorName.mk`.

`ActorPriorityEligible` has an explicit decidability instance backed by the
executable Boolean eligibility function.

Logical-time precedence is applied before actor priority. Minimum-priority ties
remain eligible. Absent and incomplete requests impose no priority filtering.

The wrapper retains the existing
`GlobalMultiStorePayloadDispatch.Step` unchanged.

All ten source and wrapper tests pass.

The LF target ordering, translation, and correctness proofs remain incomplete.

## Phase 4D2 exact target-step binding

The exact LF production transition has been bound to:

`Relico.LF.GlobalMultiStorePayloadDispatch.Step`

Its actor selector is:

`actorName : ActorName`

The target transition therefore uses the same nominal actor-name selector
shape as the source transition. It does not use a numeric actor index.

Phase 4D2B will add target actor-order eligibility as a separate wrapper around
this existing transition. The existing LF transition and its theorems remain
unchanged.

The planned module is:

`Relico/LF/GlobalMultiStorePayloadActorOrder.lean`

## Phase 4D2 target-semantics completion

The LF target actor-order layer is implemented in:

`Relico/LF/GlobalMultiStorePayloadActorOrder.lean`

It uses `actorName : ActorName` and a compiled numeric actor-order
representation. Lower values denote stronger ordering precedence.

Logical time is applied before actor ordering. Minimum-order ties remain
eligible. Absent and incomplete metadata impose no additional filtering.

`ActorOrderDispatchStep` wraps the existing
`Relico.LF.GlobalMultiStorePayloadDispatch.Step` without changing it.

All ten target actor-order and wrapper tests pass.

Source and target selection layers are now complete. Translation and
bidirectional correctness remain incomplete.

## Phase 4D3 translation completion

The information-preserving actor-order compiler is implemented in:

`Relico/Translation/GlobalMultiStorePayloadActorOrder.lean`

The compiler preserves actor names, numeric values, logical times, ready-list
order, absent metadata, present empty metadata, incomplete assignments, and
ties.

Base and priority-reversed source requests compile to distinct target
actor-order requests.

Twelve structural translation tests pass.

Source semantics, target semantics, and translation are now complete.

Selection correspondence and dispatch correspondence remain incomplete.

## Current next step

**phase4d4-source-target-actor-selection-correspondence**

## Phase 4D4B — Actor-selection correspondence

- Production module:
  `Relico/Correctness/GlobalMultiStorePayloadActorSelectionCorrespondence.lean`
- Regression module:
  `Relico/Tests/GlobalMultiStorePayloadActorSelectionCorrespondence.lean`
- Thirteen correspondence theorems elaborate.
- Fourteen closed regression examples pass.
- The theorem package has no `sorryAx` dependency.
- Source-to-target and target-to-source actor eligibility are proved.
- Eligible actor-name lists are preserved exactly.
- Selection correspondence is complete.
- Dispatch correspondence remains the next proof boundary.

## Phase 4D5C — Actor-priority dispatch correspondence

- Production correctness module:
  `Relico/Correctness/GlobalMultiStorePayloadActorDispatchCorrespondence.lean`
- Regression module:
  `Relico/Tests/GlobalMultiStorePayloadActorDispatchCorrespondence.lean`
- Four production correspondence theorems elaborate.
- Four direct exported-API regression checks pass.
- Generic forward and backward wrapper lifting are proved.
- Forward and backward chosen-actor dispatch correspondence are lifted through
  actor eligibility.
- The theorem package has no `sorryAx` dependency.
- One-step actor-priority dispatch correspondence is complete.
- Finite execution correspondence is the next proof boundary.

## Phase 4D6C — Step-local finite dispatch correspondence

- Production correctness module:
  `Relico/Correctness/GlobalMultiStorePayloadActorFiniteExecution.lean`
- Regression module:
  `Relico/Tests/GlobalMultiStorePayloadActorFiniteExecution.lean`
- Every finite transition carries its own ready-actor snapshot and selected
  `ActorName`.
- The target compiles each ready snapshot separately.
- Forward and backward finite one-for-one dispatch correspondence are proved.
- Selected source and target dispatch occurrences correspond pointwise.
- Corresponding occurrence traces have equal lengths.
- Twelve exported-interface regression checks pass.
- The production theorem package has no `sorryAx` dependency.
- Weak and observable execution correspondence remain separate obligations.

## Phase 4D6F — Actor-dispatch observable correspondence

- Production correctness module:
  `Relico/Correctness/GlobalMultiStorePayloadActorObservableProjection.lean`
- Regression module:
  `Relico/Tests/GlobalMultiStorePayloadActorObservableProjection.lean`
- The selected-actor trace is the shared projection of the step-local frame
  list.
- Source and target selected-actor traces are equal.
- Forward and backward actor-dispatch observable correspondence are proved.
- Pointwise dispatch-event correspondence is retained.
- The actor-dispatch wrapper introduces no stuttering.
- Eight exported-interface regression checks pass.
- The theorem package has no `sorryAx` dependency.
- This remains a scoped actor-dispatch result, not full detailed-runtime weak
  equivalence.
