# Phase 4D3B Actor-Priority to Target-Order Translation

## Result

Classification:

**ACTOR_PRIORITY_INFORMATION_PRESERVING_TARGET_ORDER_TRANSLATION_IMPLEMENTED**

The structural compiler from source actor-priority metadata to target
actor-order metadata has been implemented.

## New translation module

`Relico/Translation/GlobalMultiStorePayloadActorOrder.lean`

## Compiler functions

The module provides:

- `compileActorPriorityAssignment`;
- `compileActorPriorityRequest`;
- `compileReadyActor`;
- `compileReadyActors`.

## Preserved information

The translation preserves:

- nominal actor names;
- numeric priority/order values;
- logical times;
- ready-list order;
- absent metadata;
- present empty metadata;
- incomplete assignments;
- equal-value ties.

It does not invent, erase, or reorder assignment entries.

## Priority-reversal discrimination

The base request and the priority-reversed request compile to different target
actor-order requests.

The translation therefore does not recreate the actor-priority erasure
collision ruled out in Phase 4C.

## Mechanical validation

Twelve translation tests passed.

The source semantics, target semantics, translation module, test module, API
surface, and theorem dependencies all elaborated successfully.

The full baseline and integration builds passed.

No checked theorem depends on `sorryAx`.

## Scope boundary

This phase establishes structural translation.

It does not yet establish that source and target eligibility predicates agree.

That proof belongs to Phase 4D4.

Dispatch correspondence remains Phase 4D5.

## Non-regression status

No existing DTR, LF, or translation module was modified.

No correctness, frontend, or registry file was modified.

## Conclusion status

**CONCLUSION_2_REACHED**

Source semantics is complete.

Target semantics is complete.

Information-preserving actor-order translation is complete.

Production integration remains incomplete until selection and dispatch
correspondence are proved.

## Next phase

**phase4d4-source-target-actor-selection-correspondence**
