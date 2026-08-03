# Phase 4D2B Target Actor-Order Semantics Result

## Result

The production-layer LF target actor-order semantics has been implemented.

Classification:

**TARGET_ACTOR_ORDER_ELIGIBILITY_AND_DISPATCH_WRAPPER_IMPLEMENTED**

## New target module

`Relico/LF/GlobalMultiStorePayloadActorOrder.lean`

The module uses a compiled numeric ordering representation.

Lower natural numbers denote stronger actor-order precedence.

A literal actor-priority field is not required.

## Selection policy

Target selection applies logical time before actor ordering.

Ordering compares actors only inside the same simultaneous-ready cohort.

Minimum-order ties preserve nondeterministic eligibility.

Absent ordering metadata imposes no filtering.

Incomplete ordering metadata does not eliminate uncovered actors.

## Existing LF transition

The wrapper retains:

`Relico.LF.GlobalMultiStorePayloadDispatch.Step`

unchanged.

`ActorOrderDispatchStep` requires:

1. target actor-order eligibility for `actorName`;
2. the existing LF dispatch step.

## Mechanical validation

Ten target tests passed:

- base ordering;
- reversed ordering;
- tied ordering;
- absent ordering;
- incomplete ordering;
- logical-time precedence;
- absent actor;
- ineligible actor under the base order;
- wrapper introduction;
- wrapper premise extraction.

The target source, tests, integration build, API surface, decidability
instance, and theorem dependencies all passed.

## Non-regression status

The existing LF global dispatch module was not modified.

No translation, correctness, frontend, or registry file was modified.

## Conclusion status

**CONCLUSION_2_REACHED**

Source actor-priority semantics is complete.

Target actor-order semantics is complete.

Production integration remains incomplete until translation and bidirectional
selection/dispatch correspondence are implemented.

## Next phase

**phase4d3-actor-priority-to-target-order-translation**
