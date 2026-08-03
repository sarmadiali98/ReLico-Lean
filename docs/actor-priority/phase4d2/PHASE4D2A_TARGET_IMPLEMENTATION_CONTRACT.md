# Phase 4D2A LF Target-Interface Audit

## Audit result

Classification:

**UNIQUE_HIGH_CONFIDENCE_TARGET_TRANSITION_INTERFACE_DISCOVERED**

The audit completed after repairing the declaration-scoring script.

The relevant LF global payload modules import successfully.

The Phase 4D1B source module and all ten source tests were re-elaborated
successfully.

## Top target candidate

- Qualified name: `Relico.LF.GlobalMultiStorePayloadDispatch.Step`
- Location: `Relico/LF/GlobalMultiStorePayloadDispatch.lean:151-201`
- Kind: `inductive`
- Score: `34`
- Evidence: `inductive-relation,transition-name,global-state,pending-action,payload-reaction,actor-name,proposition,selected-value,lookup-premise`

## Ranked transition candidates

| Rank | Qualified name | Location | Kind | Score | Evidence |
|---:|---|---|---|---:|---|
| 1 | `Relico.LF.GlobalMultiStorePayloadDispatch.Step` | `Relico/LF/GlobalMultiStorePayloadDispatch.lean:151-201` | inductive | 34 | inductive-relation,transition-name,global-state,pending-action,payload-reaction,actor-name,proposition,selected-value,lookup-premise |
| 2 | `Relico.LF.GlobalMultiStorePayloadOneStep.Step` | `Relico/LF/GlobalMultiStorePayloadOneStep.lean:70-118` | inductive | 33 | inductive-relation,transition-name,global-state,pending-action,payload-reaction,actor-name,proposition,selected-value |
| 3 | `Relico.LF.GlobalMultiStorePayloadFiniteExecution.Steps` | `Relico/LF/GlobalMultiStorePayloadFiniteExecution.lean:13-49` | inductive | 19 | inductive-relation,transition-name,global-state,proposition |
| 4 | `Relico.LF.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep` | `Relico/LF/GlobalMultiStorePayloadOneStep.lean:13-39` | inductive | 19 | inductive-relation,transition-name,global-state,proposition |
| 5 | `Relico.LF.GlobalMultiStorePayloadProgram.lookupActor` | `Relico/LF/GlobalMultiStorePayload.lean:71-84` | def | 12 | definition,global-state,actor-name,lookup-premise |
| 6 | `Relico.LF.GlobalMultiStorePayloadState.lookupActor` | `Relico/LF/GlobalMultiStorePayload.lean:85-94` | def | 12 | definition,global-state,actor-name,lookup-premise |
| 7 | `Relico.LF.GlobalMultiStorePayloadState.updateActor` | `Relico/LF/GlobalMultiStorePayload.lean:95-112` | def | 11 | definition,global-state,actor-name |
| 8 | `Relico.LF.GlobalMultiStorePayloadDispatch.synchronizedAfter` | `Relico/LF/GlobalMultiStorePayloadDispatch.lean:18-37` | def | 11 | definition,global-state,actor-name |
| 9 | `Relico.LF.GlobalMultiStorePayloadProgram.actorProgramsMatchKeys` | `Relico/LF/GlobalMultiStorePayload.lean:50-60` | def | 8 | definition,actor-name,reactor-instance |
| 10 | `Relico.LF.GlobalMultiStorePayloadExternalSend.apply` | `Relico/LF/GlobalMultiStorePayloadExternalSend.lean:76-97` | def | 8 | definition,global-state,lookup-premise |
| 11 | `Relico.LF.GlobalMultiStorePayloadExternalSendFrame.apply` | `Relico/LF/GlobalMultiStorePayloadExternalSendFrame.lean:105-136` | def | 8 | definition,global-state,lookup-premise |
| 12 | `Relico.LF.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter` | `Relico/LF/GlobalMultiStorePayloadExternalSendFrame.lean:90-104` | def | 7 | definition,global-state |
| 13 | `Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries` | `Relico/LF/GlobalMultiStorePayloadInitialization.lean:33-47` | def | 7 | definition,global-state |
| 14 | `Relico.LF.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState` | `Relico/LF/GlobalMultiStorePayloadInitialization.lean:48-69` | def | 7 | definition,global-state |

## Selector evidence

- `actorName`: **15**
- `ActorName`: **6**
- `PendingAction`: **3**

No selector identifier is assumed in advance.

## Target architecture

Create:

`Relico/LF/GlobalMultiStorePayloadActorOrder.lean`

Namespace:

`Relico.LF.GlobalMultiStorePayloadActorOrder`

The new target ordering layer must wrap the existing LF transition rather than
change its meaning.

A literal actor-priority field is optional. Equivalent ordering information is
mandatory in priority-discriminating cases.

## Target policy

The target semantics must match the source policy:

- logical time precedes actor ordering;
- ties preserve nondeterminism;
- absent metadata imposes no filtering;
- incomplete metadata does not eliminate uncovered actors.

## Implementation contract

| ID | Subject | Required value | Status |
|---|---|---|---|
| T1 | new target module | Relico/LF/GlobalMultiStorePayloadActorOrder.lean | planned |
| T2 | existing transition compatibility | existing LF global payload transitions remain unchanged | required |
| T3 | ordering representation | behaviorally equivalent ordering; literal priority field optional | required |
| T4 | logical time | logical time precedes actor ordering | required |
| T5 | ties | minimal-order ties retain eligibility | required |
| T6 | absent metadata | no additional target filtering | required |
| T7 | incomplete metadata | uncovered actors are not silently eliminated | required |
| T8 | wrapper architecture | target eligibility plus existing LF transition | required |
| T9 | translation discrimination | base and reversed source priorities compile to distinguishable target ordering | required |
| T10 | proof readiness | Boolean and propositional target eligibility APIs | required |

## Translation requirement

Base and reversed source assignments must compile to distinguishable target
ordering values whenever they produce different source eligibility.

## Non-regression constraints

Existing LF transition definitions remain unchanged.

Translation, correctness, frontend, and registry files remain unchanged during
this audit.

## Conclusion status

**CONCLUSION_2_REACHED**

Source actor-priority semantics is complete.

Target actor-order semantics is not complete.

## Next phase

**phase4d2b-target-global-actor-order-semantics-implementation**
