# Phase 4D3A Translation-Interface Audit

## Result

Classification:

**TRANSLATION_CONVENTIONS_AUDITED_STRUCTURAL_ORDER_COMPILER_READY**

The source actor-priority semantics and target actor-order semantics both
remain mechanically valid.

The existing production translation surface imports successfully.

## Gate repair

The prior command stopped because its expected canonical README SHA omitted
the final hexadecimal `b`.

Correct SHA:

`7e3795540b96c17a2848b6d57357dcb66d6b1abf579a9c1e2454ce8a9c088c1b`

There was no Phase 4D2B semantic-report mismatch.

## Selected translation convention

Function prefix:

`compile`

New module:

`Relico/Translation/GlobalMultiStorePayloadActorOrder.lean`

Namespace:

`Relico.Translation.GlobalMultiStorePayloadActorOrder`

## Source and target interfaces

Source:

`Relico.DTR.GlobalMultiStorePayloadActorPriority`

Target:

`Relico.LF.GlobalMultiStorePayloadActorOrder`

Both sides use nominal `ActorName` values and numeric ordering values.

## Required compiler functions

Phase 4D3B must implement:

- `compileActorPriorityAssignment`;
- `compileActorPriorityRequest`;
- `compileReadyActor`;
- `compileReadyActors`.

## Structural preservation requirements

The compiler must preserve:

- actor names;
- logical times;
- numeric priority/order values;
- `none`;
- incomplete assignments;
- equal-value ties.

It must not invent actors or ordering entries.

## Discrimination requirement

Base and reversed source priority requests must compile to distinct target
ordering requests.

This is the direct production-level response to the erasure-impossibility
result.

## Ranked existing translation declarations

| Rank | Qualified name | Location | Kind | Score | Evidence |
|---:|---|---|---|---:|---|
| 1 | `Relico.Translation.GlobalMultiStorePayloadBasic.compileGlobalMultiStorePayloadActors` | `Relico/Translation/GlobalMultiStorePayloadBasic.lean:15-34` | def | 27 | executable-declaration,translation-name,global-payload-type,payload-type,actor-name,source-reference,target-reference |
| 2 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadReactor` | `Relico/Translation/MultiStorePayloadBasic.lean:174-209` | def | 24 | executable-declaration,translation-name,payload-type,actor-name,source-reference,target-reference,structural-map,ordering-related |
| 3 | `Relico.Translation.GlobalMultiStorePayloadBasic.translateGlobalMultiStorePayloadCore` | `Relico/Translation/GlobalMultiStorePayloadBasic.lean:35-47` | def | 23 | executable-declaration,translation-name,global-payload-type,payload-type,source-reference,target-reference |
| 4 | `Relico.Translation.GlobalMultiStorePayloadExternalSend.translateGlobalMultiStorePayloadExternalSendOccurrence` | `Relico/Translation/GlobalMultiStorePayloadExternalSend.lean:18-51` | def | 23 | executable-declaration,translation-name,global-payload-type,payload-type,source-reference,target-reference |
| 5 | `Relico.Translation.GlobalMultiStorePayloadExternalSendFrame.translateGlobalMultiStorePayloadExternalSendFrame` | `Relico/Translation/GlobalMultiStorePayloadExternalSendFrame.lean:10-23` | def | 23 | executable-declaration,translation-name,global-payload-type,payload-type,source-reference,target-reference |
| 6 | `Relico.Translation.GlobalMultiStorePayloadExternalSendStatement.translateGlobalMultiStorePayloadExternalSendStatement` | `Relico/Translation/GlobalMultiStorePayloadExternalSendStatement.lean:16-38` | def | 23 | executable-declaration,translation-name,global-payload-type,payload-type,source-reference,target-reference |
| 7 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadMessageReactions` | `Relico/Translation/MultiStorePayloadBasic.lean:161-173` | def | 20 | executable-declaration,translation-name,payload-type,source-reference,target-reference,structural-map,ordering-related |
| 8 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadExpr` | `Relico/Translation/MultiStorePayloadBasic.lean:13-28` | def | 18 | executable-declaration,translation-name,payload-type,source-reference,target-reference,ordering-related |
| 9 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadExprs` | `Relico/Translation/MultiStorePayloadBasic.lean:29-38` | def | 18 | executable-declaration,translation-name,payload-type,source-reference,target-reference,structural-map |
| 10 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadStmt` | `Relico/Translation/MultiStorePayloadBasic.lean:39-67` | def | 18 | executable-declaration,translation-name,payload-type,source-reference,target-reference,ordering-related |
| 11 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadBody` | `Relico/Translation/MultiStorePayloadBasic.lean:68-78` | def | 18 | executable-declaration,translation-name,payload-type,source-reference,target-reference,structural-map |
| 12 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadStartupReaction` | `Relico/Translation/MultiStorePayloadBasic.lean:94-119` | def | 18 | executable-declaration,translation-name,payload-type,source-reference,target-reference,ordering-related |
| 13 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadReaction` | `Relico/Translation/MultiStorePayloadBasic.lean:120-146` | def | 18 | executable-declaration,translation-name,payload-type,source-reference,target-reference,ordering-related |
| 14 | `Relico.Translation.Basic.compileReactor` | `Relico/Translation/Basic.lean:47-56` | def | 17 | executable-declaration,translation-name,actor-name,source-reference,target-reference |
| 15 | `Relico.Translation.Basic.compileReactorInstance` | `Relico/Translation/Basic.lean:57-62` | def | 17 | executable-declaration,translation-name,actor-name,source-reference,target-reference |
| 16 | `Relico.Translation.MultiStoreBasic.compileMessageReactions` | `Relico/Translation/MultiStoreBasic.lean:71-79` | def | 17 | executable-declaration,translation-name,source-reference,target-reference,structural-map,ordering-related |
| 17 | `Relico.Translation.MultiStoreBasic.compileMultiStoreReactor` | `Relico/Translation/MultiStoreBasic.lean:348-376` | def | 17 | executable-declaration,translation-name,actor-name,source-reference,target-reference |
| 18 | `Relico.Translation.StoreBasic.compileStoreReactor` | `Relico/Translation/StoreBasic.lean:71-113` | def | 17 | executable-declaration,translation-name,actor-name,source-reference,target-reference |
| 19 | `Relico.Translation.MultiStorePayloadBasic.compileMultiStorePayloadAction` | `Relico/Translation/MultiStorePayloadBasic.lean:79-93` | def | 16 | executable-declaration,translation-name,payload-type,source-reference,target-reference |
| 20 | `Relico.Translation.MultiStorePayloadBasic.translateMultiStorePayloadCore` | `Relico/Translation/MultiStorePayloadBasic.lean:210-223` | def | 16 | executable-declaration,translation-name,payload-type,source-reference,target-reference |
| 21 | `Relico.Translation.MultiStorePayloadCppBackend.translateMultiStorePayloadToCppSource` | `Relico/Translation/MultiStorePayloadCppBackend.lean:16-27` | def | 16 | executable-declaration,translation-name,payload-type,source-reference,target-reference |
| 22 | `Relico.Translation.Basic.compileBody` | `Relico/Translation/Basic.lean:28-32` | def | 15 | executable-declaration,translation-name,source-reference,target-reference,structural-map |
| 23 | `Relico.Translation.BoundPayloadBasic.compileBoundPayloadBody` | `Relico/Translation/BoundPayloadBasic.lean:33-51` | def | 15 | executable-declaration,translation-name,source-reference,target-reference,ordering-related |
| 24 | `Relico.Translation.BoundPayloadBasic.compilePayloadMessageServer` | `Relico/Translation/BoundPayloadBasic.lean:52-71` | def | 15 | executable-declaration,translation-name,source-reference,target-reference,ordering-related |
| 25 | `Relico.Translation.MultiStoreBasic.compileLogicalActions` | `Relico/Translation/MultiStoreBasic.lean:57-70` | def | 15 | executable-declaration,translation-name,source-reference,structural-map,ordering-related |
| 26 | `Relico.Translation.MultiStoreBasic.compileMultiStoreStartupReaction` | `Relico/Translation/MultiStoreBasic.lean:327-347` | def | 15 | executable-declaration,translation-name,source-reference,target-reference,ordering-related |
| 27 | `Relico.Translation.PayloadBasic.compilePayloadBody` | `Relico/Translation/PayloadBasic.lean:30-36` | def | 15 | executable-declaration,translation-name,source-reference,target-reference,structural-map |
| 28 | `Relico.Translation.StoreBasic.compileStateVariableDecl` | `Relico/Translation/StoreBasic.lean:14-26` | def | 15 | executable-declaration,translation-name,source-reference,target-reference,ordering-related |
| 29 | `Relico.Translation.StoreBasic.compileStateVariableDecls` | `Relico/Translation/StoreBasic.lean:27-33` | def | 15 | executable-declaration,translation-name,source-reference,target-reference,structural-map |
| 30 | `Relico.Translation.Basic.compileExpr` | `Relico/Translation/Basic.lean:14-20` | def | 13 | executable-declaration,translation-name,source-reference,target-reference |

## Implementation contract

| ID | Subject | Required value | Status |
|---|---|---|---|
| TR1 | new translation module | Relico/Translation/GlobalMultiStorePayloadActorOrder.lean | planned |
| TR2 | namespace | Relico.Translation.GlobalMultiStorePayloadActorOrder | planned |
| TR3 | source import | Relico.DTR.GlobalMultiStorePayloadActorPriority | required |
| TR4 | target import | Relico.LF.GlobalMultiStorePayloadActorOrder | required |
| TR5 | assignment translation | compileActorPriorityAssignment preserves actor names and numeric values | required |
| TR6 | request translation | compileActorPriorityRequest maps none to none and some structurally | required |
| TR7 | ready-actor translation | compileReadyActor preserves actorName and logicalTime | required |
| TR8 | ready-list translation | compileReadyActors is structural list mapping | required |
| TR9 | discrimination | base and reversed priority requests compile to distinct target order requests | required |
| TR10 | tie preservation | equal source priorities remain equal target orders | required |
| TR11 | absence and incompleteness | translation preserves absent and incomplete metadata without inventing entries | required |
| TR12 | semantic scope | translation only; selection and dispatch correspondence remain later phases | required |
| TR13 | existing translation compatibility | existing translation modules remain unchanged | required |
| TR14 | next phase | phase4d3b-actor-priority-to-target-order-translation-implementation | ready |

## Scope boundary

Phase 4D3B proves structural translation properties and discriminating
examples.

Selection correspondence belongs to Phase 4D4.

Dispatch correspondence belongs to Phase 4D5.

## Non-regression constraints

Do not modify existing translation modules.

Do not modify existing DTR or LF semantics.

Do not modify correctness, frontend, or registry files.

## Conclusion status

**CONCLUSION_2_REACHED**

Source semantics is complete.

Target semantics is complete.

Translation is ready for implementation but is not yet complete.

## Next phase

**phase4d3b-actor-priority-to-target-order-translation-implementation**
