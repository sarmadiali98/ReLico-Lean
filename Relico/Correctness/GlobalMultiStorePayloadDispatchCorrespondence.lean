/-
Bidirectional correspondence for explicit actor-indexed global payload
dispatch.

Existing local forward and backward runtime dispatch theorems are lifted
pointwise through aligned actor stores. Actor selection, cross-actor priority,
finite execution, and weak bisimulation remain outside this layer.
-/
import Relico.DTR.GlobalMultiStorePayloadDispatch
import Relico.LF.GlobalMultiStorePayloadDispatch
import Relico.Correctness.GlobalMultiStorePayloadStateCorrespondence
import Relico.Correctness.MultiStorePayloadForwardDispatchRuntime
import Relico.Correctness.MultiStorePayloadBackwardDispatchRuntime

set_option autoImplicit false

namespace Relico
namespace Correctness
namespace GlobalMultiStorePayloadDispatch

theorem synchronized_global_metric_time_corresponds
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceAfter :
      DTR.MultiStorePayloadState}
    {targetAfter :
      LF.MultiStorePayloadState}
    (sourceBeforeGlobal :
      DTR.GlobalMultiStorePayloadState)
    (targetBeforeGlobal :
      LF.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (hRuntime :
      _root_.Relico.Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceAfter
        targetAfter) :
    (DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter
      sourceBeforeGlobal
      actorName
      sourceAfter).currentTime =
      (LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
        targetBeforeGlobal
        actorName
        targetAfter).currentTag.time := by

  simpa [
    DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter,
    LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
  ] using
    hRuntime.states.states.currentTime.symm

/-
Temporary source relation for the synchronized actor-indexed global lift.
Actor choice remains an explicit parameter.
-/

theorem actorStatesCorrespond_lookup_target
    {models :
      DTR.GlobalMultiStorePayloadActors}
    {sourceStates :
      DTR.GlobalMultiStorePayloadActorStates}
    {targetStates :
      LF.GlobalMultiStorePayloadActorStates}
    (hCorrespond :
      _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
        models
        sourceStates
        targetStates) :
    ∀
      {actorName :
        ActorName}
      {actorModel :
        DTR.MultiStorePayloadModel}
      {sourceState :
        DTR.MultiStorePayloadState},
      Store.lookup
          models
          actorName =
        some actorModel →
      Store.lookup
          sourceStates
          actorName =
        some sourceState →
      ∃ targetState,
        Store.lookup
            targetStates
            actorName =
          some targetState ∧
        _root_.Relico.Correctness.MultiStorePayloadRuntimeStateCorresponds
          actorModel.reactiveClass.messageServers
          sourceState
          targetState := by

  induction hCorrespond with

  | nil =>
      intro
        actorName
        actorModel
        sourceState
        hModelLookup
        hSourceLookup

      simp [
        Store.lookup
      ] at hModelLookup

  | cons
      localCorrespondence
      remaining
      inductionHypothesis =>

      rename_i
        candidate
        headModel
        headSourceState
        headTargetState
        remainingModels
        remainingSourceStates
        remainingTargetStates

      intro
        actorName
        actorModel
        sourceState
        hModelLookup
        hSourceLookup

      by_cases hCandidate :
          candidate =
            actorName

      · subst candidate

        have hModelEq :
            headModel =
              actorModel := by

          simpa [
            Store.lookup
          ] using
            hModelLookup

        have hSourceEq :
            headSourceState =
              sourceState := by

          simpa [
            Store.lookup
          ] using
            hSourceLookup

        subst actorModel
        subst sourceState

        exact
          ⟨headTargetState,
           by
             simp [
               Store.lookup
             ],
           localCorrespondence⟩

      · have hRemainingModel :
            Store.lookup
                remainingModels
                actorName =
              some actorModel := by

          simpa [
            Store.lookup,
            hCandidate
          ] using
            hModelLookup

        have hRemainingSource :
            Store.lookup
                remainingSourceStates
                actorName =
              some sourceState := by

          simpa [
            Store.lookup,
            hCandidate
          ] using
            hSourceLookup

        obtain
          ⟨targetState,
           hRemainingTarget,
           hLocalCorrespondence⟩ :=
            inductionHypothesis
              hRemainingModel
              hRemainingSource

        refine
          ⟨targetState,
           ?_,
           hLocalCorrespondence⟩

        simpa [
          Store.lookup,
          hCandidate
        ] using
          hRemainingTarget

/-
Symmetric lookup extraction for a target-selected dispatch.
-/

theorem actorStatesCorrespond_lookup_source
    {models :
      DTR.GlobalMultiStorePayloadActors}
    {sourceStates :
      DTR.GlobalMultiStorePayloadActorStates}
    {targetStates :
      LF.GlobalMultiStorePayloadActorStates}
    (hCorrespond :
      _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
        models
        sourceStates
        targetStates) :
    ∀
      {actorName :
        ActorName}
      {actorModel :
        DTR.MultiStorePayloadModel}
      {targetState :
        LF.MultiStorePayloadState},
      Store.lookup
          models
          actorName =
        some actorModel →
      Store.lookup
          targetStates
          actorName =
        some targetState →
      ∃ sourceState,
        Store.lookup
            sourceStates
            actorName =
          some sourceState ∧
        _root_.Relico.Correctness.MultiStorePayloadRuntimeStateCorresponds
          actorModel.reactiveClass.messageServers
          sourceState
          targetState := by

  induction hCorrespond with

  | nil =>
      intro
        actorName
        actorModel
        targetState
        hModelLookup
        hTargetLookup

      simp [
        Store.lookup
      ] at hModelLookup

  | cons
      localCorrespondence
      remaining
      inductionHypothesis =>

      rename_i
        candidate
        headModel
        headSourceState
        headTargetState
        remainingModels
        remainingSourceStates
        remainingTargetStates

      intro
        actorName
        actorModel
        targetState
        hModelLookup
        hTargetLookup

      by_cases hCandidate :
          candidate =
            actorName

      · subst candidate

        have hModelEq :
            headModel =
              actorModel := by

          simpa [
            Store.lookup
          ] using
            hModelLookup

        have hTargetEq :
            headTargetState =
              targetState := by

          simpa [
            Store.lookup
          ] using
            hTargetLookup

        subst actorModel
        subst targetState

        exact
          ⟨headSourceState,
           by
             simp [
               Store.lookup
             ],
           localCorrespondence⟩

      · have hRemainingModel :
            Store.lookup
                remainingModels
                actorName =
              some actorModel := by

          simpa [
            Store.lookup,
            hCandidate
          ] using
            hModelLookup

        have hRemainingTarget :
            Store.lookup
                remainingTargetStates
                actorName =
              some targetState := by

          simpa [
            Store.lookup,
            hCandidate
          ] using
            hTargetLookup

        obtain
          ⟨sourceState,
           hRemainingSource,
           hLocalCorrespondence⟩ :=
            inductionHypothesis
              hRemainingModel
              hRemainingTarget

        refine
          ⟨sourceState,
           ?_,
           hLocalCorrespondence⟩

        simpa [
          Store.lookup,
          hCandidate
        ] using
          hRemainingSource

/-
Replacing the same declared actor on both sides preserves the complete
pointwise actor-state correspondence.
-/

theorem actorStatesCorrespond_update
    {models :
      DTR.GlobalMultiStorePayloadActors}
    {sourceStates :
      DTR.GlobalMultiStorePayloadActorStates}
    {targetStates :
      LF.GlobalMultiStorePayloadActorStates}
    (hCorrespond :
      _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
        models
        sourceStates
        targetStates) :
    ∀
      {actorName :
        ActorName}
      {actorModel :
        DTR.MultiStorePayloadModel}
      {sourceStateAfter :
        DTR.MultiStorePayloadState}
      {targetStateAfter :
        LF.MultiStorePayloadState},
      Store.lookup
          models
          actorName =
        some actorModel →
      _root_.Relico.Correctness.MultiStorePayloadRuntimeStateCorresponds
          actorModel.reactiveClass.messageServers
          sourceStateAfter
          targetStateAfter →
      _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
        models
        (Store.update
          sourceStates
          actorName
          sourceStateAfter)
        (Store.update
          targetStates
          actorName
          targetStateAfter) := by

  induction hCorrespond with

  | nil =>
      intro
        actorName
        actorModel
        sourceStateAfter
        targetStateAfter
        hModelLookup
        hAfter

      simp [
        Store.lookup
      ] at hModelLookup

  | cons
      localCorrespondence
      remaining
      inductionHypothesis =>

      rename_i
        candidate
        headModel
        headSourceState
        headTargetState
        remainingModels
        remainingSourceStates
        remainingTargetStates

      intro
        actorName
        actorModel
        sourceStateAfter
        targetStateAfter
        hModelLookup
        hAfter

      by_cases hCandidate :
          candidate =
            actorName

      · subst candidate

        have hModelEq :
            headModel =
              actorModel := by

          simpa [
            Store.lookup
          ] using
            hModelLookup

        subst actorModel

        simpa [
          Store.update
        ] using
          (_root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond.cons
            hAfter
            remaining)

      · have hRemainingModel :
            Store.lookup
                remainingModels
                actorName =
              some actorModel := by

          simpa [
            Store.lookup,
            hCandidate
          ] using
            hModelLookup

        have hUpdatedRemaining :
            _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
              remainingModels
              (Store.update
                remainingSourceStates
                actorName
                sourceStateAfter)
              (Store.update
                remainingTargetStates
                actorName
                targetStateAfter) :=
          inductionHypothesis
            hRemainingModel
            hAfter

        simpa [
          Store.update,
          hCandidate
        ] using
          (_root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond.cons
            localCorrespondence
            hUpdatedRemaining)

/-
Compilation maps every successful source actor lookup to the corresponding
target actor-program lookup.
-/

theorem compiledProgram_lookup_of_source_lookup
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {actorName :
      ActorName}
    {actorModel :
      DTR.MultiStorePayloadModel}
    (hCompiled :
      targetProgram.actorPrograms =
        Translation.compileGlobalMultiStorePayloadActors
          sourceModel.actors)
    (hSourceLookup :
      DTR.GlobalMultiStorePayloadModel.lookupActor
          sourceModel
          actorName =
        some actorModel) :
    LF.GlobalMultiStorePayloadProgram.lookupActor
        targetProgram
        actorName =
      some
        (Translation.translateMultiStorePayloadCore
          actorModel) := by

  unfold
    LF.GlobalMultiStorePayloadProgram.lookupActor

  rw [
    hCompiled,
    Translation.lookup_compileGlobalMultiStorePayloadActors
  ]

  change
    Store.lookup
        sourceModel.actors
        actorName =
      some actorModel
    at hSourceLookup

  rw [
    hSourceLookup
  ]

  rfl

/-
A successful lookup in the compiled actor-program store reflects a unique
observable source actor-model lookup and exact local compilation.
-/

theorem source_lookup_of_compiledProgram_lookup
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {actorName :
      ActorName}
    {actorProgram :
      LF.MultiStorePayloadProgram}
    (hCompiled :
      targetProgram.actorPrograms =
        Translation.compileGlobalMultiStorePayloadActors
          sourceModel.actors)
    (hTargetLookup :
      LF.GlobalMultiStorePayloadProgram.lookupActor
          targetProgram
          actorName =
        some actorProgram) :
    ∃ actorModel,
      DTR.GlobalMultiStorePayloadModel.lookupActor
          sourceModel
          actorName =
        some actorModel ∧
      actorProgram =
        Translation.translateMultiStorePayloadCore
          actorModel := by

  have hCompiledLookup :
      Store.lookup
          (Translation.compileGlobalMultiStorePayloadActors
            sourceModel.actors)
          actorName =
        some actorProgram := by

    rw [
      ← hCompiled
    ]

    simpa [
      LF.GlobalMultiStorePayloadProgram.lookupActor
    ] using
      hTargetLookup

  rw [
    Translation.lookup_compileGlobalMultiStorePayloadActors
  ] at hCompiledLookup

  cases hSourceLookup :
      Store.lookup
        sourceModel.actors
        actorName with

  | none =>
      simp [
        hSourceLookup
      ] at hCompiledLookup

  | some actorModel =>
      have hProgramEq :
          Translation.translateMultiStorePayloadCore
              actorModel =
            actorProgram := by

        simpa [
          hSourceLookup
        ] using
          hCompiledLookup

      exact
        ⟨actorModel,
         by
           simpa [
             DTR.GlobalMultiStorePayloadModel.lookupActor
           ] using
             hSourceLookup,
         hProgramEq.symm⟩

/-
Lift one source actor's local payload dispatch into the corresponding target
actor while synchronizing both global clocks with the selected event.
-/

theorem synchronizedGlobalDispatch_forward
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {actorName :
      ActorName}
    {sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadState}
    {targetBefore :
      LF.GlobalMultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hSourceStep :
      DTR.GlobalMultiStorePayloadDispatch.Step
        sourceModel
        actorName
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hGlobal :
      _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore
        targetBefore) :
    ∃ selectedAction targetAfter,
      LF.GlobalMultiStorePayloadDispatch.Step
          targetProgram
          actorName
          targetBefore
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetAfter ∧
        _root_.Relico.Correctness.PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter := by

  cases hSourceStep with

  | lift
      actorModel
      beforeGlobal
      sourceLocalBefore
      sourceLocalAfter
      stepMessage
      stepServer
      hModelLookup
      hSourceStateLookup
      hLocalDispatch =>

      have hModelStoreLookup :
          Store.lookup
              sourceModel.actors
              actorName =
            some actorModel := by

        simpa [
          DTR.GlobalMultiStorePayloadModel.lookupActor
        ] using
          hModelLookup

      have hSourceStateStoreLookup :
          Store.lookup
              sourceBefore.actorStates
              actorName =
            some sourceLocalBefore := by

        simpa [
          DTR.GlobalMultiStorePayloadState.lookupActor
        ] using
          hSourceStateLookup

      obtain
        ⟨targetLocalBefore,
         hTargetStateStoreLookup,
         hLocalBefore⟩ :=
          actorStatesCorrespond_lookup_target
            hGlobal.actorStates
            hModelStoreLookup
            hSourceStateStoreLookup

      have hTargetStateLookup :
          LF.GlobalMultiStorePayloadState.lookupActor
              targetBefore
              actorName =
            some targetLocalBefore := by

        simpa [
          LF.GlobalMultiStorePayloadState.lookupActor
        ] using
          hTargetStateStoreLookup

      obtain
        ⟨selectedAction,
         targetLocalAfter,
         hTargetLocalDispatch,
         hSelectedCorrespondence,
         hLocalAfter⟩ :=
          _root_.Relico.Correctness.multiStorePayload_dispatch_forward_runtime
            hLocalDispatch
            hLocalBefore

      have hTargetProgramLookup :
          LF.GlobalMultiStorePayloadProgram.lookupActor
              targetProgram
              actorName =
            some
              (Translation.translateMultiStorePayloadCore
                actorModel) :=
        compiledProgram_lookup_of_source_lookup
          hGlobal.compiledActorPrograms
          hModelLookup

      have hTargetLocalDispatchForProgram :
          LF.MultiStorePayloadDispatchStep
            (Translation.translateMultiStorePayloadCore
              actorModel).reactor.messageReactions
            targetLocalBefore
            selectedAction
            (Translation.compileMultiStorePayloadReaction
              selectedServer)
            targetLocalAfter := by

        simpa [
          Translation.translateMultiStorePayloadCore,
          Translation.compileMultiStorePayloadReactor,
          Translation.compileMultiStorePayloadMessageReactions
        ] using
          hTargetLocalDispatch

      have hTargetStep :
          LF.GlobalMultiStorePayloadDispatch.Step
            targetProgram
            actorName
            targetBefore
            selectedAction
            (Translation.compileMultiStorePayloadReaction
              selectedServer)
            (LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
              targetBefore
              actorName
              targetLocalAfter) := by

        exact
          LF.GlobalMultiStorePayloadDispatch.Step.lift
            (actorProgram :=
              Translation.translateMultiStorePayloadCore
                actorModel)
            (beforeGlobal :=
              targetBefore)
            (beforeLocal :=
              targetLocalBefore)
            (afterLocal :=
              targetLocalAfter)
            (selectedAction :=
              selectedAction)
            (selectedReaction :=
              Translation.compileMultiStorePayloadReaction
                selectedServer)
            hTargetProgramLookup
            hTargetStateLookup
            hTargetLocalDispatchForProgram

      have hActorStatesAfter :
          _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
            sourceModel.actors
            (Store.update
              sourceBefore.actorStates
              actorName
              sourceLocalAfter)
            (Store.update
              targetBefore.actorStates
              actorName
              targetLocalAfter) :=
        actorStatesCorrespond_update
          hGlobal.actorStates
          hModelStoreLookup
          hLocalAfter

      have hGlobalAfter :
          _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
            sourceModel
            targetProgram
            (DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter
              sourceBefore
              actorName
              sourceLocalAfter)
            (LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
              targetBefore
              actorName
              targetLocalAfter) := by

        refine {
          compiledActorPrograms :=
            hGlobal.compiledActorPrograms

          topology :=
            hGlobal.topology

          currentTime := ?_

          actorStates := ?_
        }

        · simpa [
            DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter,
            LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
          ] using
            hLocalAfter.toStateCorresponds.currentTime.symm

        · change
            _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
              sourceModel.actors
              (Store.update
                sourceBefore.actorStates
                actorName
                sourceLocalAfter)
              (Store.update
                targetBefore.actorStates
                actorName
                targetLocalAfter)

          exact
            hActorStatesAfter

      exact
        ⟨selectedAction,
         LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
           targetBefore
           actorName
           targetLocalAfter,
         hTargetStep,
         hSelectedCorrespondence,
         by
           simpa using
             hGlobalAfter⟩

/-
Lift one target actor's generated local payload dispatch back to the matching
source actor, again synchronizing both global clocks with the selected event.
-/

theorem synchronizedGlobalDispatch_backward
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {actorName :
      ActorName}
    {sourceBefore :
      DTR.GlobalMultiStorePayloadState}
    {targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetStep :
      LF.GlobalMultiStorePayloadDispatch.Step
        targetProgram
        actorName
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hGlobal :
      _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore
        targetBefore) :
    ∃ selectedMessage selectedServer sourceAfter,
      selectedReaction =
          Translation.compileMultiStorePayloadReaction
            selectedServer ∧
        DTR.GlobalMultiStorePayloadDispatch.Step
          sourceModel
          actorName
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter ∧
        _root_.Relico.Correctness.PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter := by

  cases hTargetStep with

  | lift
      actorProgram
      beforeGlobal
      targetLocalBefore
      targetLocalAfter
      stepAction
      stepReaction
      hProgramLookup
      hTargetStateLookup
      hLocalDispatch =>

      obtain
        ⟨actorModel,
         hModelLookup,
         hActorProgramEq⟩ :=
          source_lookup_of_compiledProgram_lookup
            hGlobal.compiledActorPrograms
            hProgramLookup

      subst actorProgram

      have hModelStoreLookup :
          Store.lookup
              sourceModel.actors
              actorName =
            some actorModel := by

        simpa [
          DTR.GlobalMultiStorePayloadModel.lookupActor
        ] using
          hModelLookup

      have hTargetStateStoreLookup :
          Store.lookup
              targetBefore.actorStates
              actorName =
            some targetLocalBefore := by

        simpa [
          LF.GlobalMultiStorePayloadState.lookupActor
        ] using
          hTargetStateLookup

      obtain
        ⟨sourceLocalBefore,
         hSourceStateStoreLookup,
         hLocalBefore⟩ :=
          actorStatesCorrespond_lookup_source
            hGlobal.actorStates
            hModelStoreLookup
            hTargetStateStoreLookup

      have hSourceStateLookup :
          DTR.GlobalMultiStorePayloadState.lookupActor
              sourceBefore
              actorName =
            some sourceLocalBefore := by

        simpa [
          DTR.GlobalMultiStorePayloadState.lookupActor
        ] using
          hSourceStateStoreLookup

      have hTargetLocalDispatchCompiled :
          LF.MultiStorePayloadDispatchStep
            (Translation.compileMultiStorePayloadMessageReactions
              actorModel.reactiveClass.messageServers)
            targetLocalBefore
            selectedAction
            selectedReaction
            targetLocalAfter := by

        simpa [
          Translation.translateMultiStorePayloadCore,
          Translation.compileMultiStorePayloadReactor,
          Translation.compileMultiStorePayloadMessageReactions
        ] using
          hLocalDispatch

      obtain
        ⟨selectedMessage,
         selectedServer,
         sourceLocalAfter,
         hReactionEq,
         hSourceLocalDispatch,
         hSelectedCorrespondence,
         hLocalAfter⟩ :=
          _root_.Relico.Correctness.multiStorePayload_dispatch_backward_runtime
            hTargetLocalDispatchCompiled
            hLocalBefore

      have hSourceStep :
          DTR.GlobalMultiStorePayloadDispatch.Step
            sourceModel
            actorName
            sourceBefore
            selectedMessage
            selectedServer
            (DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter
              sourceBefore
              actorName
              sourceLocalAfter) := by

        exact
          DTR.GlobalMultiStorePayloadDispatch.Step.lift
            (actorModel :=
              actorModel)
            (beforeGlobal :=
              sourceBefore)
            (beforeLocal :=
              sourceLocalBefore)
            (afterLocal :=
              sourceLocalAfter)
            (selectedMessage :=
              selectedMessage)
            (selectedServer :=
              selectedServer)
            hModelLookup
            hSourceStateLookup
            hSourceLocalDispatch

      have hActorStatesAfter :
          _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
            sourceModel.actors
            (Store.update
              sourceBefore.actorStates
              actorName
              sourceLocalAfter)
            (Store.update
              targetBefore.actorStates
              actorName
              targetLocalAfter) :=
        actorStatesCorrespond_update
          hGlobal.actorStates
          hModelStoreLookup
          hLocalAfter

      have hGlobalAfter :
          _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
            sourceModel
            targetProgram
            (DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter
              sourceBefore
              actorName
              sourceLocalAfter)
            (LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
              targetBefore
              actorName
              targetLocalAfter) := by

        refine {
          compiledActorPrograms :=
            hGlobal.compiledActorPrograms

          topology :=
            hGlobal.topology

          currentTime := ?_

          actorStates := ?_
        }

        · simpa [
            DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter,
            LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
          ] using
            hLocalAfter.toStateCorresponds.currentTime.symm

        · change
            _root_.Relico.Correctness.GlobalMultiStorePayloadActorStatesCorrespond
              sourceModel.actors
              (Store.update
                sourceBefore.actorStates
                actorName
                sourceLocalAfter)
              (Store.update
                targetBefore.actorStates
                actorName
                targetLocalAfter)

          exact
            hActorStatesAfter

      exact
        ⟨selectedMessage,
         selectedServer,
         DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter
           sourceBefore
           actorName
           sourceLocalAfter,
         hReactionEq,
         hSourceStep,
         hSelectedCorrespondence,
         by
           simpa using
             hGlobalAfter⟩

end GlobalMultiStorePayloadDispatch
end Correctness
end Relico
