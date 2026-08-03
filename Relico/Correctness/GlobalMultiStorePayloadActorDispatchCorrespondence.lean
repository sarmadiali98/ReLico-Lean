import Relico.Correctness.GlobalMultiStorePayloadDispatchCorrespondence
import Relico.Correctness.GlobalMultiStorePayloadActorSelectionCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness
namespace GlobalMultiStorePayloadActorDispatchCorrespondence

open DTR.GlobalMultiStorePayloadActorPriority
open LF.GlobalMultiStorePayloadActorOrder
open Translation.GlobalMultiStorePayloadActorOrder
open GlobalMultiStorePayloadActorSelectionCorrespondence

theorem actorPriorityDispatchStep_forward_of_targetBase
    {request :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest}
    {ready :
      List
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor}
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {actorName :
      ActorName}
    {sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hSource :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep
        request
        ready
        sourceModel
        actorName
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hTargetBase :
      LF.GlobalMultiStorePayloadDispatch.Step
        targetProgram
        actorName
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep
      (compileActorPriorityRequest request)
      (compileReadyActors ready)
      targetProgram
      actorName
      targetBefore
      selectedAction
      selectedReaction
      targetAfter := by

  exact
    _root_.Relico.LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep.lift
      (
        actorSelectionEligible_forward
          request
          ready
          actorName
          (
            _root_.Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep.eligible
              hSource
          )
      )
      hTargetBase

theorem actorOrderDispatchStep_backward_of_sourceBase
    {request :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest}
    {ready :
      List
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor}
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {actorName :
      ActorName}
    {sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTarget :
      LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep
        (compileActorPriorityRequest request)
        (compileReadyActors ready)
        targetProgram
        actorName
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hSourceBase :
      DTR.GlobalMultiStorePayloadDispatch.Step
        sourceModel
        actorName
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter) :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep
      request
      ready
      sourceModel
      actorName
      sourceBefore
      selectedMessage
      selectedServer
      sourceAfter := by

  exact
    _root_.Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep.lift
      (
        actorSelectionEligible_backward
          request
          ready
          actorName
          (
            _root_.Relico.LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep.eligible
              hTarget
          )
      )
      hSourceBase

theorem synchronizedActorPriorityDispatch_forward
    {request :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest}
    {ready :
      List
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor}
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
    (hSource :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep
        request
        ready
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
      LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep
          (compileActorPriorityRequest request)
          (compileReadyActors ready)
          targetProgram
          actorName
          targetBefore
          selectedAction
          (_root_.Relico.Translation.compileMultiStorePayloadReaction
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

  obtain
    ⟨selectedAction,
     targetAfter,
     hTargetBase,
     hPending,
     hAfter⟩ :=
      _root_.Relico.Correctness.GlobalMultiStorePayloadDispatch.synchronizedGlobalDispatch_forward
        (
          _root_.Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep.dispatch
            hSource
        )
        hGlobal

  exact
    ⟨selectedAction,
     targetAfter,
     actorPriorityDispatchStep_forward_of_targetBase
       hSource
       hTargetBase,
     hPending,
     hAfter⟩

theorem synchronizedActorPriorityDispatch_backward
    {request :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest}
    {ready :
      List
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor}
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
    (hTarget :
      LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep
        (compileActorPriorityRequest request)
        (compileReadyActors ready)
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
          _root_.Relico.Translation.compileMultiStorePayloadReaction
            selectedServer ∧
        DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep
          request
          ready
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

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hReaction,
     hSourceBase,
     hPending,
     hAfter⟩ :=
      _root_.Relico.Correctness.GlobalMultiStorePayloadDispatch.synchronizedGlobalDispatch_backward
        (
          _root_.Relico.LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep.dispatch
            hTarget
        )
        hGlobal

  exact
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hReaction,
     actorOrderDispatchStep_backward_of_sourceBase
       hTarget
       hSourceBase,
     hPending,
     hAfter⟩



end GlobalMultiStorePayloadActorDispatchCorrespondence
end Correctness
end Relico
