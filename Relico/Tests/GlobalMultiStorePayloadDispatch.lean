import Relico.Correctness.GlobalMultiStorePayloadDispatchCorrespondence
import Relico.Tests.MultiStorePayloadDispatch
import Relico.Tests.GlobalMultiStorePayloadExternalSend

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadDispatch

def dispatchActorModel :
    DTR.MultiStorePayloadModel where

  reactiveClass := {
    _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverReactiveClass with

    messageServers :=
      _root_.Relico.Tests.MultiStorePayloadDispatch.sourceServers
  }

  actor :=
    _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverModel.actor

def sourceGlobalModel :
    DTR.GlobalMultiStorePayloadModel where

  actors := [
    (
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor,
      dispatchActorModel
    ),
    (
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor,
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderModel
    )
  ]

  topology :=
    _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.sourceModel.topology

def sourceGlobalBefore :
    DTR.GlobalMultiStorePayloadState where

  currentTime :=
    _root_.Relico.Tests.MultiStorePayloadDispatch.sourceBefore.currentTime

  actorStates := [
    (
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor,
      _root_.Relico.Tests.MultiStorePayloadDispatch.sourceBefore
    ),
    (
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor,
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderSourceState
    )
  ]

def sourceGlobalAfter :
    DTR.GlobalMultiStorePayloadState :=
  DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter
    sourceGlobalBefore
    _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor
    _root_.Relico.Tests.MultiStorePayloadDispatch.sourceAfter

def dispatchActorProgram :
    LF.MultiStorePayloadProgram :=
  let translated :=
    Translation.translateMultiStorePayloadCore
      dispatchActorModel

  {
    translated with

    reactor := {
      translated.reactor with

      messageReactions :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.targetReactions
    }
  }

def targetGlobalProgram :
    LF.GlobalMultiStorePayloadProgram where

  actorPrograms := [
    (
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor,
      dispatchActorProgram
    ),
    (
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor,
      Translation.translateMultiStorePayloadCore
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderModel
    )
  ]

  topology :=
    sourceGlobalModel.topology

def targetGlobalBefore :
    LF.GlobalMultiStorePayloadState where

  currentTag :=
    _root_.Relico.Tests.MultiStorePayloadDispatch.targetBefore.currentTag

  actorStates := [
    (
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor,
      _root_.Relico.Tests.MultiStorePayloadDispatch.targetBefore
    ),
    (
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor,
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderTargetState
    )
  ]

def targetGlobalAfter :
    LF.GlobalMultiStorePayloadState :=
  LF.GlobalMultiStorePayloadDispatch.synchronizedAfter
    targetGlobalBefore
    _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor
    _root_.Relico.Tests.MultiStorePayloadDispatch.targetAfter

theorem concrete_source_two_actor_dispatch :
    DTR.GlobalMultiStorePayloadDispatch.Step
      sourceGlobalModel
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor
      sourceGlobalBefore
      _root_.Relico.Tests.MultiStorePayloadDispatch.highMessage
      _root_.Relico.Tests.MultiStorePayloadDispatch.highServer
      sourceGlobalAfter := by

  exact
    DTR.GlobalMultiStorePayloadDispatch.Step.lift
      (actorModel := dispatchActorModel)
      (beforeGlobal := sourceGlobalBefore)
      (beforeLocal :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.sourceBefore)
      (afterLocal :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.sourceAfter)
      (selectedMessage :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.highMessage)
      (selectedServer :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.highServer)
      rfl
      rfl
      (by
        simpa [
          dispatchActorModel
        ] using
          _root_.Relico.Tests.MultiStorePayloadDispatch.source_dispatch_fires)

theorem concrete_target_two_actor_dispatch :
    LF.GlobalMultiStorePayloadDispatch.Step
      targetGlobalProgram
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor
      targetGlobalBefore
      _root_.Relico.Tests.MultiStorePayloadDispatch.highAction
      _root_.Relico.Tests.MultiStorePayloadDispatch.highReaction
      targetGlobalAfter := by

  exact
    LF.GlobalMultiStorePayloadDispatch.Step.lift
      (actorProgram := dispatchActorProgram)
      (beforeGlobal := targetGlobalBefore)
      (beforeLocal :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.targetBefore)
      (afterLocal :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.targetAfter)
      (selectedAction :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.highAction)
      (selectedReaction :=
        _root_.Relico.Tests.MultiStorePayloadDispatch.highReaction)
      rfl
      rfl
      (by
        simpa [
          dispatchActorProgram
        ] using
          _root_.Relico.Tests.MultiStorePayloadDispatch.target_dispatch_fires)

theorem concrete_source_selected_actor_installed :
    DTR.GlobalMultiStorePayloadState.lookupActor
        sourceGlobalAfter
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor =
      some
        _root_.Relico.Tests.MultiStorePayloadDispatch.sourceAfter := by

  simpa [
    sourceGlobalAfter
  ] using
    DTR.GlobalMultiStorePayloadDispatch.synchronizedAfter_lookup_eq
      sourceGlobalBefore
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor
      _root_.Relico.Tests.MultiStorePayloadDispatch.sourceAfter

theorem concrete_target_selected_actor_installed :
    LF.GlobalMultiStorePayloadState.lookupActor
        targetGlobalAfter
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor =
      some
        _root_.Relico.Tests.MultiStorePayloadDispatch.targetAfter := by

  simpa [
    targetGlobalAfter
  ] using
    LF.GlobalMultiStorePayloadDispatch.synchronizedAfter_lookup_eq
      targetGlobalBefore
      _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor
      _root_.Relico.Tests.MultiStorePayloadDispatch.targetAfter

theorem concrete_source_unrelated_actor_preserved :
    DTR.GlobalMultiStorePayloadState.lookupActor
        sourceGlobalAfter
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor =
      some
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderSourceState := by

  calc
    DTR.GlobalMultiStorePayloadState.lookupActor
        sourceGlobalAfter
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        sourceGlobalBefore
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor := by

          exact
            DTR.GlobalMultiStorePayloadDispatch.Step.unrelatedActor_preserved
              concrete_source_two_actor_dispatch
              (by decide)

    _ =
      some
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderSourceState := by
          rfl

theorem concrete_target_unrelated_actor_preserved :
    LF.GlobalMultiStorePayloadState.lookupActor
        targetGlobalAfter
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor =
      some
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderTargetState := by

  calc
    LF.GlobalMultiStorePayloadState.lookupActor
        targetGlobalAfter
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor =
      LF.GlobalMultiStorePayloadState.lookupActor
        targetGlobalBefore
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderActor := by

          exact
            LF.GlobalMultiStorePayloadDispatch.Step.unrelatedActor_preserved
              concrete_target_two_actor_dispatch
              (by decide)

    _ =
      some
        _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.senderTargetState := by
          rfl

theorem concrete_source_global_time_is_selected_arrival :
    sourceGlobalAfter.currentTime =
      _root_.Relico.Tests.MultiStorePayloadDispatch.highMessage.arrivalTime := by

  exact
    DTR.GlobalMultiStorePayloadDispatch.Step.globalTime_eq_selectedArrival
      concrete_source_two_actor_dispatch

theorem concrete_target_global_tag_is_selected_tag :
    targetGlobalAfter.currentTag =
      _root_.Relico.Tests.MultiStorePayloadDispatch.highAction.tag := by

  exact
    LF.GlobalMultiStorePayloadDispatch.Step.globalTag_eq_selectedTag
      concrete_target_two_actor_dispatch

theorem concrete_source_payload_binding :
    Option.map
        (fun state => state.parameters)
        (DTR.GlobalMultiStorePayloadState.lookupActor
          sourceGlobalAfter
          _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor) =
      some
        _root_.Relico.Tests.MultiStorePayloadDispatch.boundParameters := by

  rw [
    concrete_source_selected_actor_installed
  ]

  rfl

theorem concrete_target_payload_binding :
    Option.map
        (fun state => state.parameters)
        (LF.GlobalMultiStorePayloadState.lookupActor
          targetGlobalAfter
          _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor) =
      some
        _root_.Relico.Tests.MultiStorePayloadDispatch.boundParameters := by

  rw [
    concrete_target_selected_actor_installed
  ]

  rfl

theorem concrete_source_body_activation :
    Option.map
        (fun state => state.activeBody)
        (DTR.GlobalMultiStorePayloadState.lookupActor
          sourceGlobalAfter
          _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor) =
      some
        _root_.Relico.Tests.MultiStorePayloadDispatch.highServer.body := by

  rw [
    concrete_source_selected_actor_installed
  ]

  rfl

theorem concrete_target_body_activation :
    Option.map
        (fun state => state.activeBody)
        (LF.GlobalMultiStorePayloadState.lookupActor
          targetGlobalAfter
          _root_.Relico.Tests.GlobalMultiStorePayloadExternalSend.receiverActor) =
      some
        _root_.Relico.Tests.MultiStorePayloadDispatch.highReaction.body := by

  rw [
    concrete_target_selected_actor_installed
  ]

  rfl

end GlobalMultiStorePayloadDispatch
end Tests
end Relico
