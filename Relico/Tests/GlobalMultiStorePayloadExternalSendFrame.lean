import Relico.Correctness.GlobalMultiStorePayloadExternalSendFrameCorrespondence
import Relico.Tests.GlobalMultiStorePayloadExternalSendStatement

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadExternalSendFrame

open Relico.Tests.GlobalMultiStorePayloadExternalSend
open Relico.Tests.GlobalMultiStorePayloadExternalSendStatement

def continuationVariable :
    VarName :=
  ⟨"continuationValue"⟩

def sourceContinuation :
    DTR.MultiStorePayloadBody :=
  [
    .assign
      continuationVariable
      (.intLiteral 11)
  ]

def positiveFrame :
    DTR.GlobalMultiStorePayloadExternalSendFrame.Frame where

  statement :=
    positiveStatement

  remaining :=
    sourceContinuation

def positiveTargetFrame :
    LF.GlobalMultiStorePayloadExternalSendFrame.Frame :=
  Translation.translateGlobalMultiStorePayloadExternalSendFrame
    positiveFrame

def positiveFrameSuccess :
    DTR.GlobalMultiStorePayloadExternalSendFrame.Success :=
  DTR.GlobalMultiStorePayloadExternalSendFrame.makeSuccess
    positiveExpectedSuccess
    senderSourceState
    positiveFrame

theorem positive_frame_translation_is_exact :
    positiveTargetFrame.statement =
        positiveTargetStatement ∧
      positiveTargetFrame.remaining =
        Translation.compileMultiStorePayloadBody
          sourceContinuation := by
  exact ⟨rfl, rfl⟩

theorem positive_frame_attempt_succeeds :
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt
        sourceModel
        sourceState
        []
        positiveFrame =
      .ok positiveFrameSuccess := by

  exact
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt_of_statement_success
      sourceModel
      sourceState
      []
      positiveFrame
      senderSourceState
      positiveExpectedSuccess
      rfl
      positive_adapter_attempt_succeeds

theorem positive_source_sender_continuation_installed :
    DTR.GlobalMultiStorePayloadState.lookupActor
        positiveFrameSuccess.state
        senderActor =
      some
        (DTR.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
          senderSourceState
          positiveFrame) := by

  exact
    DTR.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter_sender
      positiveExpectedSuccess
      positiveFrame
      senderSourceState

theorem positive_source_sender_queue_is_unchanged :
    (DTR.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
      senderSourceState
      positiveFrame).pendingMessages =
      senderSourceState.pendingMessages := by
  rfl

theorem positive_source_receiver_update_survives :
    DTR.GlobalMultiStorePayloadState.lookupActor
        positiveFrameSuccess.state
        receiverActor =
      some
        (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          receiverSourceState
          positiveSourceOccurrence) := by

  calc
    DTR.GlobalMultiStorePayloadState.lookupActor
        positiveFrameSuccess.state
        receiverActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        positiveExpectedSuccess.state
        receiverActor := by

          exact
            DTR.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter_receiver_preserved
              sourceModel
              sourceState
              []
              positiveFrame
              [7]
              positiveExpectedSuccess
              senderSourceState
              rfl

    _ =
      some
        (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          receiverSourceState
          positiveSourceOccurrence) := by
        rfl

theorem positive_target_frame_applies :
    LF.GlobalMultiStorePayloadExternalSendFrame.apply?
        targetState
        positiveTargetOccurrence
        positiveTargetFrame =
      some
        (LF.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter
          (LF.GlobalMultiStorePayloadState.updateActor
            targetState
            receiverActor
            (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
              receiverTargetState
              positiveTargetOccurrence))
          positiveTargetFrame
          senderTargetState) := by

  exact
    LF.GlobalMultiStorePayloadExternalSendFrame.apply?_of_lookups
      targetState
      positiveTargetOccurrence
      positiveTargetFrame
      senderTargetState
      receiverTargetState
      rfl
      rfl

theorem positive_target_sender_continuation_installed :
    LF.GlobalMultiStorePayloadState.lookupActor
        (LF.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter
          (LF.GlobalMultiStorePayloadState.updateActor
            targetState
            receiverActor
            (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
              receiverTargetState
              positiveTargetOccurrence))
          positiveTargetFrame
          senderTargetState)
        senderActor =
      some
        (LF.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
          senderTargetState
          positiveTargetFrame) := by

  exact
    LF.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter_sender
      (LF.GlobalMultiStorePayloadState.updateActor
        targetState
        receiverActor
        (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          receiverTargetState
          positiveTargetOccurrence))
      positiveTargetFrame
      senderTargetState

theorem positive_sender_states_after_correspond :
    Correctness.MultiStorePayloadStateCorresponds
      (DTR.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
        senderSourceState
        positiveFrame)
      (LF.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
        senderTargetState
        positiveTargetFrame) := by

  exact
    Correctness.translated_globalMultiStorePayloadExternalSendFrame_senderAfter_corresponds
      positiveFrame
      senderSourceState
      senderTargetState
      senderStatesCorrespond

theorem positive_frame_transition_corresponds :
    Correctness.GlobalMultiStorePayloadExternalSendFrameTransitionWitness
      sourceModel
      sourceState
      targetState
      []
      positiveFrame
      [7]
      positiveExpectedSuccess
      senderSourceState
      senderTargetState
      receiverTargetState := by

  exact
    Correctness.translated_globalMultiStorePayloadExternalSendFrame_transition
      sourceModel
      sourceState
      targetState
      []
      positiveFrame
      [7]
      positiveExpectedSuccess
      senderSourceState
      senderTargetState
      receiverTargetState
      rfl
      rfl
      rfl
      senderStatesCorrespond
      positive_adapter_attempt_succeeds
      rfl

theorem positive_frame_history_is_unique :
    DTR.GlobalMultiStorePayloadExternalSend.HistoryUnique
      positiveFrameSuccess.foundation.history := by

  exact
    positive_success_history_unique

def zeroDelayFrame :
    DTR.GlobalMultiStorePayloadExternalSendFrame.Frame where

  statement :=
    zeroDelayStatement

  remaining :=
    sourceContinuation

def zeroDelayTargetFrame :
    LF.GlobalMultiStorePayloadExternalSendFrame.Frame :=
  Translation.translateGlobalMultiStorePayloadExternalSendFrame
    zeroDelayFrame

def zeroDelayFoundation :
    DTR.GlobalMultiStorePayloadExternalSend.Success where

  occurrence :=
    zeroSourceOccurrence

  state :=
    DTR.GlobalMultiStorePayloadState.updateActor
      sourceState
      receiverActor
      (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        receiverSourceState
        zeroSourceOccurrence)

  history :=
    [
      zeroSourceOccurrence.key
    ]

theorem zero_delay_statement_attempt_succeeds :
    DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
        sourceModel
        sourceState
        []
        zeroDelayStatement =
      .ok zeroDelayFoundation := by
  rfl

theorem zero_delay_frame_attempt_succeeds :
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt
        sourceModel
        sourceState
        []
        zeroDelayFrame =
      .ok
        (DTR.GlobalMultiStorePayloadExternalSendFrame.makeSuccess
          zeroDelayFoundation
          senderSourceState
          zeroDelayFrame) := by

  exact
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt_of_statement_success
      sourceModel
      sourceState
      []
      zeroDelayFrame
      senderSourceState
      zeroDelayFoundation
      rfl
      zero_delay_statement_attempt_succeeds

theorem zero_delay_target_frame_applies :
    LF.GlobalMultiStorePayloadExternalSendFrame.apply?
        targetState
        zeroTargetOccurrence
        zeroDelayTargetFrame =
      some
        (LF.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter
          (LF.GlobalMultiStorePayloadState.updateActor
            targetState
            receiverActor
            (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
              receiverTargetState
              zeroTargetOccurrence))
          zeroDelayTargetFrame
          senderTargetState) ∧
      zeroTargetOccurrence.deliveryTag =
        {
          time := 5
          microstep := 5
        } := by

  constructor

  · exact
      LF.GlobalMultiStorePayloadExternalSendFrame.apply?_of_lookups
        targetState
        zeroTargetOccurrence
        zeroDelayTargetFrame
        senderTargetState
        receiverTargetState
        rfl
        rfl

  · exact
      explicit_zero_delay_target_tag

def failedEvaluationFrame :
    DTR.GlobalMultiStorePayloadExternalSendFrame.Frame where

  statement :=
    failedEvaluationStatement

  remaining :=
    sourceContinuation

theorem payload_evaluation_failure_performs_no_transition :
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt
        sourceModel
        sourceState
        []
        failedEvaluationFrame =
      .error .payloadEvaluationFailed := by

  exact
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt_of_statement_failure
      sourceModel
      sourceState
      []
      failedEvaluationFrame
      senderSourceState
      .payloadEvaluationFailed
      rfl
      failed_payload_evaluation_is_rejected

theorem duplicate_collision_performs_no_transition :
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt
        sourceModel
        sourceState
        [positiveSourceOccurrence.key]
        positiveFrame =
      .error
        (.foundation
          .duplicateSameEdgeTime) := by
  rfl

theorem self_resolution_performs_no_transition :
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt
        selfGlobalModel
        selfGlobalState
        []
        positiveFrame =
      .error
        (.foundation
          .selfSendNotExternal) := by
  rfl

def unrelatedActor :
    ActorName :=
  ⟨"unrelated"⟩

theorem arbitrary_unrelated_actor_is_preserved :
    DTR.GlobalMultiStorePayloadState.lookupActor
        positiveFrameSuccess.state
        unrelatedActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        positiveExpectedSuccess.state
        unrelatedActor := by

  exact
    DTR.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter_unrelated_preserved
      positiveExpectedSuccess
      positiveFrame
      senderSourceState
      unrelatedActor
      (by decide)

end GlobalMultiStorePayloadExternalSendFrame
end Tests
end Relico
