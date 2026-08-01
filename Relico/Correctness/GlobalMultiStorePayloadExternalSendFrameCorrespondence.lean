import Relico.Correctness.GlobalMultiStorePayloadExternalSendStatementCorrespondence
import Relico.Translation.GlobalMultiStorePayloadExternalSendFrame

set_option autoImplicit false

namespace Relico
namespace Correctness

structure GlobalMultiStorePayloadExternalSendFrameCorresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame)
    (target :
      LF.GlobalMultiStorePayloadExternalSendFrame.Frame) :
    Prop where

  statement :
    GlobalMultiStorePayloadExternalSendStatementCorresponds
      source.statement
      target.statement

  remaining :
    target.remaining =
      Translation.compileMultiStorePayloadBody
        source.remaining

theorem translated_globalMultiStorePayloadExternalSendFrame_corresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame) :
    GlobalMultiStorePayloadExternalSendFrameCorresponds
      source
      (Translation.translateGlobalMultiStorePayloadExternalSendFrame
        source) := by

  exact {
    statement :=
      translated_globalMultiStorePayloadExternalSendStatement_corresponds
        source.statement

    remaining :=
      rfl
  }

theorem translated_globalMultiStorePayloadExternalSendFrame_senderAfter_corresponds
    (sourceFrame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame)
    (sourceSenderBefore :
      DTR.MultiStorePayloadState)
    (targetSenderBefore :
      LF.MultiStorePayloadState)
    (hStates :
      MultiStorePayloadStateCorresponds
        sourceSenderBefore
        targetSenderBefore) :
    MultiStorePayloadStateCorresponds
      (DTR.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
        sourceSenderBefore
        sourceFrame)
      (LF.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
        targetSenderBefore
        (Translation.translateGlobalMultiStorePayloadExternalSendFrame
          sourceFrame)) := by

  refine {
    currentTime :=
      hStates.currentTime

    stateStore :=
      hStates.stateStore

    parameters :=
      hStates.parameters

    pendingQueues :=
      hStates.pendingQueues

    activeBody := ?_
  }

  rfl

def translatedGlobalMultiStorePayloadExternalSendFrameOccurrence
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (targetSenderBefore :
      LF.MultiStorePayloadState) :
    LF.GlobalMultiStorePayloadExternalSend.Occurrence :=
  Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
    foundation.occurrence
    targetSenderBefore.currentTag

def translatedGlobalMultiStorePayloadExternalSendFrameReceiverUpdated
    (targetBefore :
      LF.GlobalMultiStorePayloadState)
    (targetReceiverBefore :
      LF.MultiStorePayloadState)
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (targetSenderBefore :
      LF.MultiStorePayloadState) :
    LF.GlobalMultiStorePayloadState :=
  LF.GlobalMultiStorePayloadState.updateActor
    targetBefore
    foundation.occurrence.receiver
    (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
      targetReceiverBefore
      (translatedGlobalMultiStorePayloadExternalSendFrameOccurrence
        foundation
        targetSenderBefore))

def globalMultiStorePayloadExternalSendFrameSourceAfter
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (sourceFrame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame)
    (sourceSenderBefore :
      DTR.MultiStorePayloadState) :
    DTR.GlobalMultiStorePayloadState :=
  DTR.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter
    foundation
    sourceFrame
    sourceSenderBefore

def globalMultiStorePayloadExternalSendFrameTargetAfter
    (targetBefore :
      LF.GlobalMultiStorePayloadState)
    (targetReceiverBefore :
      LF.MultiStorePayloadState)
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (sourceFrame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame)
    (targetSenderBefore :
      LF.MultiStorePayloadState) :
    LF.GlobalMultiStorePayloadState :=
  LF.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter
    (translatedGlobalMultiStorePayloadExternalSendFrameReceiverUpdated
      targetBefore
      targetReceiverBefore
      foundation
      targetSenderBefore)
    (Translation.translateGlobalMultiStorePayloadExternalSendFrame
      sourceFrame)
    targetSenderBefore

structure GlobalMultiStorePayloadExternalSendFrameTransitionWitness
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (sourceBefore :
      DTR.GlobalMultiStorePayloadState)
    (targetBefore :
      LF.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (sourceFrame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame)
    (payload :
      Payload)
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (sourceSenderBefore :
      DTR.MultiStorePayloadState)
    (targetSenderBefore :
      LF.MultiStorePayloadState)
    (targetReceiverBefore :
      LF.MultiStorePayloadState) :
    Prop where

  frame :
    GlobalMultiStorePayloadExternalSendFrameCorresponds
      sourceFrame
      (Translation.translateGlobalMultiStorePayloadExternalSendFrame
        sourceFrame)

  sourceExecution :
    DTR.GlobalMultiStorePayloadExternalSendFrame.attempt
        model
        sourceBefore
        history
        sourceFrame =
      .ok
        (DTR.GlobalMultiStorePayloadExternalSendFrame.makeSuccess
          foundation
          sourceSenderBefore
          sourceFrame)

  targetExecution :
    LF.GlobalMultiStorePayloadExternalSendFrame.apply?
        targetBefore
        (translatedGlobalMultiStorePayloadExternalSendFrameOccurrence
          foundation
          targetSenderBefore)
        (Translation.translateGlobalMultiStorePayloadExternalSendFrame
          sourceFrame) =
      some
        (globalMultiStorePayloadExternalSendFrameTargetAfter
          targetBefore
          targetReceiverBefore
          foundation
          sourceFrame
          targetSenderBefore)

  senderStatesAfter :
    MultiStorePayloadStateCorresponds
      (DTR.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
        sourceSenderBefore
        sourceFrame)
      (LF.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
        targetSenderBefore
        (Translation.translateGlobalMultiStorePayloadExternalSendFrame
          sourceFrame))

  sourceSenderInstalled :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (globalMultiStorePayloadExternalSendFrameSourceAfter
          foundation
          sourceFrame
          sourceSenderBefore)
        sourceFrame.statement.sender =
      some
        (DTR.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
          sourceSenderBefore
          sourceFrame)

  targetSenderInstalled :
    LF.GlobalMultiStorePayloadState.lookupActor
        (globalMultiStorePayloadExternalSendFrameTargetAfter
          targetBefore
          targetReceiverBefore
          foundation
          sourceFrame
          targetSenderBefore)
        sourceFrame.statement.sender =
      some
        (LF.GlobalMultiStorePayloadExternalSendFrame.senderStateAfter
          targetSenderBefore
          (Translation.translateGlobalMultiStorePayloadExternalSendFrame
            sourceFrame))

  sourceReceiverPreserved :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (globalMultiStorePayloadExternalSendFrameSourceAfter
          foundation
          sourceFrame
          sourceSenderBefore)
        foundation.occurrence.receiver =
      DTR.GlobalMultiStorePayloadState.lookupActor
        foundation.state
        foundation.occurrence.receiver

  targetReceiverInstalled :
    LF.GlobalMultiStorePayloadState.lookupActor
        (globalMultiStorePayloadExternalSendFrameTargetAfter
          targetBefore
          targetReceiverBefore
          foundation
          sourceFrame
          targetSenderBefore)
        foundation.occurrence.receiver =
      some
        (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          targetReceiverBefore
          (translatedGlobalMultiStorePayloadExternalSendFrameOccurrence
            foundation
            targetSenderBefore))

  historyResult :
    foundation.history =
      history ++
        [foundation.occurrence.key]

theorem translated_globalMultiStorePayloadExternalSendFrame_transition
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (sourceBefore :
      DTR.GlobalMultiStorePayloadState)
    (targetBefore :
      LF.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (sourceFrame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame)
    (payload :
      Payload)
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (sourceSenderBefore :
      DTR.MultiStorePayloadState)
    (targetSenderBefore :
      LF.MultiStorePayloadState)
    (targetReceiverBefore :
      LF.MultiStorePayloadState)
    (hSourceSenderLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          sourceBefore
          sourceFrame.statement.sender =
        some sourceSenderBefore)
    (hTargetSenderLookup :
      LF.GlobalMultiStorePayloadState.lookupActor
          targetBefore
          sourceFrame.statement.sender =
        some targetSenderBefore)
    (hTargetReceiverLookup :
      LF.GlobalMultiStorePayloadState.lookupActor
          targetBefore
          foundation.occurrence.receiver =
        some targetReceiverBefore)
    (hSenderStates :
      MultiStorePayloadStateCorresponds
        sourceSenderBefore
        targetSenderBefore)
    (hStatement :
      DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
          model
          sourceBefore
          history
          sourceFrame.statement =
        .ok foundation)
    (hFoundation :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          sourceBefore
          history
          (sourceFrame.statement.toRequest payload) =
        .ok foundation) :
    GlobalMultiStorePayloadExternalSendFrameTransitionWitness
      model
      sourceBefore
      targetBefore
      history
      sourceFrame
      payload
      foundation
      sourceSenderBefore
      targetSenderBefore
      targetReceiverBefore := by

  have hReceiverNeSender :
      foundation.occurrence.receiver ≠
        sourceFrame.statement.sender := by

    simpa using
      DTR.GlobalMultiStorePayloadExternalSend.attempt_success_receiver_ne_sender
        model
        sourceBefore
        history
        (sourceFrame.statement.toRequest payload)
        foundation
        hFoundation

  have hSenderNeReceiver :
      sourceFrame.statement.sender ≠
        foundation.occurrence.receiver := by

    exact
      fun hSenderEqReceiver =>
        hReceiverNeSender
          hSenderEqReceiver.symm

  have hTargetSenderNeReceiver :
      (Translation.translateGlobalMultiStorePayloadExternalSendFrame
        sourceFrame).statement.sender ≠
        foundation.occurrence.receiver := by

    change
      sourceFrame.statement.sender ≠
        foundation.occurrence.receiver

    exact
      hSenderNeReceiver

  refine {
    frame :=
      translated_globalMultiStorePayloadExternalSendFrame_corresponds
        sourceFrame

    sourceExecution :=
      DTR.GlobalMultiStorePayloadExternalSendFrame.attempt_of_statement_success
        model
        sourceBefore
        history
        sourceFrame
        sourceSenderBefore
        foundation
        hSourceSenderLookup
        hStatement

    targetExecution := ?_

    senderStatesAfter :=
      translated_globalMultiStorePayloadExternalSendFrame_senderAfter_corresponds
        sourceFrame
        sourceSenderBefore
        targetSenderBefore
        hSenderStates

    sourceSenderInstalled := ?_

    targetSenderInstalled := ?_

    sourceReceiverPreserved := ?_

    targetReceiverInstalled := ?_

    historyResult :=
      DTR.GlobalMultiStorePayloadExternalSend.attempt_success_history
        model
        sourceBefore
        history
        (sourceFrame.statement.toRequest payload)
        foundation
        hFoundation
  }

  · simpa [
      globalMultiStorePayloadExternalSendFrameTargetAfter,
      translatedGlobalMultiStorePayloadExternalSendFrameReceiverUpdated,
      translatedGlobalMultiStorePayloadExternalSendFrameOccurrence,
      Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
    ] using
      LF.GlobalMultiStorePayloadExternalSendFrame.apply?_of_lookups
        targetBefore
        (translatedGlobalMultiStorePayloadExternalSendFrameOccurrence
          foundation
          targetSenderBefore)
        (Translation.translateGlobalMultiStorePayloadExternalSendFrame
          sourceFrame)
        targetSenderBefore
        targetReceiverBefore
        (by
          change
            LF.GlobalMultiStorePayloadState.lookupActor
                targetBefore
                sourceFrame.statement.sender =
              some targetSenderBefore

          exact
            hTargetSenderLookup)
        (by
          change
            LF.GlobalMultiStorePayloadState.lookupActor
                targetBefore
                foundation.occurrence.receiver =
              some targetReceiverBefore

          exact
            hTargetReceiverLookup)

  · simpa [
      globalMultiStorePayloadExternalSendFrameSourceAfter
    ] using
      DTR.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter_sender
        foundation
        sourceFrame
        sourceSenderBefore

  · simpa [
      globalMultiStorePayloadExternalSendFrameTargetAfter
    ] using
      LF.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter_sender
        (translatedGlobalMultiStorePayloadExternalSendFrameReceiverUpdated
          targetBefore
          targetReceiverBefore
          foundation
          targetSenderBefore)
        (Translation.translateGlobalMultiStorePayloadExternalSendFrame
          sourceFrame)
        targetSenderBefore

  · simpa [
      globalMultiStorePayloadExternalSendFrameSourceAfter
    ] using
      DTR.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter_receiver_preserved
        model
        sourceBefore
        history
        sourceFrame
        payload
        foundation
        sourceSenderBefore
        hFoundation

  · calc
      LF.GlobalMultiStorePayloadState.lookupActor
          (globalMultiStorePayloadExternalSendFrameTargetAfter
            targetBefore
            targetReceiverBefore
            foundation
            sourceFrame
            targetSenderBefore)
          foundation.occurrence.receiver =
        LF.GlobalMultiStorePayloadState.lookupActor
          (translatedGlobalMultiStorePayloadExternalSendFrameReceiverUpdated
            targetBefore
            targetReceiverBefore
            foundation
            targetSenderBefore)
          foundation.occurrence.receiver := by

            exact
              LF.GlobalMultiStorePayloadExternalSendFrame.globalStateAfter_unrelated_preserved
                (translatedGlobalMultiStorePayloadExternalSendFrameReceiverUpdated
                  targetBefore
                  targetReceiverBefore
                  foundation
                  targetSenderBefore)
                (Translation.translateGlobalMultiStorePayloadExternalSendFrame
                  sourceFrame)
                targetSenderBefore
                foundation.occurrence.receiver
                hTargetSenderNeReceiver

      _ =
        some
          (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
            targetReceiverBefore
            (translatedGlobalMultiStorePayloadExternalSendFrameOccurrence
              foundation
              targetSenderBefore)) := by

            exact
              LF.GlobalMultiStorePayloadState.lookupActor_update_eq
                targetBefore
                foundation.occurrence.receiver
                (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
                  targetReceiverBefore
                  (translatedGlobalMultiStorePayloadExternalSendFrameOccurrence
                    foundation
                    targetSenderBefore))

end Correctness
end Relico
