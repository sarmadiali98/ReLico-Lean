import Relico.Correctness.GlobalMultiStorePayloadStateCorrespondence
import Relico.Correctness.PayloadCorrespondence
import Relico.Translation.GlobalMultiStorePayloadExternalSend

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Metadata and timing correspondence for one external-send occurrence.
-/
structure GlobalMultiStorePayloadExternalSendOccurrenceCorresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (target :
      LF.GlobalMultiStorePayloadExternalSend.Occurrence) :
    Prop where

  sender :
    target.sender =
      source.sender

  receiver :
    target.receiver =
      source.receiver

  knownRebec :
    target.knownRebec =
      source.knownRebec

  actionName :
    target.actionName =
      Translation.actionNameFor
        source.messageName

  payload :
    target.payload =
      source.payload

  delay :
    target.delay =
      source.delay

  sendTime :
    target.sendTag.time =
      source.sendTime

  arrivalTime :
    target.deliveryTag.time =
      source.arrivalTime

/--
The canonical occurrence translation establishes metadata and metric-time
correspondence.
-/
theorem translated_globalMultiStorePayloadExternalSendOccurrence_corresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (senderTag : LF.Tag)
    (hSendTime :
      senderTag.time =
        source.sendTime)
    (hArrivalTime :
      source.arrivalTime =
        LogicalTime.after
          source.sendTime
          source.delay) :
    GlobalMultiStorePayloadExternalSendOccurrenceCorresponds
      source
      (Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
        source
        senderTag) := by

  refine {
    sender := rfl
    receiver := rfl
    knownRebec := rfl
    actionName := rfl
    payload := rfl
    delay := rfl
    sendTime := hSendTime
    arrivalTime := ?_
  }

  exact
    Translation.translateGlobalMultiStorePayloadExternalSendOccurrence_deliveryTime
      source
      senderTag
      hSendTime
      hArrivalTime

/--
The source pending message and translated LF pending action carry the same
message/action identity, metric arrival time, payload, and occurrence count.
-/
theorem translated_globalMultiStorePayloadExternalSend_pendingPayloadCorresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (senderTag : LF.Tag)
    (hSendTime :
      senderTag.time =
        source.sendTime) :
    PendingPayloadCorresponds
      source.pendingMessage
      (Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
        source
        senderTag).pendingAction := by

  change
    PendingPayloadCorresponds
      (DTR.PendingMessage.scheduleWithPayload
        source.sendTime
        source.messageName
        source.payload
        source.delay)
      (LF.PendingAction.scheduleWithPayload
        senderTag
        (Translation.actionNameFor
          source.messageName)
        source.payload
        source.delay)

  exact
    pendingPayloadCorresponds_scheduleWithPayload
      source.sendTime
      senderTag
      source.messageName
      source.payload
      source.delay
      hSendTime

/--
Appending the translated external-send occurrence preserves the published local
payload-aware runtime-state correspondence for the receiver.
-/
theorem translated_globalMultiStorePayloadExternalSend_receiverStates_correspond
    (sourceOccurrence :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (senderTag : LF.Tag)
    (sourceBefore : DTR.MultiStorePayloadState)
    (targetBefore : LF.MultiStorePayloadState)
    (hStates :
      MultiStorePayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSendTime :
      senderTag.time =
        sourceOccurrence.sendTime) :
    MultiStorePayloadStateCorresponds
      (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        sourceBefore
        sourceOccurrence)
      (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        targetBefore
        (Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
          sourceOccurrence
          senderTag)) := by

  refine {
    currentTime := ?_
    stateStore := ?_
    parameters := ?_
    pendingQueues := ?_
    activeBody := ?_
  }

  · simpa [
      DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter,
      LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
    ] using
      hStates.currentTime

  · simpa [
      DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter,
      LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
    ] using
      hStates.stateStore

  · simpa [
      DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter,
      LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
    ] using
      hStates.parameters

  · change
      PayloadQueueCorresponds
        (sourceBefore.pendingMessages ++
          [DTR.PendingMessage.scheduleWithPayload
            sourceOccurrence.sendTime
            sourceOccurrence.messageName
            sourceOccurrence.payload
            sourceOccurrence.delay])
        (targetBefore.pendingActions ++
          [LF.PendingAction.scheduleWithPayload
            senderTag
            (Translation.actionNameFor
              sourceOccurrence.messageName)
            sourceOccurrence.payload
            sourceOccurrence.delay])

    exact
      payloadQueueCorresponds_append_scheduleWithPayload
        hStates.pendingQueues
        sourceOccurrence.sendTime
        senderTag
        sourceOccurrence.messageName
        sourceOccurrence.payload
        sourceOccurrence.delay
        hSendTime

  · simpa [
      DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter,
      LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
    ] using
      hStates.activeBody

/--
A packaged one-send correspondence witness. It records the actual sender states,
the resolved receiver states, both global updates, and the preserved receiver
state relation. It deliberately contains no global dispatch or actor-priority
claim.
-/
structure GlobalMultiStorePayloadExternalSendCorrespondenceWitness
    (sourceOccurrence :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (targetOccurrence :
      LF.GlobalMultiStorePayloadExternalSend.Occurrence)
    (sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadState)
    (targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState) where

  sourceSenderBefore :
    DTR.MultiStorePayloadState

  targetSenderBefore :
    LF.MultiStorePayloadState

  sourceReceiverBefore :
    DTR.MultiStorePayloadState

  targetReceiverBefore :
    LF.MultiStorePayloadState

  sourceSenderLookup :
    DTR.GlobalMultiStorePayloadState.lookupActor
        sourceBefore
        sourceOccurrence.sender =
      some sourceSenderBefore

  targetSenderLookup :
    LF.GlobalMultiStorePayloadState.lookupActor
        targetBefore
        targetOccurrence.sender =
      some targetSenderBefore

  sourceReceiverLookup :
    DTR.GlobalMultiStorePayloadState.lookupActor
        sourceBefore
        sourceOccurrence.receiver =
      some sourceReceiverBefore

  targetReceiverLookup :
    LF.GlobalMultiStorePayloadState.lookupActor
        targetBefore
        targetOccurrence.receiver =
      some targetReceiverBefore

  senderStates :
    MultiStorePayloadStateCorresponds
      sourceSenderBefore
      targetSenderBefore

  receiverStatesBefore :
    MultiStorePayloadStateCorresponds
      sourceReceiverBefore
      targetReceiverBefore

  sourceSendTime :
    sourceOccurrence.sendTime =
      sourceSenderBefore.currentTime

  occurrence :
    GlobalMultiStorePayloadExternalSendOccurrenceCorresponds
      sourceOccurrence
      targetOccurrence

  sourceAfterDefinition :
    sourceAfter =
      DTR.GlobalMultiStorePayloadState.updateActor
        sourceBefore
        sourceOccurrence.receiver
        (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          sourceReceiverBefore
          sourceOccurrence)

  targetAfterDefinition :
    targetAfter =
      LF.GlobalMultiStorePayloadState.updateActor
        targetBefore
        targetOccurrence.receiver
        (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          targetReceiverBefore
          targetOccurrence)

  receiverStatesAfter :
    MultiStorePayloadStateCorresponds
      (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        sourceReceiverBefore
        sourceOccurrence)
      (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        targetReceiverBefore
        targetOccurrence)

/--
The public one-send correspondence proposition is inhabited exactly when a
fully typed witness packages the sender states, receiver states, occurrence
translation, and both receiver-only global updates.
-/
def GlobalMultiStorePayloadExternalSendCorresponds
    (sourceOccurrence :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (targetOccurrence :
      LF.GlobalMultiStorePayloadExternalSend.Occurrence)
    (sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadState)
    (targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState) :
    Prop :=
  Nonempty
    (GlobalMultiStorePayloadExternalSendCorrespondenceWitness
      sourceOccurrence
      targetOccurrence
      sourceBefore
      sourceAfter
      targetBefore
      targetAfter)

/--
Construct the packaged correspondence for the canonical translation.
-/
theorem translated_globalMultiStorePayloadExternalSend_corresponds
    (sourceOccurrence :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (sourceBefore : DTR.GlobalMultiStorePayloadState)
    (targetBefore : LF.GlobalMultiStorePayloadState)
    (sourceSenderBefore : DTR.MultiStorePayloadState)
    (targetSenderBefore : LF.MultiStorePayloadState)
    (sourceReceiverBefore : DTR.MultiStorePayloadState)
    (targetReceiverBefore : LF.MultiStorePayloadState)
    (hSourceSenderLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          sourceBefore
          sourceOccurrence.sender =
        some sourceSenderBefore)
    (hTargetSenderLookup :
      LF.GlobalMultiStorePayloadState.lookupActor
          targetBefore
          sourceOccurrence.sender =
        some targetSenderBefore)
    (hSourceReceiverLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          sourceBefore
          sourceOccurrence.receiver =
        some sourceReceiverBefore)
    (hTargetReceiverLookup :
      LF.GlobalMultiStorePayloadState.lookupActor
          targetBefore
          sourceOccurrence.receiver =
        some targetReceiverBefore)
    (hSenderStates :
      MultiStorePayloadStateCorresponds
        sourceSenderBefore
        targetSenderBefore)
    (hReceiverStates :
      MultiStorePayloadStateCorresponds
        sourceReceiverBefore
        targetReceiverBefore)
    (hSourceSendTime :
      sourceOccurrence.sendTime =
        sourceSenderBefore.currentTime)
    (hArrivalTime :
      sourceOccurrence.arrivalTime =
        LogicalTime.after
          sourceOccurrence.sendTime
          sourceOccurrence.delay) :
    GlobalMultiStorePayloadExternalSendCorresponds
      sourceOccurrence
      (Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
        sourceOccurrence
        targetSenderBefore.currentTag)
      sourceBefore
      (DTR.GlobalMultiStorePayloadState.updateActor
        sourceBefore
        sourceOccurrence.receiver
        (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          sourceReceiverBefore
          sourceOccurrence))
      targetBefore
      (LF.GlobalMultiStorePayloadState.updateActor
        targetBefore
        sourceOccurrence.receiver
        (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          targetReceiverBefore
          (Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
            sourceOccurrence
            targetSenderBefore.currentTag))) := by

  have hSenderMetricTime :
      targetSenderBefore.currentTag.time =
        sourceOccurrence.sendTime := by
    calc
      targetSenderBefore.currentTag.time =
          sourceSenderBefore.currentTime :=
        hSenderStates.currentTime

      _ =
          sourceOccurrence.sendTime :=
        hSourceSendTime.symm

  refine ⟨{
    sourceSenderBefore :=
      sourceSenderBefore

    targetSenderBefore :=
      targetSenderBefore

    sourceReceiverBefore :=
      sourceReceiverBefore

    targetReceiverBefore :=
      targetReceiverBefore

    sourceSenderLookup :=
      hSourceSenderLookup

    targetSenderLookup := by
      simpa using
        hTargetSenderLookup

    sourceReceiverLookup :=
      hSourceReceiverLookup

    targetReceiverLookup := by
      simpa using
        hTargetReceiverLookup

    senderStates :=
      hSenderStates

    receiverStatesBefore :=
      hReceiverStates

    sourceSendTime :=
      hSourceSendTime

    occurrence := ?_

    sourceAfterDefinition :=
      rfl

    targetAfterDefinition :=
      rfl

    receiverStatesAfter := ?_
  }⟩

  · exact
      translated_globalMultiStorePayloadExternalSendOccurrence_corresponds
        sourceOccurrence
        targetSenderBefore.currentTag
        hSenderMetricTime
        hArrivalTime

  · exact
      translated_globalMultiStorePayloadExternalSend_receiverStates_correspond
        sourceOccurrence
        targetSenderBefore.currentTag
        sourceReceiverBefore
        targetReceiverBefore
        hReceiverStates
        hSenderMetricTime

/--
Updating the receiver preserves every distinct source actor lookup.
-/
theorem globalMultiStorePayloadExternalSend_source_unrelated_preserved
    (state : DTR.GlobalMultiStorePayloadState)
    (receiverState : DTR.MultiStorePayloadState)
    (occurrence :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (otherActor : ActorName)
    (hDifferent :
      occurrence.receiver ≠
        otherActor) :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (DTR.GlobalMultiStorePayloadState.updateActor
          state
          occurrence.receiver
          (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
            receiverState
            occurrence))
        otherActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        state
        otherActor := by

  exact
    DTR.GlobalMultiStorePayloadState.lookupActor_update_ne
      state
      (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        receiverState
        occurrence)
      hDifferent

/--
Updating the receiver preserves every distinct target actor lookup.
-/
theorem globalMultiStorePayloadExternalSend_target_unrelated_preserved
    (state : LF.GlobalMultiStorePayloadState)
    (receiverState : LF.MultiStorePayloadState)
    (occurrence :
      LF.GlobalMultiStorePayloadExternalSend.Occurrence)
    (otherActor : ActorName)
    (hDifferent :
      occurrence.receiver ≠
        otherActor) :
    LF.GlobalMultiStorePayloadState.lookupActor
        (LF.GlobalMultiStorePayloadState.updateActor
          state
          occurrence.receiver
          (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
            receiverState
            occurrence))
        otherActor =
      LF.GlobalMultiStorePayloadState.lookupActor
        state
        otherActor := by

  exact
    LF.GlobalMultiStorePayloadState.lookupActor_update_ne
      state
      (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        receiverState
        occurrence)
      hDifferent

end Correctness
end Relico
