import Relico.DTR.GlobalMultiStorePayloadExternalSend
import Relico.LF.GlobalMultiStorePayloadExternalSend
import Relico.Translation.GlobalMultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Translate one validated source external-send occurrence at the actual sender LF
tag.

The generated action name follows the existing message-to-action translation.
The delivery tag always uses `LF.Tag.schedule`; therefore explicit zero delay
advances the microstep and positive delay advances metric time.
-/
def translateGlobalMultiStorePayloadExternalSendOccurrence
    (source :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (senderTag : LF.Tag) :
    LF.GlobalMultiStorePayloadExternalSend.Occurrence where

  sender :=
    source.sender

  receiver :=
    source.receiver

  knownRebec :=
    source.knownRebec

  actionName :=
    actionNameFor
      source.messageName

  payload :=
    source.payload

  delay :=
    source.delay

  sendTag :=
    senderTag

  deliveryTag :=
    LF.Tag.schedule
      senderTag
      source.delay

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendOccurrence_sender
    (source :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (senderTag : LF.Tag) :
    (translateGlobalMultiStorePayloadExternalSendOccurrence
      source
      senderTag).sender =
      source.sender := by
  rfl

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendOccurrence_receiver
    (source :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (senderTag : LF.Tag) :
    (translateGlobalMultiStorePayloadExternalSendOccurrence
      source
      senderTag).receiver =
      source.receiver := by
  rfl

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendOccurrence_payload
    (source :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (senderTag : LF.Tag) :
    (translateGlobalMultiStorePayloadExternalSendOccurrence
      source
      senderTag).payload =
      source.payload := by
  rfl

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendOccurrence_deliveryTag
    (source :
      DTR.GlobalMultiStorePayloadExternalSend.Occurrence)
    (senderTag : LF.Tag) :
    (translateGlobalMultiStorePayloadExternalSendOccurrence
      source
      senderTag).deliveryTag =
      LF.Tag.schedule
        senderTag
        source.delay := by
  rfl

/--
Metric delivery time agrees with the source arrival time whenever the source
occurrence records sender-time scheduling and the LF sender tag has the same
metric time.
-/
theorem translateGlobalMultiStorePayloadExternalSendOccurrence_deliveryTime
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
    (translateGlobalMultiStorePayloadExternalSendOccurrence
      source
      senderTag).deliveryTag.time =
      source.arrivalTime := by

  calc
    (translateGlobalMultiStorePayloadExternalSendOccurrence
      source
      senderTag).deliveryTag.time =
        LogicalTime.after
          senderTag.time
          source.delay := by
            simp [
              translateGlobalMultiStorePayloadExternalSendOccurrence
            ]

    _ =
        LogicalTime.after
          source.sendTime
          source.delay := by
            rw [hSendTime]

    _ =
        source.arrivalTime :=
          hArrivalTime.symm

end Translation
end Relico
