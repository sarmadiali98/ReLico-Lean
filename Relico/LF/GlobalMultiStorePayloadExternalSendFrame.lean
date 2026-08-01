import Relico.LF.GlobalMultiStorePayloadExternalSendStatement

set_option autoImplicit false

namespace Relico
namespace LF
namespace GlobalMultiStorePayloadExternalSendFrame

structure Frame where
  statement :
    LF.GlobalMultiStorePayloadExternalSendStatement.Statement

  remaining :
    LF.MultiStorePayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

def senderStateAfter
    (senderBefore :
      LF.MultiStorePayloadState)
    (frame :
      Frame) :
    LF.MultiStorePayloadState :=
  {
    senderBefore with
    activeBody :=
      frame.remaining
  }

@[simp]
theorem senderStateAfter_currentTag
    (senderBefore :
      LF.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).currentTag =
      senderBefore.currentTag := by
  rfl

@[simp]
theorem senderStateAfter_stateStore
    (senderBefore :
      LF.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).stateStore =
      senderBefore.stateStore := by
  rfl

@[simp]
theorem senderStateAfter_parameters
    (senderBefore :
      LF.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).parameters =
      senderBefore.parameters := by
  rfl

@[simp]
theorem senderStateAfter_pendingActions
    (senderBefore :
      LF.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).pendingActions =
      senderBefore.pendingActions := by
  rfl

@[simp]
theorem senderStateAfter_activeBody
    (senderBefore :
      LF.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).activeBody =
      frame.remaining := by
  rfl

def globalStateAfter
    (receiverUpdated :
      LF.GlobalMultiStorePayloadState)
    (frame :
      Frame)
    (senderBefore :
      LF.MultiStorePayloadState) :
    LF.GlobalMultiStorePayloadState :=
  LF.GlobalMultiStorePayloadState.updateActor
    receiverUpdated
    frame.statement.sender
    (senderStateAfter
      senderBefore
      frame)

def apply?
    (state :
      LF.GlobalMultiStorePayloadState)
    (occurrence :
      LF.GlobalMultiStorePayloadExternalSend.Occurrence)
    (frame :
      Frame) :
    Option LF.GlobalMultiStorePayloadState :=
  match
      LF.GlobalMultiStorePayloadState.lookupActor
        state
        frame.statement.sender
  with
  | none =>
      none

  | some senderBefore =>
      match
          LF.GlobalMultiStorePayloadExternalSend.apply?
            state
            occurrence
      with
      | none =>
          none

      | some receiverUpdated =>
          some
            (globalStateAfter
              receiverUpdated
              frame
              senderBefore)

theorem apply?_of_lookups
    (state :
      LF.GlobalMultiStorePayloadState)
    (occurrence :
      LF.GlobalMultiStorePayloadExternalSend.Occurrence)
    (frame :
      Frame)
    (senderBefore :
      LF.MultiStorePayloadState)
    (receiverBefore :
      LF.MultiStorePayloadState)
    (hSenderLookup :
      LF.GlobalMultiStorePayloadState.lookupActor
          state
          frame.statement.sender =
        some senderBefore)
    (hReceiverLookup :
      LF.GlobalMultiStorePayloadState.lookupActor
          state
          occurrence.receiver =
        some receiverBefore) :
    apply?
        state
        occurrence
        frame =
      some
        (globalStateAfter
          (LF.GlobalMultiStorePayloadState.updateActor
            state
            occurrence.receiver
            (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
              receiverBefore
              occurrence))
          frame
          senderBefore) := by

  simp [
    apply?,
    hSenderLookup,
    LF.GlobalMultiStorePayloadExternalSend.apply?,
    hReceiverLookup
  ]

theorem globalStateAfter_sender
    (receiverUpdated :
      LF.GlobalMultiStorePayloadState)
    (frame :
      Frame)
    (senderBefore :
      LF.MultiStorePayloadState) :
    LF.GlobalMultiStorePayloadState.lookupActor
        (globalStateAfter
          receiverUpdated
          frame
          senderBefore)
        frame.statement.sender =
      some
        (senderStateAfter
          senderBefore
          frame) := by

  exact
    LF.GlobalMultiStorePayloadState.lookupActor_update_eq
      receiverUpdated
      frame.statement.sender
      (senderStateAfter
        senderBefore
        frame)

theorem globalStateAfter_unrelated_preserved
    (receiverUpdated :
      LF.GlobalMultiStorePayloadState)
    (frame :
      Frame)
    (senderBefore :
      LF.MultiStorePayloadState)
    (otherActor :
      ActorName)
    (hDifferent :
      frame.statement.sender ≠
        otherActor) :
    LF.GlobalMultiStorePayloadState.lookupActor
        (globalStateAfter
          receiverUpdated
          frame
          senderBefore)
        otherActor =
      LF.GlobalMultiStorePayloadState.lookupActor
        receiverUpdated
        otherActor := by

  exact
    LF.GlobalMultiStorePayloadState.lookupActor_update_ne
      receiverUpdated
      (senderStateAfter
        senderBefore
        frame)
      hDifferent

@[simp]
theorem globalStateAfter_currentTag
    (receiverUpdated :
      LF.GlobalMultiStorePayloadState)
    (frame :
      Frame)
    (senderBefore :
      LF.MultiStorePayloadState) :
    (globalStateAfter
      receiverUpdated
      frame
      senderBefore).currentTag =
      receiverUpdated.currentTag := by
  rfl

end GlobalMultiStorePayloadExternalSendFrame
end LF
end Relico
