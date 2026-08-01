import Relico.LF.GlobalMultiStorePayload

set_option autoImplicit false

namespace Relico
namespace LF
namespace GlobalMultiStorePayloadExternalSend

/--
One generated LF-side external-send occurrence.

The complete send tag and delivery tag are retained. For explicit zero delay,
`deliveryTag` is the next microstep at the same metric time.
-/
structure Occurrence where
  sender :
    ActorName

  receiver :
    ActorName

  knownRebec :
    KnownRebecName

  actionName :
    ActionName

  payload :
    Payload

  delay :
    Delay

  sendTag :
    LF.Tag

  deliveryTag :
    LF.Tag

deriving Repr, DecidableEq, BEq, Inhabited

/--
The receiver-local generated trigger occurrence.
-/
def Occurrence.pendingAction
    (occurrence : Occurrence) :
    LF.PendingAction where

  name :=
    occurrence.actionName

  tag :=
    occurrence.deliveryTag

  payload :=
    occurrence.payload

/--
Append exactly one generated occurrence to the receiver queue.
-/
def receiverStateAfter
    (receiverState : LF.MultiStorePayloadState)
    (occurrence : Occurrence) :
    LF.MultiStorePayloadState :=
  {
    receiverState with
    pendingActions :=
      receiverState.pendingActions ++
        [occurrence.pendingAction]
  }

/--
Apply a translated occurrence to a global LF state when the receiver state is
present. No scheduling or dispatch policy is introduced.
-/
def apply?
    (state : LF.GlobalMultiStorePayloadState)
    (occurrence : Occurrence) :
    Option LF.GlobalMultiStorePayloadState :=
  match
      LF.GlobalMultiStorePayloadState.lookupActor
        state
        occurrence.receiver
  with
  | none =>
      none

  | some receiverState =>
      some
        (LF.GlobalMultiStorePayloadState.updateActor
          state
          occurrence.receiver
          (receiverStateAfter
            receiverState
            occurrence))

@[simp]
theorem receiverStateAfter_pendingActions
    (receiverState : LF.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).pendingActions =
      receiverState.pendingActions ++
        [occurrence.pendingAction] := by
  rfl

@[simp]
theorem receiverStateAfter_currentTag
    (receiverState : LF.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).currentTag =
      receiverState.currentTag := by
  rfl

@[simp]
theorem receiverStateAfter_stateStore
    (receiverState : LF.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).stateStore =
      receiverState.stateStore := by
  rfl

@[simp]
theorem receiverStateAfter_parameters
    (receiverState : LF.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).parameters =
      receiverState.parameters := by
  rfl

@[simp]
theorem receiverStateAfter_activeBody
    (receiverState : LF.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).activeBody =
      receiverState.activeBody := by
  rfl

@[simp]
theorem apply?_of_lookup
    (state : LF.GlobalMultiStorePayloadState)
    (occurrence : Occurrence)
    (receiverState : LF.MultiStorePayloadState)
    (hLookup :
      LF.GlobalMultiStorePayloadState.lookupActor
          state
          occurrence.receiver =
        some receiverState) :
    apply?
        state
        occurrence =
      some
        (LF.GlobalMultiStorePayloadState.updateActor
          state
          occurrence.receiver
          (receiverStateAfter
            receiverState
            occurrence)) := by
  simp [apply?, hLookup]

end GlobalMultiStorePayloadExternalSend
end LF
end Relico
