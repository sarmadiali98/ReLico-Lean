/-
Actor-indexed lifting of payload-aware DTR dispatch into a global actor state.

The actor is an explicit relation parameter. Dispatch installs that actor's
local result and synchronizes global metric time with the selected message.
No autonomous global actor-selection policy is introduced.
-/
import Relico.DTR.GlobalMultiStorePayload
import Relico.DTR.MultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace DTR
namespace GlobalMultiStorePayloadDispatch

def synchronizedAfter
    (before :
      DTR.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (afterLocal :
      DTR.MultiStorePayloadState) :
    DTR.GlobalMultiStorePayloadState :=
  {
    DTR.GlobalMultiStorePayloadState.updateActor
      before
      actorName
      afterLocal with

    currentTime :=
      afterLocal.currentTime
  }

theorem localDispatch_after_currentTime
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    after.currentTime =
      selectedMessage.arrivalTime := by

  cases hDispatch

  rfl

theorem synchronizedAfter_currentTime
    (before :
      DTR.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (afterLocal :
      DTR.MultiStorePayloadState) :
    (synchronizedAfter
      before
      actorName
      afterLocal).currentTime =
      afterLocal.currentTime := by
  rfl

@[simp]

theorem synchronizedAfter_lookup_eq
    (before :
      DTR.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (afterLocal :
      DTR.MultiStorePayloadState) :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (synchronizedAfter
          before
          actorName
          afterLocal)
        actorName =
      some afterLocal := by

  change
    DTR.GlobalMultiStorePayloadState.lookupActor
        (DTR.GlobalMultiStorePayloadState.updateActor
          before
          actorName
          afterLocal)
        actorName =
      some afterLocal

  exact
    DTR.GlobalMultiStorePayloadState.lookupActor_update_eq
      before
      actorName
      afterLocal

theorem synchronizedAfter_lookup_ne
    (before :
      DTR.GlobalMultiStorePayloadState)
    (actorName otherActor :
      ActorName)
    (afterLocal :
      DTR.MultiStorePayloadState)
    (hDifferent :
      actorName ≠ otherActor) :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (synchronizedAfter
          before
          actorName
          afterLocal)
        otherActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        before
        otherActor := by

  change
    DTR.GlobalMultiStorePayloadState.lookupActor
        (DTR.GlobalMultiStorePayloadState.updateActor
          before
          actorName
          afterLocal)
        otherActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        before
        otherActor

  exact
    DTR.GlobalMultiStorePayloadState.lookupActor_update_ne
      before
      afterLocal
      hDifferent

inductive Step
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (actorName :
      ActorName) :
    DTR.GlobalMultiStorePayloadState →
    DTR.PendingMessage →
    DTR.MultiStorePayloadMessageServer →
    DTR.GlobalMultiStorePayloadState →
    Prop where

  | lift
      (actorModel :
        DTR.MultiStorePayloadModel)
      (beforeGlobal :
        DTR.GlobalMultiStorePayloadState)
      (beforeLocal afterLocal :
        DTR.MultiStorePayloadState)
      (selectedMessage :
        DTR.PendingMessage)
      (selectedServer :
        DTR.MultiStorePayloadMessageServer)
      (hModelLookup :
        DTR.GlobalMultiStorePayloadModel.lookupActor
            model
            actorName =
          some actorModel)
      (hStateLookup :
        DTR.GlobalMultiStorePayloadState.lookupActor
            beforeGlobal
            actorName =
          some beforeLocal)
      (hLocalDispatch :
        DTR.MultiStorePayloadDispatchStep
          actorModel.reactiveClass.messageServers
          beforeLocal
          selectedMessage
          selectedServer
          afterLocal) :

      Step
        model
        actorName
        beforeGlobal
        selectedMessage
        selectedServer
        (synchronizedAfter
          beforeGlobal
          actorName
          afterLocal)

/-
Temporary target relation for the synchronized actor-indexed global lift.
-/

theorem Step.globalTime_eq_selectedArrival
    {model :
      DTR.GlobalMultiStorePayloadModel}
    {actorName :
      ActorName}
    {before after :
      DTR.GlobalMultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hStep :
      Step
        model
        actorName
        before
        selectedMessage
        selectedServer
        after) :
    after.currentTime =
      selectedMessage.arrivalTime := by

  cases hStep with

  | lift
      actorModel
      beforeGlobal
      beforeLocal
      afterLocal
      selectedMessage
      selectedServer
      hModelLookup
      hStateLookup
      hLocalDispatch =>

      simpa [
        synchronizedAfter
      ] using
        localDispatch_after_currentTime
          hLocalDispatch

theorem Step.unrelatedActor_preserved
    {model :
      DTR.GlobalMultiStorePayloadModel}
    {actorName otherActor :
      ActorName}
    {before after :
      DTR.GlobalMultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hStep :
      Step
        model
        actorName
        before
        selectedMessage
        selectedServer
        after)
    (hDifferent :
      actorName ≠ otherActor) :
    DTR.GlobalMultiStorePayloadState.lookupActor
        after
        otherActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        before
        otherActor := by

  cases hStep with

  | lift
      actorModel
      beforeGlobal
      beforeLocal
      afterLocal
      selectedMessage
      selectedServer
      hModelLookup
      hStateLookup
      hLocalDispatch =>

      exact
        synchronizedAfter_lookup_ne
          before
          actorName
          otherActor
          afterLocal
          hDifferent

end GlobalMultiStorePayloadDispatch
end DTR
end Relico
