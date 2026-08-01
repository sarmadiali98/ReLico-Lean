/-
Actor-indexed lifting of generated LF payload dispatch into a global actor
state.

The actor is an explicit relation parameter. Dispatch installs that actor's
local result and synchronizes the complete global tag with the selected action.
No autonomous global actor-selection policy is introduced.
-/
import Relico.LF.GlobalMultiStorePayload
import Relico.LF.MultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace LF
namespace GlobalMultiStorePayloadDispatch

def synchronizedAfter
    (before :
      LF.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (afterLocal :
      LF.MultiStorePayloadState) :
    LF.GlobalMultiStorePayloadState :=
  {
    LF.GlobalMultiStorePayloadState.updateActor
      before
      actorName
      afterLocal with

    currentTag :=
      afterLocal.currentTag
  }

@[simp]

theorem localDispatch_after_currentTag
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hDispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    after.currentTag =
      selectedAction.tag := by

  cases hDispatch

  rfl

/-
Preserving the global source clock is coherent only when the selected event
already occurs at the global clock.
-/

theorem synchronizedAfter_currentTag
    (before :
      LF.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (afterLocal :
      LF.MultiStorePayloadState) :
    (synchronizedAfter
      before
      actorName
      afterLocal).currentTag =
      afterLocal.currentTag := by
  rfl

theorem synchronizedAfter_lookup_eq
    (before :
      LF.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (afterLocal :
      LF.MultiStorePayloadState) :
    LF.GlobalMultiStorePayloadState.lookupActor
        (synchronizedAfter
          before
          actorName
          afterLocal)
        actorName =
      some afterLocal := by

  change
    LF.GlobalMultiStorePayloadState.lookupActor
        (LF.GlobalMultiStorePayloadState.updateActor
          before
          actorName
          afterLocal)
        actorName =
      some afterLocal

  exact
    LF.GlobalMultiStorePayloadState.lookupActor_update_eq
      before
      actorName
      afterLocal

theorem synchronizedAfter_lookup_ne
    (before :
      LF.GlobalMultiStorePayloadState)
    (actorName otherActor :
      ActorName)
    (afterLocal :
      LF.MultiStorePayloadState)
    (hDifferent :
      actorName ≠ otherActor) :
    LF.GlobalMultiStorePayloadState.lookupActor
        (synchronizedAfter
          before
          actorName
          afterLocal)
        otherActor =
      LF.GlobalMultiStorePayloadState.lookupActor
        before
        otherActor := by

  change
    LF.GlobalMultiStorePayloadState.lookupActor
        (LF.GlobalMultiStorePayloadState.updateActor
          before
          actorName
          afterLocal)
        otherActor =
      LF.GlobalMultiStorePayloadState.lookupActor
        before
        otherActor

  exact
    LF.GlobalMultiStorePayloadState.lookupActor_update_ne
      before
      afterLocal
      hDifferent

/-
Synchronizing both global clocks preserves metric-time agreement supplied by
the existing local runtime correspondence.
-/

inductive Step
    (program :
      LF.GlobalMultiStorePayloadProgram)
    (actorName :
      ActorName) :
    LF.GlobalMultiStorePayloadState →
    LF.PendingAction →
    LF.MultiStorePayloadReaction →
    LF.GlobalMultiStorePayloadState →
    Prop where

  | lift
      (actorProgram :
        LF.MultiStorePayloadProgram)
      (beforeGlobal :
        LF.GlobalMultiStorePayloadState)
      (beforeLocal afterLocal :
        LF.MultiStorePayloadState)
      (selectedAction :
        LF.PendingAction)
      (selectedReaction :
        LF.MultiStorePayloadReaction)
      (hProgramLookup :
        LF.GlobalMultiStorePayloadProgram.lookupActor
            program
            actorName =
          some actorProgram)
      (hStateLookup :
        LF.GlobalMultiStorePayloadState.lookupActor
            beforeGlobal
            actorName =
          some beforeLocal)
      (hLocalDispatch :
        LF.MultiStorePayloadDispatchStep
          actorProgram.reactor.messageReactions
          beforeLocal
          selectedAction
          selectedReaction
          afterLocal) :

      Step
        program
        actorName
        beforeGlobal
        selectedAction
        selectedReaction
        (synchronizedAfter
          beforeGlobal
          actorName
          afterLocal)

theorem Step.globalTag_eq_selectedTag
    {program :
      LF.GlobalMultiStorePayloadProgram}
    {actorName :
      ActorName}
    {before after :
      LF.GlobalMultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hStep :
      Step
        program
        actorName
        before
        selectedAction
        selectedReaction
        after) :
    after.currentTag =
      selectedAction.tag := by

  cases hStep with

  | lift
      actorProgram
      beforeGlobal
      beforeLocal
      afterLocal
      selectedAction
      selectedReaction
      hProgramLookup
      hStateLookup
      hLocalDispatch =>

      simpa [
        synchronizedAfter
      ] using
        localDispatch_after_currentTag
          hLocalDispatch

theorem Step.unrelatedActor_preserved
    {program :
      LF.GlobalMultiStorePayloadProgram}
    {actorName otherActor :
      ActorName}
    {before after :
      LF.GlobalMultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hStep :
      Step
        program
        actorName
        before
        selectedAction
        selectedReaction
        after)
    (hDifferent :
      actorName ≠ otherActor) :
    LF.GlobalMultiStorePayloadState.lookupActor
        after
        otherActor =
      LF.GlobalMultiStorePayloadState.lookupActor
        before
        otherActor := by

  cases hStep with

  | lift
      actorProgram
      beforeGlobal
      beforeLocal
      afterLocal
      selectedAction
      selectedReaction
      hProgramLookup
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
end LF
end Relico
