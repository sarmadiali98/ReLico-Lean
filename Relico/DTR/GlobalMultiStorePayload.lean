import Relico.Common.ActorTopology
import Relico.DTR.MultiStorePayloadSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

abbrev GlobalMultiStorePayloadActors :=
  Store ActorName
    DTR.MultiStorePayloadModel

abbrev GlobalMultiStorePayloadActorStates :=
  Store ActorName
    DTR.MultiStorePayloadState

/--
A finite ordered collection of payload-aware actors plus known-rebec topology.

No global transition relation is introduced here.
-/
structure GlobalMultiStorePayloadModel where
  actors :
    DTR.GlobalMultiStorePayloadActors

  topology :
    ActorTopology

deriving Repr, DecidableEq, BEq, Inhabited

/--
A global runtime snapshot containing one local DTR state per actor.

The global time is represented explicitly but no global event-selection policy
is introduced by this structure.
-/
structure GlobalMultiStorePayloadState where
  currentTime :
    LogicalTime

  actorStates :
    DTR.GlobalMultiStorePayloadActorStates

deriving Repr, DecidableEq, BEq, Inhabited

namespace GlobalMultiStorePayloadModel

/--
Every store key is the exact name of the actor model stored at that key, and
the actor instance names its declared reactive class.
-/
def actorsMatchKeysAndClasses
    (actors :
      DTR.GlobalMultiStorePayloadActors) :
    Bool :=
  actors.all
    (fun actorEntry =>
      (actorEntry.1 ==
        actorEntry.2.actor.name) &&
      (actorEntry.2.actor.className ==
        actorEntry.2.reactiveClass.name))

/--
Structural global-model well-formedness for the E2 foundation.
-/
def wellFormed
    (model :
      DTR.GlobalMultiStorePayloadModel) :
    Bool :=
  ActorTopology.wellFormed
      model.actors
      model.topology &&
    actorsMatchKeysAndClasses
      model.actors

def lookupActor
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (actorName :
      ActorName) :
    Option DTR.MultiStorePayloadModel :=
  Store.lookup
    model.actors
    actorName

end GlobalMultiStorePayloadModel

namespace GlobalMultiStorePayloadState

def lookupActor
    (state :
      DTR.GlobalMultiStorePayloadState)
    (actorName :
      ActorName) :
    Option DTR.MultiStorePayloadState :=
  Store.lookup
    state.actorStates
    actorName

/--
Update exactly one actor component while preserving global time.
-/
def updateActor
    (state :
      DTR.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (actorState :
      DTR.MultiStorePayloadState) :
    DTR.GlobalMultiStorePayloadState :=
  {
    state with
    actorStates :=
      Store.update
        state.actorStates
        actorName
        actorState
  }

@[simp]
theorem lookupActor_update_eq
    (state :
      DTR.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (actorState :
      DTR.MultiStorePayloadState) :
    lookupActor
        (updateActor
          state
          actorName
          actorState)
        actorName =
      some actorState := by
  simp [
    lookupActor,
    updateActor
  ]

theorem lookupActor_update_ne
    (state :
      DTR.GlobalMultiStorePayloadState)
    {actorName otherActor :
      ActorName}
    (actorState :
      DTR.MultiStorePayloadState)
    (hDifferent :
      actorName ≠ otherActor) :
    lookupActor
        (updateActor
          state
          actorName
          actorState)
        otherActor =
      lookupActor
        state
        otherActor := by
  simpa [
    lookupActor,
    updateActor
  ] using
    Store.lookup_update_ne
      state.actorStates
      actorState
      hDifferent

@[simp]
theorem updateActor_currentTime
    (state :
      DTR.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (actorState :
      DTR.MultiStorePayloadState) :
    (updateActor
      state
      actorName
      actorState).currentTime =
      state.currentTime := by
  rfl

end GlobalMultiStorePayloadState
end DTR
end Relico
