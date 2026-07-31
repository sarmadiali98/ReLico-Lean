import Relico.Common.ActorTopology
import Relico.LF.MultiStorePayloadSemantics

set_option autoImplicit false

namespace Relico
namespace LF

abbrev GlobalMultiStorePayloadActorPrograms :=
  Store ActorName
    LF.MultiStorePayloadProgram

abbrev GlobalMultiStorePayloadActorStates :=
  Store ActorName
    LF.MultiStorePayloadState

/--
A finite ordered collection of generated local reactor programs.

The topology is still abstract at E2. Concrete LF ports and connections remain
a later layer.
-/
structure GlobalMultiStorePayloadProgram where
  actorPrograms :
    LF.GlobalMultiStorePayloadActorPrograms

  topology :
    ActorTopology

deriving Repr, DecidableEq, BEq, Inhabited

/--
A global LF runtime snapshot containing one local reactor state per actor.
-/
structure GlobalMultiStorePayloadState where
  currentTag :
    LF.Tag

  actorStates :
    LF.GlobalMultiStorePayloadActorStates

deriving Repr, DecidableEq, BEq, Inhabited

namespace GlobalMultiStorePayloadProgram

/--
Each actor key matches the generated reactor-instance actor name, and the
instance references the generated reactor declaration.
-/
def actorProgramsMatchKeys
    (programs :
      LF.GlobalMultiStorePayloadActorPrograms) :
    Bool :=
  programs.all
    (fun programEntry =>
      (programEntry.1 ==
        programEntry.2.reactorInstance.name) &&
      (programEntry.2.reactor.name ==
        programEntry.2.reactorInstance.reactorName))

def wellFormed
    (program :
      LF.GlobalMultiStorePayloadProgram) :
    Bool :=
  ActorTopology.wellFormed
      program.actorPrograms
      program.topology &&
    actorProgramsMatchKeys
      program.actorPrograms

def lookupActor
    (program :
      LF.GlobalMultiStorePayloadProgram)
    (actorName :
      ActorName) :
    Option LF.MultiStorePayloadProgram :=
  Store.lookup
    program.actorPrograms
    actorName

end GlobalMultiStorePayloadProgram

namespace GlobalMultiStorePayloadState

def lookupActor
    (state :
      LF.GlobalMultiStorePayloadState)
    (actorName :
      ActorName) :
    Option LF.MultiStorePayloadState :=
  Store.lookup
    state.actorStates
    actorName

def updateActor
    (state :
      LF.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (actorState :
      LF.MultiStorePayloadState) :
    LF.GlobalMultiStorePayloadState :=
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
      LF.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (actorState :
      LF.MultiStorePayloadState) :
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
      LF.GlobalMultiStorePayloadState)
    {actorName otherActor :
      ActorName}
    (actorState :
      LF.MultiStorePayloadState)
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
theorem updateActor_currentTag
    (state :
      LF.GlobalMultiStorePayloadState)
    (actorName :
      ActorName)
    (actorState :
      LF.MultiStorePayloadState) :
    (updateActor
      state
      actorName
      actorState).currentTag =
      state.currentTag := by
  rfl

end GlobalMultiStorePayloadState
end LF
end Relico
