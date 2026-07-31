import Relico.DTR.GlobalMultiStorePayload
import Relico.LF.GlobalMultiStorePayload
import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Compile the ordered actor collection componentwise.

The actor-key order is preserved exactly.
-/
def compileGlobalMultiStorePayloadActors :
    DTR.GlobalMultiStorePayloadActors →
    LF.GlobalMultiStorePayloadActorPrograms

  | [] =>
      []

  | (actorName, model) ::
      remaining =>
      (
        actorName,
        translateMultiStorePayloadCore
          model
      ) ::
        compileGlobalMultiStorePayloadActors
          remaining

/--
Compile all local actors and preserve the abstract topology unchanged.
-/
def translateGlobalMultiStorePayloadCore
    (model :
      DTR.GlobalMultiStorePayloadModel) :
    LF.GlobalMultiStorePayloadProgram where

  actorPrograms :=
    compileGlobalMultiStorePayloadActors
      model.actors

  topology :=
    model.topology

@[simp]
theorem compileGlobalMultiStorePayloadActors_nil :
    compileGlobalMultiStorePayloadActors [] =
      [] := by
  rfl

@[simp]
theorem compileGlobalMultiStorePayloadActors_cons
    (actorName :
      ActorName)
    (model :
      DTR.MultiStorePayloadModel)
    (remaining :
      DTR.GlobalMultiStorePayloadActors) :
    compileGlobalMultiStorePayloadActors
        ((actorName, model) ::
          remaining) =
      (
        actorName,
        translateMultiStorePayloadCore
          model
      ) ::
        compileGlobalMultiStorePayloadActors
          remaining := by
  rfl

theorem compileGlobalMultiStorePayloadActors_keys
    (actors :
      DTR.GlobalMultiStorePayloadActors) :
    Store.keys
        (compileGlobalMultiStorePayloadActors
          actors) =
      Store.keys actors := by

  induction actors with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨actorName, model⟩

      change
        actorName ::
            Store.keys
              (compileGlobalMultiStorePayloadActors
                remaining) =
          actorName ::
            Store.keys remaining

      exact
        congrArg
          (fun actorNames =>
            actorName ::
              actorNames)
          inductionHypothesis

theorem lookup_compileGlobalMultiStorePayloadActors
    (actors :
      DTR.GlobalMultiStorePayloadActors)
    (actorName :
      ActorName) :
    Store.lookup
        (compileGlobalMultiStorePayloadActors
          actors)
        actorName =
      Option.map
        translateMultiStorePayloadCore
        (Store.lookup
          actors
          actorName) := by

  induction actors with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨candidate, model⟩

      by_cases hCandidate :
          candidate = actorName

      · subst candidate

        simp [
          compileGlobalMultiStorePayloadActors,
          Store.lookup
        ]

      · simp [
          compileGlobalMultiStorePayloadActors,
          Store.lookup,
          hCandidate,
          inductionHypothesis
        ]

@[simp]
theorem translateGlobalMultiStorePayloadCore_topology
    (model :
      DTR.GlobalMultiStorePayloadModel) :
    (translateGlobalMultiStorePayloadCore
      model).topology =
      model.topology := by
  rfl

theorem translateGlobalMultiStorePayloadCore_actorKeys
    (model :
      DTR.GlobalMultiStorePayloadModel) :
    Store.keys
        (translateGlobalMultiStorePayloadCore
          model).actorPrograms =
      Store.keys model.actors := by
  exact
    compileGlobalMultiStorePayloadActors_keys
      model.actors

end Translation
end Relico
