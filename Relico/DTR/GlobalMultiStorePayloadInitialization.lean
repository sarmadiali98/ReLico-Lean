import Relico.Correctness.MultiStorePayloadDetailedStartupEntry
import Relico.DTR.GlobalMultiStorePayload

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Ordered actor-specific persistent-state inputs used at global startup.
-/
abbrev GlobalMultiStorePayloadInitialStores :=
  Store ActorName
    StateStore

/--
Aligned startup entries retain each local model together with its initial
persistent store.
-/
abbrev GlobalMultiStorePayloadStartupEntries :=
  Store ActorName
    (
      DTR.MultiStorePayloadModel ×
      StateStore
    )

namespace GlobalMultiStorePayloadInitialization

def initialStoresWellFormed
    (actors :
      DTR.GlobalMultiStorePayloadActors)
    (initialStores :
      DTR.GlobalMultiStorePayloadInitialStores) :
    Bool :=
  decide
      (Store.KeysUnique
        initialStores) &&
    (Store.keys actors ==
      Store.keys initialStores)

/--
Reject missing, extra, reordered, or differently named initial-store entries.
-/
def alignStartupEntries
    (actors :
      DTR.GlobalMultiStorePayloadActors)
    (initialStores :
      DTR.GlobalMultiStorePayloadInitialStores) :
    Option
      DTR.GlobalMultiStorePayloadStartupEntries :=
  Store.zipValuesWithKey
    (fun _ model initialStore =>
      (
        model,
        initialStore
      ))
    actors
    initialStores

/--
Construct one source startup state per aligned actor.
-/
def startupActorStates
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    DTR.GlobalMultiStorePayloadActorStates :=
  Store.mapValuesWithKey
    (fun _ entry =>
      _root_.Relico.DTR.MultiStorePayloadConstructor.startupMultiStorePayloadState
        entry.1.reactiveClass.constructor
        entry.2)
    entries

def startupStateFromEntries
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    DTR.GlobalMultiStorePayloadState where

  currentTime :=
    0

  actorStates :=
    startupActorStates
      entries

/--
Executable global source startup construction.

The source model must be structurally well-formed and the initial-store domain
must match the actor domain exactly.
-/
def initializeGlobalMultiStorePayloadState
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (initialStores :
      DTR.GlobalMultiStorePayloadInitialStores) :
    Option
      DTR.GlobalMultiStorePayloadState :=

  if
      model.wellFormed &&
      initialStoresWellFormed
        model.actors
        initialStores
  then
    Option.map
      startupStateFromEntries
      (alignStartupEntries
        model.actors
        initialStores)
  else
    none

theorem alignStartupEntries_keys
    {actors :
      DTR.GlobalMultiStorePayloadActors}
    {initialStores :
      DTR.GlobalMultiStorePayloadInitialStores}
    {entries :
      DTR.GlobalMultiStorePayloadStartupEntries}
    (hAlign :
      alignStartupEntries
          actors
          initialStores =
        some entries) :
    Store.keys entries =
        Store.keys actors ∧
      Store.keys entries =
        Store.keys initialStores := by

  exact
    Store.keys_zipValuesWithKey_of_eq_some
      (fun _ model initialStore =>
        (
          model,
          initialStore
        ))
      hAlign

theorem startupActorStates_keys
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    Store.keys
        (startupActorStates
          entries) =
      Store.keys entries := by

  exact
    Store.keys_mapValuesWithKey
      (fun _ entry =>
        _root_.Relico.DTR.MultiStorePayloadConstructor.startupMultiStorePayloadState
          entry.1.reactiveClass.constructor
          entry.2)
      entries

theorem startupActorStates_lookup
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries)
    (actorName :
      ActorName) :
    Store.lookup
        (startupActorStates
          entries)
        actorName =
      Option.map
        (fun entry =>
          _root_.Relico.DTR.MultiStorePayloadConstructor.startupMultiStorePayloadState
            entry.1.reactiveClass.constructor
            entry.2)
        (Store.lookup
          entries
          actorName) := by

  exact
    Store.lookup_mapValuesWithKey
      (fun _ entry =>
        _root_.Relico.DTR.MultiStorePayloadConstructor.startupMultiStorePayloadState
          entry.1.reactiveClass.constructor
          entry.2)
      entries
      actorName

@[simp]
theorem startupStateFromEntries_currentTime
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    (startupStateFromEntries
      entries).currentTime =
      0 := by
  rfl

theorem startupStateFromEntries_actorKeys
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    Store.keys
        (startupStateFromEntries
          entries).actorStates =
      Store.keys entries := by

  exact
    startupActorStates_keys
      entries

theorem startupStateFromEntries_lookupActor
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries)
    (actorName :
      ActorName) :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (startupStateFromEntries
          entries)
        actorName =
      Option.map
        (fun entry =>
          _root_.Relico.DTR.MultiStorePayloadConstructor.startupMultiStorePayloadState
            entry.1.reactiveClass.constructor
            entry.2)
        (Store.lookup
          entries
          actorName) := by

  exact
    startupActorStates_lookup
      entries
      actorName

end GlobalMultiStorePayloadInitialization
end DTR
end Relico
