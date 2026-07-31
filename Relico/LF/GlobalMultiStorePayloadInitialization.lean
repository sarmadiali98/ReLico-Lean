import Relico.DTR.GlobalMultiStorePayloadInitialization
import Relico.LF.GlobalMultiStorePayload

set_option autoImplicit false

namespace Relico
namespace LF
namespace GlobalMultiStorePayloadInitialization

def globalStartupTag :
    LF.Tag where

  time :=
    0

  microstep :=
    0

/--
Construct one generated-LF startup state per aligned actor entry.
-/
def startupActorStates
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    LF.GlobalMultiStorePayloadActorStates :=
  Store.mapValuesWithKey
    (fun _ entry =>
      LF.startupLFMultiStorePayloadState
        entry.1.reactiveClass.constructor
        entry.2)
    entries

def startupStateFromEntries
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    LF.GlobalMultiStorePayloadState where

  currentTag :=
    globalStartupTag

  actorStates :=
    startupActorStates
      entries

/--
Executable generated-LF startup construction over the same aligned input.
-/
def initializeGlobalMultiStorePayloadState
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (initialStores :
      DTR.GlobalMultiStorePayloadInitialStores) :
    Option
      LF.GlobalMultiStorePayloadState :=

  if
      model.wellFormed &&
      _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.initialStoresWellFormed
          model.actors
          initialStores
  then
    Option.map
      startupStateFromEntries
      (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
          model.actors
          initialStores)
  else
    none

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
        LF.startupLFMultiStorePayloadState
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
          LF.startupLFMultiStorePayloadState
            entry.1.reactiveClass.constructor
            entry.2)
        (Store.lookup
          entries
          actorName) := by

  exact
    Store.lookup_mapValuesWithKey
      (fun _ entry =>
        LF.startupLFMultiStorePayloadState
          entry.1.reactiveClass.constructor
          entry.2)
      entries
      actorName

@[simp]
theorem startupStateFromEntries_currentTag
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    (startupStateFromEntries
      entries).currentTag =
      globalStartupTag := by
  rfl

@[simp]
theorem startupStateFromEntries_currentTime
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    (startupStateFromEntries
      entries).currentTag.time =
      0 := by
  rfl

@[simp]
theorem startupStateFromEntries_microstep
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries) :
    (startupStateFromEntries
      entries).currentTag.microstep =
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
    LF.GlobalMultiStorePayloadState.lookupActor
        (startupStateFromEntries
          entries)
        actorName =
      Option.map
        (fun entry =>
          LF.startupLFMultiStorePayloadState
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
end LF
end Relico
