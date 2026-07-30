import Relico.Correctness.MultiStorePayloadDetailedInitialization

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadDetailedInitialization

#check
  DTR.initialMultiStorePayloadState

#check
  DTR.initialDetailedMultiStorePayloadState

#check
  LF.initialMultiStorePayloadState

#check
  LF.initialDetailedMultiStorePayloadState

#check
  Correctness.multiStorePayloadInitialStates_correspond

#check
  Correctness.detailedMultiStorePayloadInitialStates_correspond

#check
  Correctness.multiStorePayloadInitialStates_idle

#check
  Correctness.multiStorePayloadInitialSchedulerBase

#check
  Correctness.multiStorePayloadInitialStores

#check
  Correctness.multiStorePayloadInitialEntry_package

example
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore) :
    Correctness.MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (DTR.initialDetailedMultiStorePayloadState
        messageServers
        initialStateStore)
      (LF.initialDetailedMultiStorePayloadState
        messageServers
        initialStateStore) := by

  exact
    Correctness.detailedMultiStorePayloadInitialStates_correspond
      messageServers
      initialStateStore

example
    (initialStateStore :
      StateStore) :
    (DTR.initialMultiStorePayloadState
        initialStateStore).currentTime =
      0 := by

  rfl

example
    (initialStateStore :
      StateStore) :
    (LF.initialMultiStorePayloadState
        initialStateStore).currentTag.time =
      0 := by

  rfl

example
    (initialStateStore :
      StateStore) :
    (LF.initialMultiStorePayloadState
        initialStateStore).currentTag.microstep =
      0 := by

  rfl

example
    (initialStateStore :
      StateStore) :
    (DTR.initialMultiStorePayloadState
        initialStateStore).pendingMessages =
      [] := by

  rfl

example
    (initialStateStore :
      StateStore) :
    (LF.initialMultiStorePayloadState
        initialStateStore).pendingActions =
      [] := by

  rfl

example
    (initialStateStore :
      StateStore) :
    (DTR.initialMultiStorePayloadState
        initialStateStore).stateStore =
      initialStateStore := by

  rfl

example
    (initialStateStore :
      StateStore) :
    (LF.initialMultiStorePayloadState
        initialStateStore).stateStore =
      initialStateStore := by

  rfl

#print axioms
  Correctness.multiStorePayloadInitialStates_correspond

#print axioms
  Correctness.detailedMultiStorePayloadInitialStates_correspond

#print axioms
  Correctness.multiStorePayloadInitialEntry_package

end MultiStorePayloadDetailedInitialization
end Tests
end Relico
