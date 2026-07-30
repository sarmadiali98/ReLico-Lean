import Relico.Correctness.MultiStorePayloadDetailedObservableWeakExecution

set_option autoImplicit false

namespace Relico

namespace DTR

/--
Canonical source base state for the payload-aware multi-server fragment.

The persistent store is supplied explicitly. Initial execution has metric
time zero, no activation-local parameters, no pending messages, and no active
message-server body.
-/
def initialMultiStorePayloadState
    (initialStateStore : StateStore) :
    DTR.MultiStorePayloadState :=
  {
    currentTime :=
      0

    stateStore :=
      initialStateStore

    parameters :=
      []

    pendingMessages :=
      []

    activeBody :=
      []
  }

/--
Stable detailed source wrapper for the canonical initial base state.
-/
def initialDetailedMultiStorePayloadState
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore) :
    DTR.DetailedMultiStorePayloadState
      messageServers :=
  .stable
    (DTR.initialMultiStorePayloadState
      initialStateStore)

end DTR

namespace LF

/--
Canonical generated-LF base state corresponding to the source initial state.

The target starts at tag `(0,0)`, uses the same persistent store, and has no
activation-local parameters, pending actions, or active reaction body.
-/
def initialMultiStorePayloadState
    (initialStateStore : StateStore) :
    LF.MultiStorePayloadState :=
  {
    currentTag :=
      {
        time :=
          0

        microstep :=
          0
      }

    stateStore :=
      initialStateStore

    parameters :=
      []

    pendingActions :=
      []

    activeBody :=
      []
  }

/--
Stable detailed generated-LF wrapper for the canonical initial base state.
-/
def initialDetailedMultiStorePayloadState
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore) :
    LF.DetailedMultiStorePayloadState
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers) :=
  .stable
    (LF.initialMultiStorePayloadState
      initialStateStore)

end LF

namespace Correctness

/--
The canonical source and generated-LF base states satisfy the complete
payload-aware runtime correspondence.

The persistent store is shared exactly. Both queues and active bodies are
empty, so payload correspondence, selection compatibility, and the LF
pending-not-past invariant hold without an execution premise.
-/
theorem multiStorePayloadInitialStates_correspond
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore) :
    MultiStorePayloadRuntimeStateCorresponds
      messageServers
      (DTR.initialMultiStorePayloadState
        initialStateStore)
      (LF.initialMultiStorePayloadState
        initialStateStore) := by

  refine
    {
      states :=
        {
          states :=
            {
              currentTime :=
                rfl

              stateStore :=
                rfl

              parameters :=
                rfl

              pendingQueues :=
                PayloadQueueCorresponds.nil

              activeBody :=
                rfl
            }

          pendingEvents :=
            multiStorePayloadSelectionCompatible_nil
              messageServers
        }

      pendingNotPast :=
        LF.MultiStorePayloadState.pendingNotPast_of_pendingActions_nil
          rfl
    }

/--
The canonical stable detailed states correspond.
-/
theorem detailedMultiStorePayloadInitialStates_correspond
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (DTR.initialDetailedMultiStorePayloadState
        messageServers
        initialStateStore)
      (LF.initialDetailedMultiStorePayloadState
        messageServers
        initialStateStore) := by

  exact
    MultiStorePayloadDetailedRuntimeStateCorresponds.stable
      (multiStorePayloadInitialStates_correspond
        messageServers
        initialStateStore)

/--
Canonical initial states have no active body, activation-local parameters,
or pending event occurrences.
-/
theorem multiStorePayloadInitialStates_idle
    (initialStateStore :
      StateStore) :
    (DTR.initialMultiStorePayloadState
        initialStateStore).activeBody =
      [] ∧
    (DTR.initialMultiStorePayloadState
        initialStateStore).parameters =
      [] ∧
    (DTR.initialMultiStorePayloadState
        initialStateStore).pendingMessages =
      [] ∧
    (LF.initialMultiStorePayloadState
        initialStateStore).activeBody =
      [] ∧
    (LF.initialMultiStorePayloadState
        initialStateStore).parameters =
      [] ∧
    (LF.initialMultiStorePayloadState
        initialStateStore).pendingActions =
      [] := by

  simp [
    DTR.initialMultiStorePayloadState,
    LF.initialMultiStorePayloadState
  ]

/--
Canonical initial scheduler values are source time zero and target tag
`(0,0)`.
-/
theorem multiStorePayloadInitialSchedulerBase
    (initialStateStore :
      StateStore) :
    (DTR.initialMultiStorePayloadState
        initialStateStore).currentTime =
      0 ∧
    (LF.initialMultiStorePayloadState
        initialStateStore).currentTag.time =
      0 ∧
    (LF.initialMultiStorePayloadState
        initialStateStore).currentTag.microstep =
      0 := by

  simp [
    DTR.initialMultiStorePayloadState,
    LF.initialMultiStorePayloadState
  ]

/--
Both canonical initial states contain exactly the supplied persistent store.
-/
theorem multiStorePayloadInitialStores
    (initialStateStore :
      StateStore) :
    (DTR.initialMultiStorePayloadState
        initialStateStore).stateStore =
      initialStateStore ∧
    (LF.initialMultiStorePayloadState
        initialStateStore).stateStore =
      initialStateStore := by

  simp [
    DTR.initialMultiStorePayloadState,
    LF.initialMultiStorePayloadState
  ]

/--
Package the canonical detailed-state correspondence and the elementary
initial-state facts required by later finite-execution wrappers.
-/
theorem multiStorePayloadInitialEntry_package
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (DTR.initialDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        (LF.initialDetailedMultiStorePayloadState
          messageServers
          initialStateStore) ∧
      ((DTR.initialMultiStorePayloadState
            initialStateStore).activeBody =
          [] ∧
        (DTR.initialMultiStorePayloadState
            initialStateStore).parameters =
          [] ∧
        (DTR.initialMultiStorePayloadState
            initialStateStore).pendingMessages =
          [] ∧
        (LF.initialMultiStorePayloadState
            initialStateStore).activeBody =
          [] ∧
        (LF.initialMultiStorePayloadState
            initialStateStore).parameters =
          [] ∧
        (LF.initialMultiStorePayloadState
            initialStateStore).pendingActions =
          []) ∧
      ((DTR.initialMultiStorePayloadState
            initialStateStore).currentTime =
          0 ∧
        (LF.initialMultiStorePayloadState
            initialStateStore).currentTag.time =
          0 ∧
        (LF.initialMultiStorePayloadState
            initialStateStore).currentTag.microstep =
          0) ∧
      ((DTR.initialMultiStorePayloadState
            initialStateStore).stateStore =
          initialStateStore ∧
        (LF.initialMultiStorePayloadState
            initialStateStore).stateStore =
          initialStateStore) := by

  exact
    ⟨ detailedMultiStorePayloadInitialStates_correspond
        messageServers
        initialStateStore,
      multiStorePayloadInitialStates_idle
        initialStateStore,
      multiStorePayloadInitialSchedulerBase
        initialStateStore,
      multiStorePayloadInitialStores
        initialStateStore ⟩

end Correctness
end Relico
