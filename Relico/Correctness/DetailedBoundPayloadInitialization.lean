import Relico.Correctness.DetailedBoundPayloadObservableWeakExecution
import Relico.LF.Initialization

set_option autoImplicit false

namespace Relico

namespace DTR

/--
Canonical idle runtime state for one parameter-aware payload message server.

The persistent state value is supplied explicitly because the current
single-server payload fragment does not contain state-variable declarations or
a model-level initializer.

No activation is running and no message has yet been supplied by the
environment.
-/
def PayloadMessageServer.initialBoundPayloadState
    (_server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    DTR.BoundPayloadState := {

  currentTime :=
    0

  stateValue :=
    initialStateValue

  parameters :=
    ParameterStore.empty

  pendingMessages :=
    []

  activeBody :=
    []
}

/--
Canonical detailed source entry is the stable wrapper around the idle
bound-payload runtime state.
-/
def PayloadMessageServer.initialDetailedBoundPayloadState
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    DTR.DetailedBoundPayloadState
      server :=

  DTR.DetailedBoundPayloadState.stable
    (server.initialBoundPayloadState
      initialStateValue)

@[simp]
theorem PayloadMessageServer.initialBoundPayloadState_currentTime
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    (server.initialBoundPayloadState
      initialStateValue).currentTime =
      0 := by
  rfl

@[simp]
theorem PayloadMessageServer.initialBoundPayloadState_stateValue
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    (server.initialBoundPayloadState
      initialStateValue).stateValue =
      initialStateValue := by
  rfl

@[simp]
theorem PayloadMessageServer.initialBoundPayloadState_parameters
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    (server.initialBoundPayloadState
      initialStateValue).parameters =
      ParameterStore.empty := by
  rfl

@[simp]
theorem PayloadMessageServer.initialBoundPayloadState_pendingMessages
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    (server.initialBoundPayloadState
      initialStateValue).pendingMessages =
      [] := by
  rfl

@[simp]
theorem PayloadMessageServer.initialBoundPayloadState_activeBody
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    (server.initialBoundPayloadState
      initialStateValue).activeBody =
      [] := by
  rfl

end DTR

namespace LF

/--
Canonical idle generated-LF state for one parameter-aware payload reaction.

It starts at the established LF initial tag, carries the same persistent state
value as the source, and contains no active reaction or pending action.
-/
def PayloadReaction.initialBoundPayloadState
    (_reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    LF.BoundPayloadState := {

  currentTag :=
    LF.initialTag

  stateValue :=
    initialStateValue

  parameters :=
    ParameterStore.empty

  pendingActions :=
    []

  activeBody :=
    []
}

/--
Canonical detailed generated-LF entry is the stable wrapper around the idle
bound-payload runtime state.
-/
def PayloadReaction.initialDetailedBoundPayloadState
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    LF.DetailedBoundPayloadState
      reaction :=

  LF.DetailedBoundPayloadState.stable
    (reaction.initialBoundPayloadState
      initialStateValue)

@[simp]
theorem PayloadReaction.initialBoundPayloadState_currentTag
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    (reaction.initialBoundPayloadState
      initialStateValue).currentTag =
      LF.initialTag := by
  rfl

@[simp]
theorem PayloadReaction.initialBoundPayloadState_currentTime
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    (reaction.initialBoundPayloadState
      initialStateValue).currentTag.time =
      0 := by
  rfl

@[simp]
theorem PayloadReaction.initialBoundPayloadState_currentMicrostep
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    (reaction.initialBoundPayloadState
      initialStateValue).currentTag.microstep =
      0 := by
  rfl

@[simp]
theorem PayloadReaction.initialBoundPayloadState_stateValue
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    (reaction.initialBoundPayloadState
      initialStateValue).stateValue =
      initialStateValue := by
  rfl

@[simp]
theorem PayloadReaction.initialBoundPayloadState_parameters
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    (reaction.initialBoundPayloadState
      initialStateValue).parameters =
      ParameterStore.empty := by
  rfl

@[simp]
theorem PayloadReaction.initialBoundPayloadState_pendingActions
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    (reaction.initialBoundPayloadState
      initialStateValue).pendingActions =
      [] := by
  rfl

@[simp]
theorem PayloadReaction.initialBoundPayloadState_activeBody
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int) :
    (reaction.initialBoundPayloadState
      initialStateValue).activeBody =
      [] := by
  rfl

end LF

namespace Correctness

/--
The canonical idle source state and the idle state of the compiled payload
reaction correspond.

All scalar and body obligations are definitional. The only propositional
component is correspondence of the two empty pending-event queues.
-/
theorem boundPayloadInitialStates_correspond
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    BoundPayloadStateCorresponds
      (server.initialBoundPayloadState
        initialStateValue)
      ((Translation.compilePayloadMessageServer
          server).initialBoundPayloadState
        initialStateValue) := by

  exact {
    currentTime :=
      rfl

    stateValue :=
      rfl

    parameters :=
      rfl

    pendingEvents :=
      payloadQueueCorresponds_nil

    activeBody :=
      rfl
  }

/--
Canonical idle initialization lifts directly to stable detailed-state
correspondence.
-/
theorem detailedBoundPayloadInitialStates_correspond
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    DetailedBoundPayloadStateCorresponds
      server
      (server.initialDetailedBoundPayloadState
        initialStateValue)
      ((Translation.compilePayloadMessageServer
          server).initialDetailedBoundPayloadState
        initialStateValue) := by

  exact
    DetailedBoundPayloadStateCorresponds.stable
      (boundPayloadInitialStates_correspond
        server
        initialStateValue)

/--
The initialization state is genuinely idle on both sides: there is no active
activation and no pending event supplied by the environment.
-/
theorem boundPayloadInitialStates_idle
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    (server.initialBoundPayloadState
        initialStateValue).activeBody =
        [] ∧
      (server.initialBoundPayloadState
        initialStateValue).pendingMessages =
        [] ∧
      ((Translation.compilePayloadMessageServer
          server).initialBoundPayloadState
        initialStateValue).activeBody =
        [] ∧
      ((Translation.compilePayloadMessageServer
          server).initialBoundPayloadState
        initialStateValue).pendingActions =
        [] := by

  exact
    ⟨rfl,
     rfl,
     rfl,
     rfl⟩

/--
Canonical initialization also exposes the target scheduler facts needed by a
future invocation-entry invariant.
-/
theorem boundPayloadInitialTargetSchedulerBase
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    ((Translation.compilePayloadMessageServer
        server).initialBoundPayloadState
      initialStateValue).currentTag.time =
        0 ∧
      ((Translation.compilePayloadMessageServer
        server).initialBoundPayloadState
      initialStateValue).currentTag.microstep =
        0 ∧
      ((Translation.compilePayloadMessageServer
        server).initialBoundPayloadState
      initialStateValue).pendingActions =
        [] := by

  exact
    ⟨rfl,
     rfl,
     rfl⟩

end Correctness
end Relico
