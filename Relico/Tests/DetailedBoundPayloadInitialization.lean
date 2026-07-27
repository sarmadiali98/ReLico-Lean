import Relico.Correctness.DetailedBoundPayloadInitialization

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadInitialization

#check DTR.PayloadMessageServer.initialBoundPayloadState
#check DTR.PayloadMessageServer.initialDetailedBoundPayloadState

#check LF.PayloadReaction.initialBoundPayloadState
#check LF.PayloadReaction.initialDetailedBoundPayloadState

#check DTR.PayloadMessageServer.initialBoundPayloadState_currentTime
#check DTR.PayloadMessageServer.initialBoundPayloadState_stateValue
#check DTR.PayloadMessageServer.initialBoundPayloadState_parameters
#check DTR.PayloadMessageServer.initialBoundPayloadState_pendingMessages
#check DTR.PayloadMessageServer.initialBoundPayloadState_activeBody

#check LF.PayloadReaction.initialBoundPayloadState_currentTag
#check LF.PayloadReaction.initialBoundPayloadState_currentTime
#check LF.PayloadReaction.initialBoundPayloadState_currentMicrostep
#check LF.PayloadReaction.initialBoundPayloadState_stateValue
#check LF.PayloadReaction.initialBoundPayloadState_parameters
#check LF.PayloadReaction.initialBoundPayloadState_pendingActions
#check LF.PayloadReaction.initialBoundPayloadState_activeBody

#check Correctness.boundPayloadInitialStates_correspond
#check Correctness.detailedBoundPayloadInitialStates_correspond
#check Correctness.boundPayloadInitialStates_idle
#check Correctness.boundPayloadInitialTargetSchedulerBase

theorem source_initial_runtime_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    server.initialBoundPayloadState
        initialStateValue =
      {
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
      } := by
  rfl

theorem target_initial_runtime_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    (Translation.compilePayloadMessageServer
        server).initialBoundPayloadState
        initialStateValue =
      {
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
      } := by
  rfl

theorem runtime_initial_correspondence_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    Correctness.BoundPayloadStateCorresponds
      (server.initialBoundPayloadState
        initialStateValue)
      ((Translation.compilePayloadMessageServer
          server).initialBoundPayloadState
        initialStateValue) := by

  exact
    Correctness.boundPayloadInitialStates_correspond
      server
      initialStateValue

theorem detailed_initial_correspondence_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    Correctness.DetailedBoundPayloadStateCorresponds
      server
      (server.initialDetailedBoundPayloadState
        initialStateValue)
      ((Translation.compilePayloadMessageServer
          server).initialDetailedBoundPayloadState
        initialStateValue) := by

  exact
    Correctness.detailedBoundPayloadInitialStates_correspond
      server
      initialStateValue

theorem idle_initialization_interface
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
    Correctness.boundPayloadInitialStates_idle
      server
      initialStateValue

theorem target_scheduler_base_interface
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
    Correctness.boundPayloadInitialTargetSchedulerBase
      server
      initialStateValue

end DetailedBoundPayloadInitialization
end Tests
end Relico
