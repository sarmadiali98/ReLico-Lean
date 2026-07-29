import Relico.LF.PendingNotPast
import Relico.Correctness.MultiStorePayloadStatementCorrespondence
import Relico.Correctness.MultiStorePayloadDispatchSelection

set_option autoImplicit false

namespace Relico

namespace LF

/--
Scheduler consistency for the payload-aware LF runtime state.

Every pending logical action is at the current complete LF tag or a later
complete LF tag.
-/
def MultiStorePayloadState.PendingNotPast
    (state :
      LF.MultiStorePayloadState) :
    Prop :=
  LF.ActionQueue.PendingNotPast
    state.currentTag
    state.pendingActions

/--
A payload-aware LF runtime state with an empty pending-action queue satisfies
the scheduler-consistency invariant.
-/
theorem MultiStorePayloadState.pendingNotPast_of_pendingActions_nil
    {state :
      LF.MultiStorePayloadState}
    (hEmpty :
      state.pendingActions =
        []) :
    state.PendingNotPast := by

  unfold
    LF.MultiStorePayloadState.PendingNotPast

  rw [hEmpty]

  exact
    LF.ActionQueue.pendingNotPast_nil
      state.currentTag

/--
Extract complete-tag admissibility for one pending action.
-/
theorem MultiStorePayloadState.PendingNotPast.action
    {state :
      LF.MultiStorePayloadState}
    (hPending :
      state.PendingNotPast)
    {action :
      LF.PendingAction}
    (hAction :
      action ∈
        state.pendingActions) :
    state.currentTag.PrecedesOrEqual
      action.tag := by

  exact
    hPending
      action
      hAction

end LF

namespace Correctness

/--
Payload-aware store-state correspondence strengthened with the scheduler
selection relation.

The structural component equates metric time, persistent state, activation
parameters, exact payload queues, and active bodies. The pending-event
component additionally records occurrence-sensitive selection compatibility.
-/
structure MultiStorePayloadStoreStateCorresponds
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceState :
      DTR.MultiStorePayloadState)
    (targetState :
      LF.MultiStorePayloadState) :
    Prop where

  states :
    MultiStorePayloadStateCorresponds
      sourceState
      targetState

  pendingEvents :
    MultiStorePayloadSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions

/--
Runtime correspondence adds complete-tag scheduler consistency on the LF side.
-/
structure MultiStorePayloadRuntimeStateCorresponds
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceState :
      DTR.MultiStorePayloadState)
    (targetState :
      LF.MultiStorePayloadState) :
    Prop where

  states :
    MultiStorePayloadStoreStateCorresponds
      messageServers
      sourceState
      targetState

  pendingNotPast :
    targetState.PendingNotPast

theorem MultiStorePayloadStoreStateCorresponds.toStateCorresponds
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hStates :
      MultiStorePayloadStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    MultiStorePayloadStateCorresponds
      sourceState
      targetState :=
  hStates.states

theorem MultiStorePayloadStoreStateCorresponds.selectionCompatible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hStates :
      MultiStorePayloadStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    MultiStorePayloadSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions :=
  hStates.pendingEvents

theorem MultiStorePayloadStoreStateCorresponds.payloadQueues
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hStates :
      MultiStorePayloadStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    PayloadQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions :=
  hStates.states.pendingQueues

theorem MultiStorePayloadRuntimeStateCorresponds.toStoreStateCorresponds
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    MultiStorePayloadStoreStateCorresponds
      messageServers
      sourceState
      targetState :=
  hRuntime.states

theorem MultiStorePayloadRuntimeStateCorresponds.toStateCorresponds
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    MultiStorePayloadStateCorresponds
      sourceState
      targetState :=
  hRuntime.states.states

theorem MultiStorePayloadRuntimeStateCorresponds.selectionCompatible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    MultiStorePayloadSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions :=
  hRuntime.states.pendingEvents

theorem MultiStorePayloadRuntimeStateCorresponds.payloadQueues
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    PayloadQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions :=
  hRuntime.states.states.pendingQueues

theorem MultiStorePayloadRuntimeStateCorresponds.pendingActionNotPast
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState)
    {action :
      LF.PendingAction}
    (hAction :
      action ∈
        targetState.pendingActions) :
    targetState.currentTag.PrecedesOrEqual
      action.tag := by

  exact
    LF.MultiStorePayloadState.PendingNotPast.action
      hRuntime.pendingNotPast
      hAction

end Correctness
end Relico
