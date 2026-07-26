import Relico.Correctness.DetailedPriorityRuntimeInvariant

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedPriorityRuntimeInvariant

theorem generated_initial_state_has_priority_runtime_invariant
    (program : LF.MultiStoreProgram) :
    LF.StoreState.PriorityRuntimeInvariant
      (LF.MultiStoreProgram.initialState
        program) := by

  exact
    LF.MultiStoreProgram.initialState_priorityRuntimeInvariant
      program

theorem forward_dispatch_compatibility_is_derived
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {targetBefore : LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hStates :
      Correctness.StoreStateCorresponds
        sourceBefore
        targetBefore)
    (hTargetInvariant :
      LF.StoreState.PriorityRuntimeInvariant
        targetBefore) :
    Correctness.StoreForwardDispatchCompatible
      selectedMessage
      sourceAfter.pendingMessages
      targetBefore := by

  exact
    Correctness.storeForwardDispatchCompatible_of_priorityRuntimeInvariant
      hSourceDispatch
      hStates
      hTargetInvariant

theorem target_machine_step_preserves_full_invariant
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState targetStateAfter : LF.StoreState}
    {targetLabel : LF.MultiStoreMachineLabel}
    (hTargetStep :
      LF.MultiStoreMachineStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      Correctness.StoreStateCorresponds
        sourceState
        targetState)
    (hSourceTiming :
      DTR.Body.PriorityTimingWellFormed
        sourceState.activeBody)
    (hTargetInvariant :
      LF.StoreState.PriorityRuntimeInvariant
        targetState) :
    LF.StoreState.PriorityRuntimeInvariant
      targetStateAfter := by

  exact
    Correctness.targetMultiStoreMachineStep_preserves_priorityRuntimeInvariant
      hTargetStep
      hStates
      hSourceTiming
      hTargetInvariant

end DetailedPriorityRuntimeInvariant
end Tests
end Relico
