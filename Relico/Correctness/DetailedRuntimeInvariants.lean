import Relico.Correctness.DetailedPriorityRuntimeInvariant

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Phase-aware source invariant for the detailed DTR machine.

At a stable phase, it describes the stored source state.

At a dispatch-ready phase, dispatch has already removed the selected message
and loaded its message-server body, so the invariant describes the resulting
post-dispatch source state.
-/
def ConcreteDetailedSourceRuntimeInvariant
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (state :
      DTR.DetailedMultiStoreState
        messageServers) :
    Prop :=

  match state with

  | .stable sourceState =>
      DTR.StoreState.MultiStoreRuntimeWellFormed
          declaredVariables
          messageServers
          sourceState ∧
        DTR.Body.PriorityTimingWellFormed
          sourceState.activeBody

  | .dispatchReady
      _sourceBefore
      _selectedMessage
      _selectedServer
      sourceAfter
      _sourceDispatch =>

      DTR.StoreState.MultiStoreRuntimeWellFormed
          declaredVariables
          messageServers
          sourceAfter ∧
        DTR.Body.PriorityTimingWellFormed
          sourceAfter.activeBody

/--
Canonical target invariant for detailed generated-LF executions in the
positive-delay priority fragment.

Stable states and `afterTime` states carry the full priority runtime
invariant.

A canonical positive-delay execution does not persist in `dispatchReady`.
Every selected generated action has microstep zero, so after metric-time
progression the reaction is consumed directly from `afterTime`.
-/
def ConcreteDetailedTargetRuntimeInvariant
    (messageServers : List DTR.MessageServer)
    (state :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)) :
    Prop :=

  match state with

  | .stable targetState =>
      LF.StoreState.PriorityRuntimeInvariant
        targetState

  | .afterTime
      _targetBefore
      _selectedAction
      _selectedReaction
      targetAfter
      _targetDispatch =>

      LF.StoreState.PriorityRuntimeInvariant
        targetAfter

  | .dispatchReady
      _targetBefore
      _selectedAction
      _selectedReaction
      _targetAfter
      _targetDispatch =>

      False

@[simp]
theorem concreteDetailedSourceRuntimeInvariant_stable
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState} :
    ConcreteDetailedSourceRuntimeInvariant
          declaredVariables
          messageServers
          (.stable sourceState) ↔
      DTR.StoreState.MultiStoreRuntimeWellFormed
          declaredVariables
          messageServers
          sourceState ∧
        DTR.Body.PriorityTimingWellFormed
          sourceState.activeBody := by

  rfl

@[simp]
theorem concreteDetailedSourceRuntimeInvariant_dispatchReady
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter} :
    ConcreteDetailedSourceRuntimeInvariant
          declaredVariables
          messageServers
          (.dispatchReady
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
            sourceDispatch) ↔
      DTR.StoreState.MultiStoreRuntimeWellFormed
          declaredVariables
          messageServers
          sourceAfter ∧
        DTR.Body.PriorityTimingWellFormed
          sourceAfter.activeBody := by

  rfl

@[simp]
theorem concreteDetailedTargetRuntimeInvariant_stable
    {messageServers : List DTR.MessageServer}
    {targetState : LF.StoreState} :
    ConcreteDetailedTargetRuntimeInvariant
          messageServers
          (.stable targetState) ↔
      LF.StoreState.PriorityRuntimeInvariant
        targetState := by

  rfl

@[simp]
theorem concreteDetailedTargetRuntimeInvariant_afterTime
    {messageServers : List DTR.MessageServer}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter} :
    ConcreteDetailedTargetRuntimeInvariant
          messageServers
          (.afterTime
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch) ↔
      LF.StoreState.PriorityRuntimeInvariant
        targetAfter := by

  rfl

@[simp]
theorem concreteDetailedTargetRuntimeInvariant_dispatchReady
    {messageServers : List DTR.MessageServer}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter} :
    ¬ ConcreteDetailedTargetRuntimeInvariant
        messageServers
        (.dispatchReady
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch) := by

  simp [
    ConcreteDetailedTargetRuntimeInvariant
  ]

/--
Every exact detailed DTR transition preserves the phase-aware source runtime
invariant.

Statement and direct-consumption transitions reuse the corresponding combined
machine-step preservation theorems. Future dispatch moves the invariant to the
post-dispatch state. The `consumeReady` phase changes only the detailed phase
wrapper and therefore preserves the same underlying invariant directly.
-/
theorem concreteDetailedSourceRuntimeInvariant_preserved
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
    {sourceLabel :
      DTR.DetailedMultiStoreLabel}
    (hSourceStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        sourceBefore
        sourceLabel
        sourceAfter)
    (hMessageBodiesWellFormed :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.MultiStoreWellFormed
            declaredVariables
            (DTR.messageServerNames
              messageServers)
            messageServer.body)
    (hMessageBodiesTiming :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.PriorityTimingWellFormed
            messageServer.body)
    (hBefore :
      ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore) :
    ConcreteDetailedSourceRuntimeInvariant
      declaredVariables
      messageServers
      sourceAfter := by

  cases hSourceStep with

  | statement hStatement =>
      exact
        ⟨DTR.MultiStoreMachineStep.preserves_runtimeWellFormed
            (DTR.MultiStoreMachineStep.statement
              hStatement)
            hMessageBodiesWellFormed
            hBefore.1,
         DTR.MultiStoreMachineStep.preserves_priorityTimingWellFormed
            (DTR.MultiStoreMachineStep.statement
              hStatement)
            hMessageBodiesTiming
            hBefore.2⟩

  | timeAdvance hDispatch hFuture =>
      exact
        ⟨DTR.MultiStoreMachineStep.preserves_runtimeWellFormed
            (DTR.MultiStoreMachineStep.dispatch
              hDispatch)
            hMessageBodiesWellFormed
            hBefore.1,
         DTR.MultiStoreMachineStep.preserves_priorityTimingWellFormed
            (declaredVariables :=
              declaredVariables)
            (DTR.MultiStoreMachineStep.dispatch
              (declaredVariables :=
                declaredVariables)
              hDispatch)
            hMessageBodiesTiming
            hBefore.2⟩

  | consumeReady hDispatch =>
      simpa [
        ConcreteDetailedSourceRuntimeInvariant
      ] using
        hBefore

  | consumeNow hDispatch hSameTime =>
      exact
        ⟨DTR.MultiStoreMachineStep.preserves_runtimeWellFormed
            (DTR.MultiStoreMachineStep.dispatch
              hDispatch)
            hMessageBodiesWellFormed
            hBefore.1,
         DTR.MultiStoreMachineStep.preserves_priorityTimingWellFormed
            (declaredVariables :=
              declaredVariables)
            (DTR.MultiStoreMachineStep.dispatch
              (declaredVariables :=
                declaredVariables)
              hDispatch)
            hMessageBodiesTiming
            hBefore.2⟩

end Correctness
end Relico
