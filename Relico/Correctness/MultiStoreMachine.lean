import Relico.Correctness.MultiStoreBackward
import Relico.Correctness.MultiStoreDispatch
import Relico.Correctness.MultiStoreForward
import Relico.DTR.MultiStoreMachineSemantics
import Relico.LF.MultiStoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between combined multi-server machine labels.

Statement labels use the existing transition-label correspondence.
Dispatch labels additionally identify the exact generated reaction for
the selected source message server.
-/
inductive MultiStoreMachineLabelCorresponds :
    DTR.MultiStoreMachineLabel →
    LF.MultiStoreMachineLabel →
    Prop where

  | statement
      {sourceLabel : DTR.Label}
      {targetLabel : LF.Label}
      (hLabels :
        LabelCorresponds
          sourceLabel
          targetLabel) :

      MultiStoreMachineLabelCorresponds
        (DTR.MultiStoreMachineLabel.statement
          sourceLabel)
        (LF.MultiStoreMachineLabel.statement
          targetLabel)

  | dispatch
      {sourceMessage : DTR.PendingMessage}
      {sourceServer : DTR.MessageServer}
      {targetAction : LF.PendingAction}
      {targetReaction : LF.Reaction}
      (hReaction :
        targetReaction =
          Translation.compileMessageReaction
            sourceServer)
      (hPending :
        PendingCorresponds
          sourceMessage
          targetAction) :

      MultiStoreMachineLabelCorresponds
        (DTR.MultiStoreMachineLabel.dispatch
          sourceMessage
          sourceServer)
        (LF.MultiStoreMachineLabel.dispatch
          targetAction
          targetReaction)

/--
Compatibility required for forward combined-machine simulation.

Statement transitions require no additional scheduler condition.
Dispatch transitions retain the existing LF tag-scheduler
compatibility premise.
-/
def MultiStoreForwardMachineCompatible
    (sourceLabel : DTR.MultiStoreMachineLabel)
    (sourceStateAfter : DTR.StoreState)
    (targetState : LF.StoreState) :
    Prop :=
  match sourceLabel with

  | DTR.MultiStoreMachineLabel.statement _ =>
      True

  | DTR.MultiStoreMachineLabel.dispatch
      selectedMessage
      _selectedServer =>

      StoreForwardDispatchCompatible
        selectedMessage
        sourceStateAfter.pendingMessages
        targetState

/--
Conditional forward simulation for one combined multi-server machine
step.
-/
theorem multiStoreMachineStep_forward
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceState sourceStateAfter : DTR.StoreState}
    {sourceLabel : DTR.MultiStoreMachineLabel}
    {targetState : LF.StoreState}
    (hSourceStep :
      DTR.MultiStoreMachineStep
        declaredVariables
        messageServers
        sourceState
        sourceLabel
        sourceStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hCompatible :
      MultiStoreForwardMachineCompatible
        sourceLabel
        sourceStateAfter
        targetState) :
    ∃ targetLabel targetStateAfter,
      LF.MultiStoreMachineStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          targetState
          targetLabel
          targetStateAfter ∧
      MultiStoreMachineLabelCorresponds
        sourceLabel
        targetLabel ∧
      StoreStateCorresponds
        sourceStateAfter
        targetStateAfter := by

  cases hSourceStep with

  | statement hStatement =>
      rcases
          multiStore_step_forward
            hStatement
            hStates
        with
          ⟨targetStatementLabel,
           targetStateAfter,
           hTargetStatement,
           hLabels,
           hFinalStates⟩

      exact
        ⟨LF.MultiStoreMachineLabel.statement
            targetStatementLabel,
         targetStateAfter,
         LF.MultiStoreMachineStep.statement
           hTargetStatement,
         MultiStoreMachineLabelCorresponds.statement
           hLabels,
         hFinalStates⟩

  | dispatch hDispatch =>
      rcases
          multiStore_dispatch_forward_of_compatible
            hDispatch
            hStates
            (by
              simpa [
                MultiStoreForwardMachineCompatible
              ] using
                hCompatible)
        with
          ⟨selectedAction,
           targetReaction,
           targetStateAfter,
           hTargetDispatch,
           hReaction,
           hPending,
           hFinalStates⟩

      exact
        ⟨LF.MultiStoreMachineLabel.dispatch
            selectedAction
            targetReaction,
         targetStateAfter,
         LF.MultiStoreMachineStep.dispatch
           hTargetDispatch,
         MultiStoreMachineLabelCorresponds.dispatch
           hReaction
           hPending,
         hFinalStates⟩

/--
Backward simulation for one generated multi-server machine step.

Statement recovery requires source active-body well-formedness.
Dispatch recovery obtains the source message server directly from the
generated reaction declaration.
-/
theorem multiStoreMachineStep_backward
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
      StoreStateCorresponds
        sourceState
        targetState)
    (hTargetMicrostepsZero :
      LF.StoreState.PendingMicrostepsZero
        targetState)
    (hSourceBodyWellFormed :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceState.activeBody) :
    ∃ sourceLabel sourceStateAfter,
      DTR.MultiStoreMachineStep
          declaredVariables
          messageServers
          sourceState
          sourceLabel
          sourceStateAfter ∧
      MultiStoreMachineLabelCorresponds
        sourceLabel
        targetLabel ∧
      StoreStateCorresponds
        sourceStateAfter
        targetStateAfter := by

  cases hTargetStep with

  | statement hStatement =>
      rcases
          multiStore_step_backward
            hStatement
            hStates
            hSourceBodyWellFormed
        with
          ⟨sourceStatementLabel,
           sourceStateAfter,
           hSourceStatement,
           hLabels,
           hFinalStates⟩

      exact
        ⟨DTR.MultiStoreMachineLabel.statement
            sourceStatementLabel,
         sourceStateAfter,
         DTR.MultiStoreMachineStep.statement
           hSourceStatement,
         MultiStoreMachineLabelCorresponds.statement
           hLabels,
         hFinalStates⟩

  | dispatch hDispatch =>
      rcases
          multiStore_dispatch_backward
            hDispatch
            hStates
            hTargetMicrostepsZero
        with
          ⟨selectedMessage,
           sourceServer,
           sourceStateAfter,
           hSourceDispatch,
           hReaction,
           hPending,
           hFinalStates⟩

      exact
        ⟨DTR.MultiStoreMachineLabel.dispatch
            selectedMessage
            sourceServer,
         sourceStateAfter,
         DTR.MultiStoreMachineStep.dispatch
           hSourceDispatch,
         MultiStoreMachineLabelCorresponds.dispatch
           hReaction
           hPending,
         hFinalStates⟩

end Correctness
end Relico
