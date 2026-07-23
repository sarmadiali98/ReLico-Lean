import Relico.Correctness.StoreBackward
import Relico.Correctness.StoreDispatch
import Relico.Correctness.StoreForward
import Relico.DTR.StoreMachineSemantics
import Relico.LF.StoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between combined store-machine transition labels.
-/
inductive StoreMachineLabelCorresponds :
    DTR.StoreMachineLabel →
    LF.StoreMachineLabel →
    Prop where

  | statement
      {sourceLabel : DTR.Label}
      {targetLabel : LF.Label}
      (hLabels :
        LabelCorresponds
          sourceLabel
          targetLabel) :

      StoreMachineLabelCorresponds
        (DTR.StoreMachineLabel.statement
          sourceLabel)
        (LF.StoreMachineLabel.statement
          targetLabel)

  | dispatch
      {sourceMessage : DTR.PendingMessage}
      {targetAction : LF.PendingAction}
      (hPending :
        PendingCorresponds
          sourceMessage
          targetAction) :

      StoreMachineLabelCorresponds
        (DTR.StoreMachineLabel.dispatch
          sourceMessage)
        (LF.StoreMachineLabel.dispatch
          targetAction)

/--
Compatibility required for forward combined-machine simulation.

Statement transitions require no additional scheduler premise.
Dispatch transitions require compatibility with the LF tag scheduler.
-/
def StoreForwardMachineCompatible
    (sourceLabel : DTR.StoreMachineLabel)
    (sourceStateAfter : DTR.StoreState)
    (targetState : LF.StoreState) :
    Prop :=
  match sourceLabel with

  | DTR.StoreMachineLabel.statement _ =>
      True

  | DTR.StoreMachineLabel.dispatch selectedMessage =>
      StoreForwardDispatchCompatible
        selectedMessage
        sourceStateAfter.pendingMessages
        targetState

/--
Conditional forward simulation for one combined store-machine step.

Statement execution is unconditional. Dispatch execution uses the
explicit LF scheduling compatibility premise.
-/
theorem storeMachineStep_forward
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {sourceState sourceStateAfter : DTR.StoreState}
    {sourceLabel : DTR.StoreMachineLabel}
    {targetState : LF.StoreState}
    (hSourceStep :
      DTR.StoreMachineStep
        declaredVariables
        messageServer
        messageBody
        sourceState
        sourceLabel
        sourceStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hCompatible :
      StoreForwardMachineCompatible
        sourceLabel
        sourceStateAfter
        targetState) :
    ∃ targetLabel targetStateAfter,
      LF.StoreMachineStep
          declaredVariables
          (Translation.actionNameFor
            messageServer)
          (Translation.compileBody
            messageBody)
          targetState
          targetLabel
          targetStateAfter ∧
      StoreMachineLabelCorresponds
        sourceLabel
        targetLabel ∧
      StoreStateCorresponds
        sourceStateAfter
        targetStateAfter := by

  cases hSourceStep with

  | statement hStatement =>
      rcases
          store_step_forward
            hStatement
            hStates
        with
          ⟨targetStatementLabel,
           targetStateAfter,
           hTargetStatement,
           hLabels,
           hFinalStates⟩

      exact
        ⟨LF.StoreMachineLabel.statement
            targetStatementLabel,
         targetStateAfter,
         LF.StoreMachineStep.statement
           hTargetStatement,
         StoreMachineLabelCorresponds.statement
           hLabels,
         hFinalStates⟩

  | dispatch hDispatch =>
      rcases
          store_dispatch_forward_of_compatible
            hDispatch
            hStates
            (by
              simpa [
                StoreForwardMachineCompatible
              ] using
                hCompatible)
        with
          ⟨selectedAction,
           targetStateAfter,
           hTargetDispatch,
           hPending,
           hFinalStates⟩

      exact
        ⟨LF.StoreMachineLabel.dispatch
            selectedAction,
         targetStateAfter,
         LF.StoreMachineStep.dispatch
           hTargetDispatch,
         StoreMachineLabelCorresponds.dispatch
           hPending,
         hFinalStates⟩

/--
Backward simulation for one combined store-machine step.

Generated statement transitions require source-body structural
well-formedness. Generated dispatch transitions require the source
pending-message target invariant.
-/
theorem storeMachineStep_backward
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {sourceState : DTR.StoreState}
    {targetState targetStateAfter : LF.StoreState}
    {targetLabel : LF.StoreMachineLabel}
    (hTargetStep :
      LF.StoreMachineStep
        declaredVariables
        (Translation.actionNameFor
          messageServer)
        (Translation.compileBody
          messageBody)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hSourceBodyWellFormed :
      DTR.Body.StoreWellFormed
        declaredVariables
        messageServer
        sourceState.activeBody)
    (hPendingTargets :
      ∀ pendingMessage,
        pendingMessage ∈
          sourceState.pendingMessages →
        pendingMessage.name =
          messageServer) :
    ∃ sourceLabel sourceStateAfter,
      DTR.StoreMachineStep
          declaredVariables
          messageServer
          messageBody
          sourceState
          sourceLabel
          sourceStateAfter ∧
      StoreMachineLabelCorresponds
        sourceLabel
        targetLabel ∧
      StoreStateCorresponds
        sourceStateAfter
        targetStateAfter := by

  cases hTargetStep with

  | statement hStatement =>
      rcases
          store_step_backward
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
        ⟨DTR.StoreMachineLabel.statement
            sourceStatementLabel,
         sourceStateAfter,
         DTR.StoreMachineStep.statement
           hSourceStatement,
         StoreMachineLabelCorresponds.statement
           hLabels,
         hFinalStates⟩

  | dispatch hDispatch =>
      rcases
          store_dispatch_backward
            hDispatch
            hStates
            hPendingTargets
        with
          ⟨selectedMessage,
           sourceStateAfter,
           hSourceDispatch,
           hPending,
           hFinalStates⟩

      exact
        ⟨DTR.StoreMachineLabel.dispatch
            selectedMessage,
         sourceStateAfter,
         DTR.StoreMachineStep.dispatch
           hSourceDispatch,
         StoreMachineLabelCorresponds.dispatch
           hPending,
         hFinalStates⟩

end Correctness
end Relico
