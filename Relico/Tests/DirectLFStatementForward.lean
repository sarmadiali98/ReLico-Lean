import Relico.Correctness.DirectLFStatementForward

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFStatementForward

/--
The direct state relation contains occurrence-preserving correspondence
between the source pending-message bag and the LF action queue.
-/
theorem state_correspondence_contains_bag_correspondence
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState}
    (hStates :
      Correctness.DirectLFStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.DirectLFBagQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions :=
  hStates.toBagQueueCorresponds

/--
An ordinary DTR multiple-message-server statement step has a corresponding
ordinary generated-LF statement step.

For self-send, the append premise is the approved local non-overtaking
obligation. For assignment, the premise reduces to `True`.
-/
theorem ordinary_statement_forward
    {declaredVariables :
      List VarName}
    {messageServers :
      List DTR.MessageServer}
    {sourceState sourceStateAfter :
      DTR.StoreState}
    {sourceLabel :
      DTR.Label}
    {targetState :
      LF.StoreState}
    (hSourceStep :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceState
        sourceLabel
        sourceStateAfter)
    (hStates :
      Correctness.DirectLFStoreStateCorresponds
        messageServers
        sourceState
        targetState)
    (hStatementAppend :
      Correctness.DirectLFStatementAppendCompatible
        messageServers
        sourceState
        targetState) :
    ∃ targetLabel targetStateAfter,
      LF.MultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          targetState
          targetLabel
          targetStateAfter ∧
        Correctness.LabelCorresponds
          sourceLabel
          targetLabel ∧
        Correctness.DirectLFStoreStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter :=
  Correctness.directLF_multiStore_step_forward
    hSourceStep
    hStates
    hStatementAppend

#check Correctness.DirectLFStoreStateCorresponds

#check
  Correctness.DirectLFStoreStateCorresponds.toBagQueueCorresponds

#check Correctness.DirectLFStatementAppendCompatible
#check Correctness.directLF_multiStore_step_forward

#check state_correspondence_contains_bag_correspondence
#check ordinary_statement_forward

end DirectLFStatementForward
end Tests
end Relico
