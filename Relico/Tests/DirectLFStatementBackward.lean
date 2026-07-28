import Relico.Correctness.DirectLFStatementBackward

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFStatementBackward

/--
Every ordinary generated-LF multiple-message-server statement step can be
matched by the originating ordinary DTR statement step.

The append premise is relevant only when the current source statement is a
self-send.
-/
theorem ordinary_statement_backward
    {declaredVariables :
      List VarName}
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState targetStateAfter :
      LF.StoreState}
    {targetLabel :
      LF.Label}
    (hTargetStep :
      LF.MultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      Correctness.DirectLFStoreStateCorresponds
        messageServers
        sourceState
        targetState)
    (hStatementAppend :
      Correctness.DirectLFStatementAppendCompatible
        messageServers
        sourceState
        targetState)
    (hSourceBodyWellFormed :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceState.activeBody) :
    ∃ sourceLabel sourceStateAfter,
      DTR.MultiStoreStep
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          sourceState
          sourceLabel
          sourceStateAfter ∧
        Correctness.LabelCorresponds
          sourceLabel
          targetLabel ∧
        Correctness.DirectLFStoreStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter :=
  Correctness.directLF_multiStore_step_backward
    hTargetStep
    hStates
    hStatementAppend
    hSourceBodyWellFormed

#check Correctness.DirectLFStoreStateCorresponds
#check Correctness.DirectLFStatementAppendCompatible
#check Correctness.directLF_multiStore_step_forward
#check Correctness.directLF_multiStore_step_backward
#check ordinary_statement_backward

end DirectLFStatementBackward
end Tests
end Relico
