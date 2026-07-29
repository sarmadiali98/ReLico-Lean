import Relico.Correctness.DirectLFDetailedFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFDetailedFiniteWeakExecution

#check
  Correctness.DirectLFDetailedForwardPhaseCompatible

#check
  Correctness.DirectLFDetailedBackwardPhaseCompatible

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.forwardStep

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardStep

#check
  Correctness.directLFDetailedRuntime_phaseWeakBisimulation

example
    {messageServers : List DTR.MessageServer}
    (sourceBefore sourceAfter : DTR.StoreState)
    (targetBefore : LF.StoreState) :
    Correctness.DirectLFDetailedForwardPhaseCompatible
        (messageServers := messageServers)
        (DTR.DetailedMultiStoreState.stable
          (messageServers := messageServers)
          sourceBefore)
        DTR.DetailedMultiStoreLabel.tau
        (DTR.DetailedMultiStoreState.stable
          (messageServers := messageServers)
          sourceAfter)
        (LF.DetailedMultiStoreState.stable
          (messageReactions :=
            Translation.compileMessageReactions
              messageServers)
          targetBefore) =
      Correctness.DirectLFStatementAppendCompatible
        messageServers
        sourceBefore
        targetBefore := by

  rfl

example
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    (sourceBefore : DTR.StoreState)
    (targetBefore targetAfter : LF.StoreState) :
    Correctness.DirectLFDetailedBackwardPhaseCompatible
        (declaredVariables := declaredVariables)
        (messageServers := messageServers)
        (DTR.DetailedMultiStoreState.stable
          (messageServers := messageServers)
          sourceBefore)
        (LF.DetailedMultiStoreState.stable
          (messageReactions :=
            Translation.compileMessageReactions
              messageServers)
          targetBefore)
        LF.DetailedMultiStoreLabel.tau
        (LF.DetailedMultiStoreState.stable
          (messageReactions :=
            Translation.compileMessageReactions
              messageServers)
          targetAfter) =
      (Correctness.DirectLFStatementAppendCompatible
          messageServers
          sourceBefore
          targetBefore ∧
        DTR.Body.MultiStoreWellFormed
          declaredVariables
          (DTR.messageServerNames messageServers)
          sourceBefore.activeBody) := by

  rfl

#check
  Correctness.DirectLFDetailedWeakLabelTraceCorresponds

#check
  Correctness.DirectLFDetailedWeakLabelTraceCorresponds.nil

#check
  Correctness.DirectLFDetailedWeakLabelTraceCorresponds.cons

#check
  Correctness.DirectLFDetailedWeakLabelTraceCorresponds.length_eq

#check
  Correctness.DirectLFDetailedWeakLabelTraceCorresponds.append

#check
  Correctness.DirectLFDetailedForwardLabelsCompatible

#check
  Correctness.DirectLFDetailedForwardStepsCompatible

#check
  Correctness.DirectLFDetailedBackwardLabelsCompatible

#check
  Correctness.DirectLFDetailedBackwardStepsCompatible

#check
  Correctness.directLFDetailedSteps_forward_of_compatible

#check
  Correctness.directLFDetailedSteps_backward_of_compatible

example :
    Correctness.DirectLFDetailedWeakLabelTraceCorresponds
      []
      [] := by

  exact
    Correctness.DirectLFDetailedWeakLabelTraceCorresponds.nil

example
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (hTrace :
      Correctness.DirectLFDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    sourceLabels.length =
      targetLabels.length := by

  exact hTrace.length_eq

end DirectLFDetailedFiniteWeakExecution
end Tests
end Relico
