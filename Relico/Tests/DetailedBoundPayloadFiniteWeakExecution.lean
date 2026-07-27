import Relico.Correctness.DetailedBoundPayloadFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadFiniteWeakExecution

#check DTR.DetailedBoundPayloadWeakSteps
#check LF.DetailedBoundPayloadWeakSteps

#check Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds
#check Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds.length_eq
#check Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds.append

#check Correctness.DetailedBoundPayloadForwardPhaseCompatible
#check Correctness.DetailedBoundPayloadBackwardPhaseCompatible

#check Correctness.DetailedBoundPayloadPhaseWeakBisimulation.forwardStep
#check Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardStep

#check Correctness.DetailedBoundPayloadForwardLabelsCompatible
#check Correctness.DetailedBoundPayloadForwardStepsCompatible
#check Correctness.DetailedBoundPayloadBackwardLabelsCompatible
#check Correctness.DetailedBoundPayloadBackwardStepsCompatible

theorem forward_finite_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState server}
    {sourceLabels :
      List DTR.DetailedBoundPayloadLabel}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hSourceSteps :
      DTR.DetailedBoundPayloadSteps
        server
        sourceBefore
        sourceLabels
        sourceAfter)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hCompatible :
      Correctness.DetailedBoundPayloadForwardStepsCompatible
        server
        hSourceSteps
        targetBefore) :
    ∃ targetLabels targetAfter,
      LF.DetailedBoundPayloadWeakSteps
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          targetLabels
          targetAfter ∧
        Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        Correctness.DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter := by

  exact
    Correctness.detailedBoundPayloadSteps_forward_of_compatible
      hSourceSteps
      hStates
      hCompatible

theorem backward_finite_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore :
      DTR.DetailedBoundPayloadState server}
    {targetBefore targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {targetLabels :
      List LF.DetailedBoundPayloadLabel}
    (hTargetSteps :
      LF.DetailedBoundPayloadSteps
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        targetLabels
        targetAfter)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hCompatible :
      Correctness.DetailedBoundPayloadBackwardStepsCompatible
        server
        sourceBefore
        hTargetSteps) :
    ∃ sourceLabels sourceAfter,
      DTR.DetailedBoundPayloadWeakSteps
          server
          sourceBefore
          sourceLabels
          sourceAfter ∧
        Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        Correctness.DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter := by

  exact
    Correctness.detailedBoundPayloadSteps_backward_of_compatible
      hTargetSteps
      hStates
      hCompatible

end DetailedBoundPayloadFiniteWeakExecution
end Tests
end Relico
