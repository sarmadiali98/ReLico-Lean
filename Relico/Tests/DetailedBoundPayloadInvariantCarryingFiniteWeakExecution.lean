import Relico.Correctness.DetailedBoundPayloadInvariantCarryingFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadInvariantCarryingFiniteWeakExecution

#check Correctness.DetailedBoundPayloadForwardInvariantMatch
#check Correctness.detailedBoundPayloadSourceRuntimeInvariant_preserved
#check Correctness.detailedBoundPayloadForwardInvariantMatch
#check Correctness.detailedBoundPayloadSteps_forward_with_invariants

theorem source_runtime_invariant_preservation_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    (hSourceStep :
      DTR.DetailedBoundPayloadStep
        server
        sourceBefore
        sourceLabel
        sourceAfter)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body)
    (hSourceInvariant :
      Correctness.DetailedBoundPayloadSourceRuntimeInvariant
        server
        sourceBefore) :
    Correctness.DetailedBoundPayloadSourceRuntimeInvariant
      server
      sourceAfter := by

  exact
    Correctness.detailedBoundPayloadSourceRuntimeInvariant_preserved
      hSourceStep
      hServerTiming
      hSourceInvariant

theorem forward_invariant_match_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hSourceStep :
      DTR.DetailedBoundPayloadStep
        server
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hSourceInvariant :
      Correctness.DetailedBoundPayloadSourceRuntimeInvariant
        server
        sourceBefore)
    (hTargetInvariant :
      Correctness.DetailedBoundPayloadTargetRuntimeInvariant
        server
        targetBefore)
    (hCanonical :
      Correctness.DetailedBoundPayloadForwardCanonicalPhase
        sourceBefore
        targetBefore)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
    Correctness.DetailedBoundPayloadForwardInvariantMatch
      server
      sourceLabel
      sourceAfter
      targetBefore := by

  exact
    Correctness.detailedBoundPayloadForwardInvariantMatch
      hSourceStep
      hStates
      hSourceInvariant
      hTargetInvariant
      hCanonical
      hServerTiming

theorem forward_invariant_match_has_recursive_endpoint
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hSourceStep :
      DTR.DetailedBoundPayloadStep
        server
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hSourceInvariant :
      Correctness.DetailedBoundPayloadSourceRuntimeInvariant
        server
        sourceBefore)
    (hTargetInvariant :
      Correctness.DetailedBoundPayloadTargetRuntimeInvariant
        server
        targetBefore)
    (hCanonical :
      Correctness.DetailedBoundPayloadForwardCanonicalPhase
        sourceBefore
        targetBefore)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
    ∃ targetLabel targetAfter,
      LF.DetailedBoundPayloadWeakStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          targetLabel
          targetAfter ∧

        Correctness.DetailedBoundPayloadLabelCorresponds
          sourceLabel
          targetLabel ∧

        Correctness.DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧

        Correctness.DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        Correctness.DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        Correctness.DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  exact
    Correctness.detailedBoundPayloadForwardInvariantMatch
      hSourceStep
      hStates
      hSourceInvariant
      hTargetInvariant
      hCanonical
      hServerTiming

theorem finite_forward_with_invariants_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
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
    (hSourceInvariant :
      Correctness.DetailedBoundPayloadSourceRuntimeInvariant
        server
        sourceBefore)
    (hTargetInvariant :
      Correctness.DetailedBoundPayloadTargetRuntimeInvariant
        server
        targetBefore)
    (hCanonical :
      Correctness.DetailedBoundPayloadForwardCanonicalPhase
        sourceBefore
        targetBefore)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
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
          targetAfter ∧

        Correctness.DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) ∧

        Correctness.DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        Correctness.DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        Correctness.DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  exact
    Correctness.detailedBoundPayloadSteps_forward_with_invariants
      hSourceSteps
      hStates
      hSourceInvariant
      hTargetInvariant
      hCanonical
      hServerTiming

end DetailedBoundPayloadInvariantCarryingFiniteWeakExecution
end Tests
end Relico
