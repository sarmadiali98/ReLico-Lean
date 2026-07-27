import Relico.Correctness.DetailedBoundPayloadInvariantMatches

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadInvariantMatches

#check Correctness.DetailedBoundPayloadSourceRuntimeInvariant
#check Correctness.DetailedBoundPayloadTargetRuntimeInvariant
#check Correctness.DetailedBoundPayloadForwardCanonicalPhase

#check Correctness.detailedBoundPayloadSourceRuntimeInvariant_stable
#check Correctness.detailedBoundPayloadSourceRuntimeInvariant_dispatchReady

#check Correctness.detailedBoundPayloadTargetRuntimeInvariant_stable
#check Correctness.detailedBoundPayloadTargetRuntimeInvariant_afterTime
#check Correctness.detailedBoundPayloadTargetRuntimeInvariant_dispatchReady

#check Correctness.detailedBoundPayloadForwardCanonicalPhase_stable
#check Correctness.detailedBoundPayloadForwardCanonicalPhase_futureAfterTime
#check Correctness.detailedBoundPayloadForwardCanonicalPhase_futureReady
#check Correctness.detailedBoundPayloadForwardCanonicalPhase_rejects_sameTimeAhead

#check Correctness.detailedBoundPayloadForwardPhaseCompatible_of_canonicalRuntimeInvariant
#check Correctness.detailedBoundPayloadBackwardPhaseCompatible_of_correspondence

#check Correctness.detailedBoundPayloadForwardMatch_of_canonicalRuntimeInvariant
#check Correctness.detailedBoundPayloadBackwardMatch_of_correspondence

theorem source_stable_runtime_interface
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState} :
    Correctness.DetailedBoundPayloadSourceRuntimeInvariant
          server
          (.stable sourceState) ↔
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceState.activeBody := by

  exact
    Correctness.detailedBoundPayloadSourceRuntimeInvariant_stable

theorem target_dispatchReady_runtime_interface
    {server : DTR.PayloadMessageServer}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter} :
    Correctness.DetailedBoundPayloadTargetRuntimeInvariant
          server
          (.dispatchReady
            targetBefore
            selectedAction
            targetAfter
            targetDispatch) ↔
      LF.BoundPayloadState.RuntimeInvariant
        targetAfter := by

  exact
    Correctness.detailedBoundPayloadTargetRuntimeInvariant_dispatchReady

theorem canonical_stable_interface
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState} :
    Correctness.DetailedBoundPayloadForwardCanonicalPhase
      (server := server)
      (.stable sourceState)
      (.stable targetState) := by

  exact
    Correctness.detailedBoundPayloadForwardCanonicalPhase_stable

theorem canonical_rejects_sameTimeAhead_interface
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter} :
    ¬ Correctness.DetailedBoundPayloadForwardCanonicalPhase
        (server := server)
        (.stable sourceState)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch) := by

  exact
    Correctness.detailedBoundPayloadForwardCanonicalPhase_rejects_sameTimeAhead

theorem automatic_forward_match_interface
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
    (hTargetInvariant :
      Correctness.DetailedBoundPayloadTargetRuntimeInvariant
        server
        targetBefore)
    (hCanonical :
      Correctness.DetailedBoundPayloadForwardCanonicalPhase
        sourceBefore
        targetBefore) :
    Correctness.DetailedBoundPayloadForwardMatch
      server
      sourceLabel
      sourceAfter
      targetBefore := by

  exact
    Correctness.detailedBoundPayloadForwardMatch_of_canonicalRuntimeInvariant
      hSourceStep
      hStates
      hTargetInvariant
      hCanonical

theorem automatic_backward_match_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore :
      DTR.DetailedBoundPayloadState
        server}
    {targetBefore targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    (hTargetStep :
      LF.DetailedBoundPayloadStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      targetLabel
      targetAfter
      sourceBefore := by

  exact
    Correctness.detailedBoundPayloadBackwardMatch_of_correspondence
      hTargetStep
      hStates

end DetailedBoundPayloadInvariantMatches
end Tests
end Relico
