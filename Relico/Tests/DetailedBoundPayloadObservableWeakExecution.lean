import Relico.Correctness.DetailedBoundPayloadObservableWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadObservableWeakExecution

#check Correctness.DetailedBoundPayloadObservableCorresponds
#check Correctness.DetailedBoundPayloadObservableOptionCorresponds
#check Correctness.DetailedBoundPayloadObservableTraceCorresponds

#check Correctness.DetailedBoundPayloadLabelCorresponds.observableOption

#check
  Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds.observableProjection

#check
  Correctness.DetailedBoundPayloadObservableTraceCorresponds.length_eq

#check
  Correctness.DetailedBoundPayloadObservableTraceCorresponds.append

/--
A payload-corresponding pending occurrence induces a paper-level observable
consumption event that preserves name translation, logical time, and the
complete ordered payload.
-/
theorem consume_observable_interface
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hOccurrence :
      Correctness.PendingPayloadCorresponds
        sourceMessage
        targetAction) :
    Correctness.DetailedBoundPayloadObservableCorresponds
      (.consume
        sourceMessage.name
        sourceMessage.arrivalTime
        sourceMessage.payload)
      (.consume
        targetAction.name
        targetAction.tag.time
        targetAction.payload) := by

  exact
    Correctness.DetailedBoundPayloadObservableCorresponds.consume
      hOccurrence.occurrence.actionName
      hOccurrence.occurrence.logicalTime
      hOccurrence.payload

theorem observable_projection_interface
    {sourceLabels :
      List DTR.DetailedBoundPayloadLabel}
    {targetLabels :
      List LF.DetailedBoundPayloadLabel}
    (hLabels :
      Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    Correctness.DetailedBoundPayloadObservableTraceCorresponds
      (DTR.detailedBoundPayloadObservableTrace
        sourceLabels)
      (LF.detailedBoundPayloadObservableTrace
        targetLabels) := by

  exact
    Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds.observableProjection
      hLabels

theorem forward_observable_finite_interface
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
          targetAfter ∧
        Correctness.DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) := by

  exact
    Correctness.detailedBoundPayloadSteps_forward_observable_of_compatible
      hSourceSteps
      hStates
      hCompatible

theorem backward_observable_finite_interface
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
          targetAfter ∧
        Correctness.DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) := by

  exact
    Correctness.detailedBoundPayloadSteps_backward_observable_of_compatible
      hTargetSteps
      hStates
      hCompatible

end DetailedBoundPayloadObservableWeakExecution
end Tests
end Relico
