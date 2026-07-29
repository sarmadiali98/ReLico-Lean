import Relico.Correctness.DirectLFDetailedObservableWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFDetailedObservableWeakExecution

#check
  Correctness.DirectLFDetailedObservableCorresponds

#check
  Correctness.DirectLFDetailedObservableOptionCorresponds

#check
  Correctness.DirectLFDetailedObservableTraceCorresponds

#check
  Correctness.DirectLFDetailedObservableTraceCorresponds.length_eq

#check
  Correctness.DirectLFDetailedObservableTraceCorresponds.append

#check
  Correctness.DirectLFDetailedLabelCorresponds.observableOption

#check
  Correctness.DirectLFDetailedWeakLabelTraceCorresponds.observableProjection

#check
  Correctness.directLFDetailedSteps_forward_observable_of_compatible

#check
  Correctness.directLFDetailedSteps_backward_observable_of_compatible

theorem corresponding_label_preserves_projection
    {sourceLabel :
      DTR.DetailedMultiStoreLabel}
    {targetLabel :
      LF.DetailedMultiStoreLabel}
    (hLabels :
      Correctness.DirectLFDetailedLabelCorresponds
        sourceLabel
        targetLabel) :
    Correctness.DirectLFDetailedObservableOptionCorresponds
      sourceLabel.toObservable
      targetLabel.toObservable := by

  exact
    hLabels.observableOption

theorem corresponding_trace_preserves_observables
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (hTrace :
      Correctness.DirectLFDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    Correctness.DirectLFDetailedObservableTraceCorresponds
      (DTR.detailedObservableTrace
        sourceLabels)
      (LF.detailedObservableTrace
        targetLabels) := by

  exact
    hTrace.observableProjection

example :
    Correctness.DirectLFDetailedObservableTraceCorresponds
      []
      [] := by

  exact
    Correctness.DirectLFDetailedObservableTraceCorresponds.nil

end DirectLFDetailedObservableWeakExecution
end Tests
end Relico
