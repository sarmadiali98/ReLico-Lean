import Relico.Correctness.MultiStorePayloadDetailedObservableWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadDetailedObservableWeakExecution

#check
  DTR.DetailedMultiStorePayloadObservable

#check
  LF.DetailedMultiStorePayloadObservable

#check
  DTR.DetailedMultiStorePayloadLabel.toObservable

#check
  LF.DetailedMultiStorePayloadLabel.toObservable

#check
  DTR.detailedMultiStorePayloadObservableTrace

#check
  LF.detailedMultiStorePayloadObservableTrace

#check
  Correctness.MultiStorePayloadDetailedObservableCorresponds

#check
  Correctness.MultiStorePayloadDetailedObservableOptionCorresponds

#check
  Correctness.MultiStorePayloadDetailedObservableTraceCorresponds

#check
  Correctness.MultiStorePayloadDetailedLabelCorresponds.observableOption

#check
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds.observableProjection

#check
  Correctness.MultiStorePayloadDetailedObservableTraceCorresponds.length_eq

#check
  Correctness.MultiStorePayloadDetailedObservableTraceCorresponds.append

#check
  Correctness.multiStorePayloadDetailedSteps_forward_observable_of_compatible

#check
  Correctness.multiStorePayloadDetailedSteps_backward_observable_of_compatible

theorem observable_projection_interface
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    {targetLabels :
      List LF.DetailedMultiStorePayloadLabel}
    (hTrace :
      Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    Correctness.MultiStorePayloadDetailedObservableTraceCorresponds
      (DTR.detailedMultiStorePayloadObservableTrace sourceLabels)
      (LF.detailedMultiStorePayloadObservableTrace targetLabels) := by

  exact hTrace.observableProjection

#print axioms
  Correctness.MultiStorePayloadDetailedLabelCorresponds.observableOption

#print axioms
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds.observableProjection

#print axioms
  Correctness.MultiStorePayloadDetailedObservableTraceCorresponds.length_eq

#print axioms
  Correctness.MultiStorePayloadDetailedObservableTraceCorresponds.append

#print axioms
  Correctness.multiStorePayloadDetailedSteps_forward_observable_of_compatible

#print axioms
  Correctness.multiStorePayloadDetailedSteps_backward_observable_of_compatible

#print axioms
  observable_projection_interface

end MultiStorePayloadDetailedObservableWeakExecution
end Tests
end Relico
