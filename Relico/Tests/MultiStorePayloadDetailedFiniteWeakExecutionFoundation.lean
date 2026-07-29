import Relico.Correctness.MultiStorePayloadDetailedFiniteWeakExecutionFoundation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadDetailedFiniteWeakExecutionFoundation

#check
  DTR.DetailedMultiStorePayloadWeakSteps

#check
  DTR.DetailedMultiStorePayloadWeakSteps.refl

#check
  DTR.DetailedMultiStorePayloadWeakSteps.cons

#check
  DTR.DetailedMultiStorePayloadWeakSteps.single

#check
  DTR.DetailedMultiStorePayloadWeakSteps.append

#check
  LF.DetailedMultiStorePayloadWeakSteps

#check
  LF.DetailedMultiStorePayloadWeakSteps.refl

#check
  LF.DetailedMultiStorePayloadWeakSteps.cons

#check
  LF.DetailedMultiStorePayloadWeakSteps.single

#check
  LF.DetailedMultiStorePayloadWeakSteps.append

#check
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds

#check
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds.nil

#check
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds.cons

#check
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds.length_eq

#check
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds.append

#check
  Correctness.MultiStorePayloadDetailedForwardPhaseCompatible

#check
  Correctness.MultiStorePayloadDetailedBackwardPhaseCompatible

#check
  Correctness.multiStorePayloadDetailedRuntime_forwardStep

#check
  Correctness.multiStorePayloadDetailedRuntime_backwardStep

#print axioms
  DTR.DetailedMultiStorePayloadWeakSteps.append

#print axioms
  LF.DetailedMultiStorePayloadWeakSteps.append

#print axioms
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds.length_eq

#print axioms
  Correctness.MultiStorePayloadDetailedWeakLabelTraceCorresponds.append

#print axioms
  Correctness.multiStorePayloadDetailedRuntime_forwardStep

#print axioms
  Correctness.multiStorePayloadDetailedRuntime_backwardStep

end MultiStorePayloadDetailedFiniteWeakExecutionFoundation
end Tests
end Relico
