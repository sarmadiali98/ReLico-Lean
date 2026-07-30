import Relico.Correctness.MultiStorePayloadDetailedFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadDetailedFiniteWeakExecution

#check
  DTR.DetailedMultiStorePayloadSteps

#check
  DTR.DetailedMultiStorePayloadSteps.refl

#check
  DTR.DetailedMultiStorePayloadSteps.cons

#check
  DTR.DetailedMultiStorePayloadSteps.single

#check
  DTR.DetailedMultiStorePayloadSteps.append

#check
  LF.DetailedMultiStorePayloadSteps

#check
  LF.DetailedMultiStorePayloadSteps.refl

#check
  LF.DetailedMultiStorePayloadSteps.cons

#check
  LF.DetailedMultiStorePayloadSteps.single

#check
  LF.DetailedMultiStorePayloadSteps.append

#check
  Correctness.MultiStorePayloadDetailedForwardLabelsCompatible

#check
  Correctness.MultiStorePayloadDetailedForwardStepsCompatible

#check
  Correctness.MultiStorePayloadDetailedBackwardLabelsCompatible

#check
  Correctness.MultiStorePayloadDetailedBackwardStepsCompatible

#check
  Correctness.multiStorePayloadDetailedForwardLabelsCompatible_nil

#check
  Correctness.multiStorePayloadDetailedBackwardLabelsCompatible_nil

#check
  Correctness.multiStorePayloadDetailedSteps_forward_of_compatible

#check
  Correctness.multiStorePayloadDetailedSteps_backward_of_compatible

#print axioms
  DTR.DetailedMultiStorePayloadSteps.append

#print axioms
  LF.DetailedMultiStorePayloadSteps.append

#print axioms
  Correctness.multiStorePayloadDetailedForwardLabelsCompatible_nil

#print axioms
  Correctness.multiStorePayloadDetailedBackwardLabelsCompatible_nil

#print axioms
  Correctness.multiStorePayloadDetailedSteps_forward_of_compatible

#print axioms
  Correctness.multiStorePayloadDetailedSteps_backward_of_compatible

end MultiStorePayloadDetailedFiniteWeakExecution
end Tests
end Relico
