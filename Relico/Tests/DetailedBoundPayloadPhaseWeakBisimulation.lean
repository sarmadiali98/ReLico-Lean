import Relico.Correctness.DetailedBoundPayloadPhaseWeakBisimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadPhaseWeakBisimulation

/--
The public package theorem exposes the complete payload-aware phase-indexed
weak-bisimulation interface.
-/
theorem package_interface
    (server : DTR.PayloadMessageServer) :
    Correctness.DetailedBoundPayloadPhaseWeakBisimulation
      server := by

  exact
    Correctness.detailedBoundPayload_phaseWeakBisimulation
      server

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.forwardStatementMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.forwardTimeAdvanceMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.forwardConsumeAfterTimeMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.forwardConsumeReadyMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.forwardConsumeNowMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardStatementMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardTimeAdvanceMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardMicrostepAfterTimeMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardMicrostepSameTimeMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardConsumeAfterTimeZeroMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardConsumeReadyFutureMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardConsumeReadySameTimeMatch

#check
  Correctness.DetailedBoundPayloadPhaseWeakBisimulation.backwardConsumeNowMatch

end DetailedBoundPayloadPhaseWeakBisimulation
end Tests
end Relico
