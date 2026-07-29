import Relico.Correctness.DirectLFDetailedPhaseWeakBisimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFDetailedPhaseWeakBisimulation

theorem package_interface
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer) :
    Correctness.DirectLFDetailedPhaseWeakBisimulation
      declaredVariables
      messageServers := by

  exact
    Correctness.directLFDetailedRuntime_phaseWeakBisimulation
      declaredVariables
      messageServers

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.forwardStatementMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.forwardTimeAdvanceMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.forwardConsumeAfterTimeMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.forwardConsumeReadyMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.forwardConsumeNowMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardStatementMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardTimeAdvanceMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardMicrostepAfterTimeMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardMicrostepSameTimeMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardConsumeAfterTimeZeroMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardConsumeReadyFutureMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardConsumeReadySameTimeMatch

#check
  Correctness.DirectLFDetailedPhaseWeakBisimulation.backwardConsumeNowMatch

#check
  Correctness.directLFDetailedRuntime_phaseWeakBisimulation

end DirectLFDetailedPhaseWeakBisimulation
end Tests
end Relico
