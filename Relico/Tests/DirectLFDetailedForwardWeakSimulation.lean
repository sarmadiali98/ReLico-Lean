import Relico.Correctness.DirectLFDetailedForwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFDetailedForwardWeakSimulation

example :
    Correctness.DirectLFDetailedLabelCorresponds
      DTR.DetailedMultiStoreLabel.tau
      LF.DetailedMultiStoreLabel.tau :=
  Correctness.DirectLFDetailedLabelCorresponds.tau

example
    (before after : LF.Tag) :
    Correctness.DirectLFDetailedLabelCorresponds
      DTR.DetailedMultiStoreLabel.tau
      (LF.DetailedMultiStoreLabel.microstepAdvance
        before
        after) :=
  Correctness.DirectLFDetailedLabelCorresponds.microstep
    before
    after

#check Correctness.DirectLFDetailedLabelCorresponds
#check Correctness.DirectLFDetailedForwardMatch

#check
  Correctness.directLFDetailedRuntime_statement_forward_weak

#check
  Correctness.directLFDetailedRuntime_timeAdvance_forward_weak

#check
  Correctness.directLFDetailedRuntime_consume_afterTime_forward_weak

#check
  Correctness.directLFDetailedRuntime_consume_ready_forward_weak

#check
  Correctness.directLFDetailedRuntime_consumeNow_forward_weak

#check
  Correctness.DirectLFDetailedForwardMatch.target_corresponds

end DirectLFDetailedForwardWeakSimulation
end Tests
end Relico
