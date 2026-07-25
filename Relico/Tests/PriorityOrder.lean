import Relico.Correctness.PriorityOrder
import Relico.Tests.PriorityDispatchScheduling

set_option autoImplicit false

namespace Relico
namespace Tests

theorem priority_order_transport_equivalence :
    DTR.PriorityServerNamePrecedesOrEqual
        dispatchPriorityHighName
        dispatchPriorityLowName
        dispatchPriorityServers ↔
      LF.ReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          dispatchPriorityHighName)
        (Translation.actionNameFor
          dispatchPriorityLowName)
        dispatchPriorityReactions := by

  exact
    Correctness.priorityServerNamePrecedesOrEqual_compileMessageReactions
        dispatchPriorityHighName
        dispatchPriorityLowName
        dispatchPriorityServers

theorem priority_order_transport_high_before_low :
    LF.ReactionActionPrecedesOrEqual
      (Translation.actionNameFor
        dispatchPriorityHighName)
      (Translation.actionNameFor
        dispatchPriorityLowName)
      dispatchPriorityReactions := by

  apply
    Correctness.priorityServerOrder_implies_reactionOrder

  native_decide

theorem priority_order_transport_low_not_before_high :
    ¬ LF.ReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          dispatchPriorityLowName)
        (Translation.actionNameFor
          dispatchPriorityHighName)
        dispatchPriorityReactions := by

  intro hTargetOrder

  have hSourceOrder :
      DTR.PriorityServerNamePrecedesOrEqual
        dispatchPriorityLowName
        dispatchPriorityHighName
        dispatchPriorityServers :=

    Correctness.reactionOrder_implies_priorityServerOrder
        hTargetOrder

  exact
    (by
      native_decide :
      ¬ DTR.PriorityServerNamePrecedesOrEqual
          dispatchPriorityLowName
          dispatchPriorityHighName
          dispatchPriorityServers)
      hSourceOrder

end Tests
end Relico
