import Relico.Correctness.RuntimeInvariant
import Relico.DTR.DispatchSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
DTR dispatch preserves runtime well-formedness for a well-formed model.

The dispatched message is removed from the pending-message list. Every
remaining occurrence was already present before dispatch. The newly
activated body is the model's well-formed message-server body.
-/
theorem dtrDispatch_preserves_runtimeWellFormed
    {model : DTR.Model}
    {stateBefore stateAfter : DTR.State}
    {selectedMessage : DTR.PendingMessage}
    (hDispatch :
      DTR.DispatchStep
        model
        stateBefore
        selectedMessage
        stateAfter)
    (hModel :
      DTR.Model.WellFormed model)
    (hState :
      DTR.State.WellFormed
        model
        stateBefore) :
    DTR.State.WellFormed
      model
      stateAfter := by

  cases hDispatch with

  | fire
      currentTime
      stateValue
      pendingMessages
      remainingMessages
      selectedMessage
      hRemoved
      hEarliest
      hNotPast
      hTarget =>

      refine {
        activeBodyWellFormed :=
          hModel.messageServerBodyWellFormed

        pendingMessagesWellFormed := ?_
      }

      intro pendingMessage hMembership

      apply
        hState.pendingMessagesWellFormed
          pendingMessage

      exact
        Occurrence.RemovesOne.remaining_mem
          hRemoved
          hMembership

end Correctness
end Relico
