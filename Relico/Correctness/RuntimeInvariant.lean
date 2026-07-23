import Relico.DTR.RuntimeWellFormed

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
The assignment and self-send rules preserve DTR runtime
well-formedness.
-/
theorem dtrStep_preserves_runtimeWellFormed
    {model : DTR.Model}
    {stateBefore stateAfter : DTR.State}
    {label : DTR.Label}
    (hStep :
      DTR.Step
        model
        stateBefore
        label
        stateAfter)
    (hState :
      DTR.State.WellFormed
        model
        stateBefore) :
    DTR.State.WellFormed
      model
      stateAfter := by

  cases hStep with

  | assign
      currentTime
      stateValue
      pendingMessages
      target
      expression
      remaining
      hTarget =>

      have hBody :=
        (DTR.Body.wellFormed_cons
          model.reactiveClass.stateVar
          model.reactiveClass.messageServer.name
          (DTR.Stmt.assign target expression)
          remaining).mp
          hState.activeBodyWellFormed

      exact {
        activeBodyWellFormed :=
          hBody.2

        pendingMessagesWellFormed :=
          hState.pendingMessagesWellFormed
      }

  | selfSend
      currentTime
      stateValue
      pendingMessages
      targetMessage
      delay
      remaining
      hTarget =>

      have hBody :=
        (DTR.Body.wellFormed_cons
          model.reactiveClass.stateVar
          model.reactiveClass.messageServer.name
          (DTR.Stmt.selfSend targetMessage delay)
          remaining).mp
          hState.activeBodyWellFormed

      refine {
        activeBodyWellFormed :=
          hBody.2

        pendingMessagesWellFormed := ?_
      }

      intro pendingMessage hMembership

      rw [List.mem_append] at hMembership
      rcases hMembership with
        hExisting | hNew

      · exact
          hState.pendingMessagesWellFormed
            pendingMessage
            hExisting

      · simp only [List.mem_singleton] at hNew
        subst pendingMessage
        exact hTarget

end Correctness
end Relico
