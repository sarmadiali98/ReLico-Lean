import Relico.DTR.StoreMachineSemantics
import Relico.DTR.StoreTrace

set_option autoImplicit false

namespace Relico

namespace Occurrence
namespace RemovesOne

/--
Every occurrence remaining after one removal belonged to the original
list.
-/
theorem remaining_mem_of_removesOne
    {α : Type}
    {selected value : α}
    {original remaining : List α}
    (hRemove :
      Occurrence.RemovesOne
        selected
        original
        remaining)
    (hMember :
      value ∈ remaining) :
    value ∈ original := by

  induction hRemove with

  | head remaining =>
      simp only [List.mem_cons]

      exact Or.inr hMember

  | tail head hTail inductionHypothesis =>
      simp only [List.mem_cons] at hMember ⊢

      rcases hMember with
        hHead | hRemaining

      · exact Or.inl hHead

      · exact
          Or.inr
            (inductionHypothesis
              hRemaining)

end RemovesOne
end Occurrence

namespace DTR
namespace StoreState

/--
Runtime well-formedness for a DTR state backed by a finite store.

The invariant records:

- coverage of every declared state variable;
- structural validity of the active body;
- the fact that every pending message targets the declared server.
-/
structure RuntimeWellFormed
    (declaredVariables : List VarName)
    (messageServer : MsgName)
    (state : DTR.StoreState) :
    Prop where

  coverage :
    DTR.StoreState.Covers
      declaredVariables
      state

  activeBody :
    DTR.Body.StoreWellFormed
      declaredVariables
      messageServer
      state.activeBody

  pendingTargets :
    ∀ pendingMessage,
      pendingMessage ∈
        state.pendingMessages →
      pendingMessage.name =
        messageServer

end StoreState

namespace StoreStep

/--
Statement execution preserves the pending-message target invariant.

Assignments leave the queue unchanged. A self-send adds exactly one
message targeting the declared message server.
-/
theorem preserves_pendingTargets
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {before after : DTR.StoreState}
    {label : DTR.Label}
    (hStep :
      DTR.StoreStep
        declaredVariables
        messageServer
        before
        label
        after)
    (hTargets :
      ∀ pendingMessage,
        pendingMessage ∈
          before.pendingMessages →
        pendingMessage.name =
          messageServer) :
    ∀ pendingMessage,
      pendingMessage ∈
        after.pendingMessages →
      pendingMessage.name =
        messageServer := by

  cases hStep with

  | assign
      currentTime
      stateStore
      pendingMessages
      target
      expression
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      simpa using hTargets

  | selfSend
      currentTime
      stateStore
      pendingMessages
      targetMessage
      delay
      remaining
      hTarget =>

      intro pendingMessage hMember

      simp only [
        List.mem_append,
        List.mem_singleton
      ] at hMember

      rcases hMember with
        hExisting | hAdded

      · exact
          hTargets
            pendingMessage
            hExisting

      · subst pendingMessage

        exact hTarget

end StoreStep

namespace StoreDispatchStep

/--
Dispatch preserves the pending-message target invariant because the
remaining queue is obtained only by removing one occurrence.
-/
theorem preserves_pendingTargets
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {before after : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    (hDispatch :
      DTR.StoreDispatchStep
        messageServer
        messageBody
        before
        selectedMessage
        after)
    (hTargets :
      ∀ pendingMessage,
        pendingMessage ∈
          before.pendingMessages →
        pendingMessage.name =
          messageServer) :
    ∀ pendingMessage,
      pendingMessage ∈
        after.pendingMessages →
      pendingMessage.name =
        messageServer := by

  cases hDispatch with

  | fire
      currentTime
      stateStore
      pendingMessages
      remainingMessages
      selectedMessage
      hRemoved
      hEarliest
      hNotPast
      hTarget =>

      intro pendingMessage hMember

      apply
        hTargets
          pendingMessage

      exact
        Occurrence.RemovesOne.remaining_mem_of_removesOne
          hRemoved
          hMember

end StoreDispatchStep

namespace StoreMachineStep

/--
Every combined DTR store-machine step preserves runtime
well-formedness, provided that the body loaded by dispatch is itself
well formed.
-/
theorem preserves_runtimeWellFormed
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {before after : DTR.StoreState}
    {label : DTR.StoreMachineLabel}
    (hStep :
      DTR.StoreMachineStep
        declaredVariables
        messageServer
        messageBody
        before
        label
        after)
    (hMessageBody :
      DTR.Body.StoreWellFormed
        declaredVariables
        messageServer
        messageBody)
    (hBefore :
      DTR.StoreState.RuntimeWellFormed
        declaredVariables
        messageServer
        before) :
    DTR.StoreState.RuntimeWellFormed
      declaredVariables
      messageServer
      after := by

  cases hStep with

  | statement hStatement =>
      exact {
        coverage :=
          DTR.StoreStep.preserves_coverage
            hStatement
            hBefore.coverage

        activeBody :=
          DTR.StoreStep.preserves_body_storeWellFormed
            hStatement
            hBefore.activeBody

        pendingTargets :=
          DTR.StoreStep.preserves_pendingTargets
            hStatement
            hBefore.pendingTargets
      }

  | dispatch hDispatch =>
      cases hDispatch with

      | fire
          currentTime
          stateStore
          pendingMessages
          remainingMessages
          selectedMessage
          hRemoved
          hEarliest
          hNotPast
          hTarget =>

          exact {
            coverage :=
              hBefore.coverage

            activeBody :=
              hMessageBody

            pendingTargets := by
              intro pendingMessage hMember

              apply
                hBefore.pendingTargets
                  pendingMessage

              exact
                Occurrence.RemovesOne.remaining_mem_of_removesOne
                  hRemoved
                  hMember
          }

end StoreMachineStep
end DTR
end Relico
