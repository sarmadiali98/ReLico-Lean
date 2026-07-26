import Relico.Correctness.PayloadCorrespondence
import Relico.Common.Occurrence

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Payload-aware pending correspondence contains the established
name-and-time correspondence.
-/
theorem PendingPayloadCorresponds.toPendingCorresponds
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hCorresponds :
      PendingPayloadCorresponds
        sourceMessage
        targetAction) :
    PendingCorresponds
      sourceMessage
      targetAction :=

  hCorresponds.occurrence

/--
Forgetting payload equality from every queue element yields the
established occurrence correspondence relation.
-/
theorem PayloadQueueCorresponds.toQueueCorresponds
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      PayloadQueueCorresponds
        sourceQueue
        targetQueue) :
    QueueCorresponds
      sourceQueue
      targetQueue := by

  induction hQueues with

  | nil =>
      exact
        QueueCorresponds.nil

  | cons head tail inductionHypothesis =>
      exact
        QueueCorresponds.cons
          head.occurrence
          inductionHypothesis

/--
Removing one source payload-bearing occurrence identifies the target
occurrence at the same list position.

The selected payloads correspond exactly, and the residual queues retain
payload-aware correspondence.
-/
theorem PayloadQueueCorresponds.remove_source
    {sourceQueue sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hQueues :
      PayloadQueueCorresponds
        sourceQueue
        targetQueue)
    (hRemove :
      Occurrence.RemovesOne
        selectedMessage
        sourceQueue
        sourceRemaining) :
    ∃ selectedAction targetRemaining,
      Occurrence.RemovesOne
          selectedAction
          targetQueue
          targetRemaining ∧
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        PayloadQueueCorresponds
          sourceRemaining
          targetRemaining := by

  induction hRemove generalizing targetQueue with

  | head sourceRemaining =>

      cases hQueues with

      | cons headCorresponds tailCorresponds =>

          exact
            ⟨_,
             _,
             Occurrence.RemovesOne.head _,
             headCorresponds,
             tailCorresponds⟩

  | tail sourceHead hTail inductionHypothesis =>

      cases hQueues with

      | cons headCorresponds tailCorresponds =>

          rcases
              inductionHypothesis
                tailCorresponds
            with
              ⟨selectedAction,
               targetRemaining,
               hTargetRemove,
               hSelectedCorresponds,
               hRemainingCorresponds⟩

          exact
            ⟨selectedAction,
             _,
             Occurrence.RemovesOne.tail
               _
               hTargetRemove,
             hSelectedCorresponds,
             PayloadQueueCorresponds.cons
               headCorresponds
               hRemainingCorresponds⟩

/--
Removing one target payload-bearing occurrence identifies the source
occurrence at the same list position.

The selected payloads correspond exactly, and the residual queues retain
payload-aware correspondence.
-/
theorem PayloadQueueCorresponds.remove_target
    {sourceQueue : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hQueues :
      PayloadQueueCorresponds
        sourceQueue
        targetQueue)
    (hRemove :
      Occurrence.RemovesOne
        selectedAction
        targetQueue
        targetRemaining) :
    ∃ selectedMessage sourceRemaining,
      Occurrence.RemovesOne
          selectedMessage
          sourceQueue
          sourceRemaining ∧
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        PayloadQueueCorresponds
          sourceRemaining
          targetRemaining := by

  induction hRemove generalizing sourceQueue with

  | head targetRemaining =>

      cases hQueues with

      | cons headCorresponds tailCorresponds =>

          exact
            ⟨_,
             _,
             Occurrence.RemovesOne.head _,
             headCorresponds,
             tailCorresponds⟩

  | tail targetHead hTail inductionHypothesis =>

      cases hQueues with

      | cons headCorresponds tailCorresponds =>

          rcases
              inductionHypothesis
                tailCorresponds
            with
              ⟨selectedMessage,
               sourceRemaining,
               hSourceRemove,
               hSelectedCorresponds,
               hRemainingCorresponds⟩

          exact
            ⟨selectedMessage,
             _,
             Occurrence.RemovesOne.tail
               _
               hSourceRemove,
             hSelectedCorresponds,
             PayloadQueueCorresponds.cons
               headCorresponds
               hRemainingCorresponds⟩

/--
Every source occurrence in payload-corresponding queues has a target
occurrence at the same list position.
-/
theorem PayloadQueueCorresponds.source_mem
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      PayloadQueueCorresponds
        sourceQueue
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    (hMembership :
      sourceMessage ∈
        sourceQueue) :
    ∃ targetAction,
      targetAction ∈
          targetQueue ∧
        PendingPayloadCorresponds
          sourceMessage
          targetAction := by

  induction hQueues with

  | nil =>
      simp at hMembership

  | cons headCorresponds tailCorresponds inductionHypothesis =>

      simp only [
        List.mem_cons
      ] at hMembership

      rcases hMembership with
        hHead | hTail

      · subst sourceMessage

        exact
          ⟨_,
           by simp,
           headCorresponds⟩

      · rcases
            inductionHypothesis
              hTail
          with
            ⟨targetAction,
             hTargetMembership,
             hSelectedCorresponds⟩

        exact
          ⟨targetAction,
           by
             simp only [
               List.mem_cons
             ]

             exact
               Or.inr
                 hTargetMembership,
           hSelectedCorresponds⟩

/--
Every target occurrence in payload-corresponding queues has a source
occurrence at the same list position.
-/
theorem PayloadQueueCorresponds.target_mem
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      PayloadQueueCorresponds
        sourceQueue
        targetQueue)
    {targetAction : LF.PendingAction}
    (hMembership :
      targetAction ∈
        targetQueue) :
    ∃ sourceMessage,
      sourceMessage ∈
          sourceQueue ∧
        PendingPayloadCorresponds
          sourceMessage
          targetAction := by

  induction hQueues with

  | nil =>
      simp at hMembership

  | cons headCorresponds tailCorresponds inductionHypothesis =>

      simp only [
        List.mem_cons
      ] at hMembership

      rcases hMembership with
        hHead | hTail

      · subst targetAction

        exact
          ⟨_,
           by simp,
           headCorresponds⟩

      · rcases
            inductionHypothesis
              hTail
          with
            ⟨sourceMessage,
             hSourceMembership,
             hSelectedCorresponds⟩

        exact
          ⟨sourceMessage,
           by
             simp only [
               List.mem_cons
             ]

             exact
               Or.inr
                 hSourceMembership,
           hSelectedCorresponds⟩

end Correctness
end Relico
