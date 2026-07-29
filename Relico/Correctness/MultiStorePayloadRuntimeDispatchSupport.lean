import Relico.Correctness.MultiStorePayloadRuntimeStateCorrespondence
import Relico.Correctness.MultiStorePayloadSelectionRemoval
import Relico.Correctness.MultiStorePayloadDispatchSelection

set_option autoImplicit false

namespace Relico
namespace Correctness

universe u

/--
Removing one occurrence leaves the original list permutation-equivalent to
placing the selected value in front of the residual list.
-/
theorem removesOne_before_perm_selected_cons_after
    {α : Type u}
    {selected : α}
    {before after : List α}
    (hRemove :
      Occurrence.RemovesOne
        selected
        before
        after) :
    before.Perm
      (selected :: after) := by

  induction hRemove with

  | head remaining =>
      exact
        List.Perm.refl _

  | tail headValue _hTailRemove inductionHypothesis =>
      exact
        (List.Perm.cons
          headValue
          inductionHypothesis).trans
            (List.Perm.swap
              selected
              headValue
              _)

/--
Two removals of the same value from the same list produce
permutation-equivalent residual lists.

This is deliberately weaker than residual equality because duplicate equal
values may be removed at different list positions.
-/
theorem removesOne_same_selected_remaining_perm
    {α : Type u}
    {selected : α}
    {before afterLeft afterRight : List α}
    (hLeft :
      Occurrence.RemovesOne
        selected
        before
        afterLeft)
    (hRight :
      Occurrence.RemovesOne
        selected
        before
        afterRight) :
    afterLeft.Perm
      afterRight := by

  induction hLeft generalizing afterRight with

  | head remaining =>
      cases hRight with

      | head _ =>
          exact
            List.Perm.refl _

      | tail _ hRightTail =>
          exact
            removesOne_before_perm_selected_cons_after
              hRightTail

  | tail headValue hLeftTail inductionHypothesis =>
      cases hRight with

      | head _ =>
          exact
            (removesOne_before_perm_selected_cons_after
              hLeftTail).symm

      | tail _ hRightTail =>
          exact
            List.Perm.cons
              headValue
              (inductionHypothesis
                hRightTail)

/--
Exact payload occurrence correspondence to the same target action determines
the source pending-message value uniquely.
-/
theorem pendingPayloadCorresponds_source_eq_of_sameTarget
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hLeft :
      PendingPayloadCorresponds
        sourceLeft
        targetAction)
    (hRight :
      PendingPayloadCorresponds
        sourceRight
        targetAction) :
    sourceLeft =
      sourceRight := by

  have hName :
      sourceLeft.name =
        sourceRight.name := by

    apply
      Translation.actionNameFor_injective

    calc
      Translation.actionNameFor
            sourceLeft.name =
          targetAction.name :=
        hLeft.occurrence.actionName.symm

      _ =
          Translation.actionNameFor
            sourceRight.name :=
        hRight.occurrence.actionName

  have hTime :
      sourceLeft.arrivalTime =
        sourceRight.arrivalTime := by

    calc
      sourceLeft.arrivalTime =
          targetAction.tag.time :=
        hLeft.occurrence.logicalTime.symm

      _ =
          sourceRight.arrivalTime :=
        hRight.occurrence.logicalTime

  have hPayload :
      sourceLeft.payload =
        sourceRight.payload := by

    calc
      sourceLeft.payload =
          targetAction.payload :=
        hLeft.payload.symm

      _ =
          sourceRight.payload :=
        hRight.payload

  cases sourceLeft
  cases sourceRight
  simp_all

/--
Two target actions corresponding to the same source pending-message value are
equal when their complete LF tags are equal.
-/
theorem pendingPayloadCorresponds_target_eq_of_sameSource_and_tag
    {sourceMessage :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hLeft :
      PendingPayloadCorresponds
        sourceMessage
        targetLeft)
    (hRight :
      PendingPayloadCorresponds
        sourceMessage
        targetRight)
    (hTag :
      targetLeft.tag =
        targetRight.tag) :
    targetLeft =
      targetRight := by

  have hName :
      targetLeft.name =
        targetRight.name := by

    calc
      targetLeft.name =
          Translation.actionNameFor
            sourceMessage.name :=
        hLeft.occurrence.actionName

      _ =
          targetRight.name :=
        hRight.occurrence.actionName.symm

  have hPayload :
      targetLeft.payload =
        targetRight.payload := by

    calc
      targetLeft.payload =
          sourceMessage.payload :=
        hLeft.payload

      _ =
          targetRight.payload :=
        hRight.payload.symm

  cases targetLeft
  cases targetRight
  simp_all

/--
Forward residual selection compatibility transports from one removal of a
selected target-action value to another removal of that same value.
-/
theorem multiStorePayload_forwardResidualSelectionMerge
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceRemaining :
      DTR.MessageBag}
    {targetQueue selectionRemaining positionalRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hSelectionRemoved :
      Occurrence.RemovesOne
        selectedAction
        targetQueue
        selectionRemaining)
    (hPositionalRemoved :
      Occurrence.RemovesOne
        selectedAction
        targetQueue
        positionalRemaining)
    (hSelectionRemaining :
      MultiStorePayloadSelectionCompatible
        messageServers
        sourceRemaining
        selectionRemaining) :
    MultiStorePayloadSelectionCompatible
      messageServers
      sourceRemaining
      positionalRemaining := by

  have hResidualPermutation :
      selectionRemaining.Perm
        positionalRemaining :=
    removesOne_same_selected_remaining_perm
      hSelectionRemoved
      hPositionalRemoved

  exact
    MultiStorePayloadSelectionCompatible.perm_target
      hResidualPermutation.symm
      hSelectionRemaining

/--
Backward residual selection compatibility transports from one removal of a
selected source-message value to another removal of that same value.
-/
theorem multiStorePayload_backwardResidualSelectionMerge
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue selectionRemaining positionalRemaining :
      DTR.MessageBag}
    {targetRemaining :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hSelectionRemoved :
      Occurrence.RemovesOne
        selectedMessage
        sourceQueue
        selectionRemaining)
    (hPositionalRemoved :
      Occurrence.RemovesOne
        selectedMessage
        sourceQueue
        positionalRemaining)
    (hSelectionRemaining :
      MultiStorePayloadSelectionCompatible
        messageServers
        selectionRemaining
        targetRemaining) :
    MultiStorePayloadSelectionCompatible
      messageServers
      positionalRemaining
      targetRemaining := by

  have hResidualPermutation :
      selectionRemaining.Perm
        positionalRemaining :=
    removesOne_same_selected_remaining_perm
      hSelectionRemoved
      hPositionalRemoved

  exact
    MultiStorePayloadSelectionCompatible.perm_source
      hResidualPermutation.symm
      hSelectionRemaining

end Correctness
end Relico
