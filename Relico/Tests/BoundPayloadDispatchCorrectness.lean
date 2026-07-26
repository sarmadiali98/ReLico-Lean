import Relico.Correctness.BoundPayloadDispatch
import Relico.Tests.BoundPayloadDispatch

set_option autoImplicit false

namespace Relico
namespace Tests

theorem bound_payload_dispatch_before_corresponds :
    Correctness.BoundPayloadStateCorresponds
      boundPayloadDispatchSourceBefore
      boundPayloadDispatchTargetBefore := by

  refine {
    currentTime :=
      ?_

    stateValue :=
      rfl

    parameters :=
      rfl

    pendingEvents :=
      Correctness.PayloadQueueCorresponds.cons
        bound_payload_dispatch_selected_corresponds
        Correctness.PayloadQueueCorresponds.nil

    activeBody :=
      rfl
  }

  simpa [
    boundPayloadDispatchSourceBefore,
    boundPayloadDispatchTargetBefore
  ] using
    bound_payload_dispatch_selected_corresponds.occurrence.logicalTime

theorem bound_payload_dispatch_after_corresponds :
    Correctness.BoundPayloadStateCorresponds
      boundPayloadDispatchSourceAfter
      boundPayloadDispatchTargetAfter := by

  refine {
    currentTime :=
      ?_

    stateValue :=
      rfl

    parameters :=
      rfl

    pendingEvents :=
      Correctness.PayloadQueueCorresponds.nil

    activeBody :=
      rfl
  }

  simpa [
    boundPayloadDispatchSourceAfter,
    boundPayloadDispatchTargetAfter
  ] using
    bound_payload_dispatch_selected_corresponds.occurrence.logicalTime

theorem bound_payload_dispatch_forward_compatible :
    Correctness.BoundPayloadForwardDispatchCompatible
      boundPayloadDispatchSourceSelected
      boundPayloadDispatchSourceAfter.pendingMessages
      boundPayloadDispatchTargetBefore := by

  refine
    ⟨boundPayloadDispatchTargetSelected,
     [],
     ?_,
     bound_payload_dispatch_selected_corresponds,
     Correctness.PayloadQueueCorresponds.nil,
     ?_,
     ?_⟩

  · simpa [
      boundPayloadDispatchTargetBefore
    ] using
      (Occurrence.RemovesOne.head
        (selected :=
          boundPayloadDispatchTargetSelected)
        ([] : LF.ActionQueue))

  · intro candidate hCandidate

    simp only [
      boundPayloadDispatchTargetBefore,
      List.mem_singleton
    ] at hCandidate

    subst candidate

    exact
      LF.Tag.precedesOrEqual_refl _

  · simpa [
      boundPayloadDispatchTargetBefore
    ] using
      LF.Tag.precedesOrEqual_refl
        boundPayloadDispatchTargetSelected.tag

theorem bound_payload_dispatch_forward_exists :
    ∃ selectedAction targetAfter,
      LF.BoundPayloadDispatchStep
          boundPayloadTargetReaction
          boundPayloadDispatchTargetBefore
          selectedAction
          targetAfter ∧
        Correctness.PendingPayloadCorresponds
          boundPayloadDispatchSourceSelected
          selectedAction ∧
        Correctness.BoundPayloadStateCorresponds
          boundPayloadDispatchSourceAfter
          targetAfter := by

  simpa [
    boundPayloadTargetReaction
  ] using
    Correctness.boundPayloadDispatch_forward_of_compatible
      bound_payload_source_dispatch_step
      bound_payload_dispatch_before_corresponds
      bound_payload_dispatch_forward_compatible

theorem bound_payload_dispatch_backward_exists :
    ∃ selectedMessage sourceAfter,
      DTR.BoundPayloadDispatchStep
          boundPayloadSourceServer
          boundPayloadDispatchSourceBefore
          selectedMessage
          sourceAfter ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          boundPayloadDispatchTargetSelected ∧
        Correctness.BoundPayloadStateCorresponds
          sourceAfter
          boundPayloadDispatchTargetAfter := by

  simpa [
    boundPayloadTargetReaction
  ] using
    Correctness.boundPayloadDispatch_backward
      bound_payload_target_dispatch_step
      bound_payload_dispatch_before_corresponds

theorem bound_payload_dispatch_forward_selects_expected_action :
    LF.BoundPayloadDispatchStep
      boundPayloadTargetReaction
      boundPayloadDispatchTargetBefore
      boundPayloadDispatchTargetSelected
      boundPayloadDispatchTargetAfter :=

  bound_payload_target_dispatch_step

theorem bound_payload_dispatch_backward_selects_expected_message :
    DTR.BoundPayloadDispatchStep
      boundPayloadSourceServer
      boundPayloadDispatchSourceBefore
      boundPayloadDispatchSourceSelected
      boundPayloadDispatchSourceAfter :=

  bound_payload_source_dispatch_step

theorem bound_payload_dispatch_result_parameter_correspondence :
    boundPayloadDispatchTargetAfter.parameters =
      boundPayloadDispatchSourceAfter.parameters := by
  rfl

theorem bound_payload_dispatch_result_body_correspondence :
    boundPayloadDispatchTargetAfter.activeBody =
      Translation.compileBoundPayloadBody
        boundPayloadDispatchSourceAfter.activeBody := by
  rfl

end Tests
end Relico
