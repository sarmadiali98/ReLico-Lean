import Relico.Correctness.PayloadCorrespondence
import Relico.DTR.BoundPayloadDispatch
import Relico.LF.BoundPayloadDispatch
import Relico.Tests.BoundPayloadFoundation

set_option autoImplicit false

namespace Relico
namespace Tests

def boundPayloadDispatchSourceSelected :
    DTR.PendingMessage :=
  DTR.PendingMessage.scheduleWithPayload
    3
    boundPayloadMessage
    [
      42
    ]
    boundPayloadDelay

def boundPayloadDispatchTargetSelected :
    LF.PendingAction :=
  LF.PendingAction.scheduleWithPayload
    boundPayloadTargetTag
    boundPayloadTargetReaction.logicalAction
    [
      42
    ]
    boundPayloadDelay

def boundPayloadDispatchSourceBefore :
    DTR.BoundPayloadState := {

  currentTime :=
    boundPayloadDispatchSourceSelected.arrivalTime

  stateValue :=
    9

  parameters :=
    ParameterStore.empty

  pendingMessages :=
    [
      boundPayloadDispatchSourceSelected
    ]

  activeBody :=
    []
}

def boundPayloadDispatchSourceAfter :
    DTR.BoundPayloadState := {

  currentTime :=
    boundPayloadDispatchSourceSelected.arrivalTime

  stateValue :=
    9

  parameters :=
    boundPayloadParameters

  pendingMessages :=
    []

  activeBody :=
    boundPayloadSourceServer.body
}

def boundPayloadDispatchTargetBefore :
    LF.BoundPayloadState := {

  currentTag :=
    boundPayloadDispatchTargetSelected.tag

  stateValue :=
    9

  parameters :=
    ParameterStore.empty

  pendingActions :=
    [
      boundPayloadDispatchTargetSelected
    ]

  activeBody :=
    []
}

def boundPayloadDispatchTargetAfter :
    LF.BoundPayloadState := {

  currentTag :=
    boundPayloadDispatchTargetSelected.tag

  stateValue :=
    9

  parameters :=
    boundPayloadParameters

  pendingActions :=
    []

  activeBody :=
    boundPayloadTargetReaction.body
}

theorem bound_payload_dispatch_selected_corresponds :
    Correctness.PendingPayloadCorresponds
      boundPayloadDispatchSourceSelected
      boundPayloadDispatchTargetSelected := by

  simpa [
    boundPayloadDispatchSourceSelected,
    boundPayloadDispatchTargetSelected,
    boundPayloadTargetReaction,
    boundPayloadSourceServer
  ] using
    Correctness.pendingPayloadCorresponds_scheduleWithPayload
      3
      boundPayloadTargetTag
      boundPayloadMessage
      [
        42
      ]
      boundPayloadDelay
      rfl

theorem bound_payload_source_dispatch_step :
    DTR.BoundPayloadDispatchStep
      boundPayloadSourceServer
      boundPayloadDispatchSourceBefore
      boundPayloadDispatchSourceSelected
      boundPayloadDispatchSourceAfter := by

  have hRemoved :
      Occurrence.RemovesOne
        boundPayloadDispatchSourceSelected
        [
          boundPayloadDispatchSourceSelected
        ]
        [] :=

    Occurrence.RemovesOne.head
      ([] : DTR.MessageBag)

  have hEarliest :
      DTR.IsEarliest
        boundPayloadDispatchSourceSelected
        [
          boundPayloadDispatchSourceSelected
        ] := by

    intro candidate hCandidate

    simp only [
      List.mem_singleton
    ] at hCandidate

    subst candidate

    exact
      Nat.le_refl _

  have hBind :
      ParameterStore.bindPayload
          boundPayloadSourceServer.parameters
          boundPayloadDispatchSourceSelected.payload =
        some boundPayloadParameters := by

    simpa [
      boundPayloadDispatchSourceSelected
    ] using
      bound_payload_formals_bind_exactly

  simpa [
    boundPayloadDispatchSourceBefore,
    boundPayloadDispatchSourceAfter
  ] using
    DTR.BoundPayloadDispatchStep.fire
      (server :=
        boundPayloadSourceServer)
      (currentTime :=
        boundPayloadDispatchSourceSelected.arrivalTime)
      (stateValue :=
        9)
      (parameters :=
        ParameterStore.empty)
      (pendingMessages :=
        [
          boundPayloadDispatchSourceSelected
        ])
      (remainingMessages :=
        [])
      (selectedMessage :=
        boundPayloadDispatchSourceSelected)
      (boundParameters :=
        boundPayloadParameters)
      hRemoved
      hEarliest
      (Nat.le_refl _)
      rfl
      hBind

theorem bound_payload_target_dispatch_step :
    LF.BoundPayloadDispatchStep
      boundPayloadTargetReaction
      boundPayloadDispatchTargetBefore
      boundPayloadDispatchTargetSelected
      boundPayloadDispatchTargetAfter := by

  have hRemoved :
      Occurrence.RemovesOne
        boundPayloadDispatchTargetSelected
        [
          boundPayloadDispatchTargetSelected
        ]
        [] :=

    Occurrence.RemovesOne.head
      ([] : LF.ActionQueue)

  have hEarliest :
      LF.IsEarliest
        boundPayloadDispatchTargetSelected
        [
          boundPayloadDispatchTargetSelected
        ] := by

    intro candidate hCandidate

    simp only [
      List.mem_singleton
    ] at hCandidate

    subst candidate

    exact
      LF.Tag.precedesOrEqual_refl _

  have hBind :
      ParameterStore.bindPayload
          boundPayloadTargetReaction.parameters
          boundPayloadDispatchTargetSelected.payload =
        some boundPayloadParameters := by

    simpa [
      boundPayloadDispatchTargetSelected,
      boundPayloadTargetReaction
    ] using
      bound_payload_formals_bind_exactly

  simpa [
    boundPayloadDispatchTargetBefore,
    boundPayloadDispatchTargetAfter
  ] using
    LF.BoundPayloadDispatchStep.fire
      (reaction :=
        boundPayloadTargetReaction)
      (currentTag :=
        boundPayloadDispatchTargetSelected.tag)
      (stateValue :=
        9)
      (parameters :=
        ParameterStore.empty)
      (pendingActions :=
        [
          boundPayloadDispatchTargetSelected
        ])
      (remainingActions :=
        [])
      (selectedAction :=
        boundPayloadDispatchTargetSelected)
      (boundParameters :=
        boundPayloadParameters)
      hRemoved
      hEarliest
      (LF.Tag.precedesOrEqual_refl _)
      rfl
      hBind

theorem bound_payload_source_dispatch_binds_parameter :
    boundPayloadDispatchSourceAfter.parameters =
      boundPayloadParameters := by
  rfl

theorem bound_payload_target_dispatch_binds_parameter :
    boundPayloadDispatchTargetAfter.parameters =
      boundPayloadParameters := by
  rfl

theorem bound_payload_source_dispatch_loads_body :
    boundPayloadDispatchSourceAfter.activeBody =
      boundPayloadSourceServer.body := by

  exact
    DTR.BoundPayloadDispatchStep.activates_server_body
      bound_payload_source_dispatch_step

theorem bound_payload_target_dispatch_loads_body :
    boundPayloadDispatchTargetAfter.activeBody =
      boundPayloadTargetReaction.body := by

  exact
    LF.BoundPayloadDispatchStep.activates_reaction_body
      bound_payload_target_dispatch_step

theorem bound_payload_source_parameter_available_after_dispatch :
    DTR.PayloadExpr.evaluate
        boundPayloadDispatchSourceAfter.stateValue
        boundPayloadDispatchSourceAfter.parameters
        boundPayloadSourceExpression =
      some 42 := by

  simp [
    boundPayloadDispatchSourceAfter,
    boundPayloadSourceExpression,
    boundPayloadParameters
  ]

theorem bound_payload_target_parameter_available_after_dispatch :
    LF.PayloadExpr.evaluate
        boundPayloadDispatchTargetAfter.stateValue
        boundPayloadDispatchTargetAfter.parameters
        (Translation.compilePayloadExpr
          boundPayloadSourceExpression) =
      some 42 := by

  simp [
    boundPayloadDispatchTargetAfter,
    boundPayloadSourceExpression,
    boundPayloadParameters
  ]

end Tests
end Relico
