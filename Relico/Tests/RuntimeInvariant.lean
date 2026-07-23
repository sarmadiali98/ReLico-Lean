import Relico.Correctness.RuntimeInvariant
import Relico.Tests.SmallStep

set_option autoImplicit false

namespace Relico
namespace Tests

theorem dtrAssignmentSource_runtimeWellFormed :
    DTR.State.WellFormed
      validModel
      dtrAssignmentSource := by
  refine {
    activeBodyWellFormed := ?_
    pendingMessagesWellFormed := ?_
  }

  · simp [
      dtrAssignmentSource,
      validModel,
      validReactiveClass,
      validMessageServer,
      stateVariableName,
      DTR.Body.WellFormed,
      DTR.Stmt.WellFormed,
      DTR.Expr.WellFormed
    ]

  · intro pendingMessage hMembership
    simp [dtrAssignmentSource] at hMembership

theorem dtrAssignmentTarget_runtimeWellFormed :
    DTR.State.WellFormed
      validModel
      dtrAssignmentTarget := by
  apply Correctness.dtrStep_preserves_runtimeWellFormed
    (stateBefore := dtrAssignmentSource)
    (label := DTR.Label.internal)

  · simpa [
      dtrAssignmentSource,
      dtrAssignmentTarget
    ] using
      (DTR.Step.assign
        (model := validModel)
        (currentTime := 2)
        (stateValue := 5)
        (pendingMessages := [])
        (target := stateVariableName)
        (expression := .intLiteral 7)
        (remaining := [])
        (hTarget := rfl))

  · exact dtrAssignmentSource_runtimeWellFormed

theorem dtrSendSource_runtimeWellFormed :
    DTR.State.WellFormed
      validModel
      dtrSendSource := by
  refine {
    activeBodyWellFormed := ?_
    pendingMessagesWellFormed := ?_
  }

  · simp [
      dtrSendSource,
      validModel,
      validReactiveClass,
      validMessageServer,
      tickMessageName,
      DTR.Body.WellFormed,
      DTR.Stmt.WellFormed
    ]

  · intro pendingMessage hMembership
    simp [dtrSendSource] at hMembership

theorem dtrSendTarget_runtimeWellFormed :
    DTR.State.WellFormed
      validModel
      dtrSendTarget := by
  apply Correctness.dtrStep_preserves_runtimeWellFormed
    (stateBefore := dtrSendSource)
    (label :=
      DTR.Label.send
        tickMessageName
        (LogicalTime.after 2 ⟨3⟩))

  · simpa [
      dtrSendSource,
      dtrSendTarget
    ] using
      (DTR.Step.selfSend
        (model := validModel)
        (currentTime := 2)
        (stateValue := 5)
        (pendingMessages := [])
        (targetMessage := tickMessageName)
        (delay := ⟨3⟩)
        (remaining := [])
        (hTarget := rfl))

  · exact dtrSendSource_runtimeWellFormed

end Tests
end Relico
