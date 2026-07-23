import Relico.Correctness.Inversion
import Relico.Tests.DTRWellFormed

set_option autoImplicit false

namespace Relico
namespace Tests

def inversionAssignmentBody : DTR.Body := [
  .assign
    stateVariableName
    (.intLiteral 7),
  .selfSend
    tickMessageName
    ⟨2⟩
]

theorem compiledAssignmentBody_can_be_inverted :
    ∃ sourceVar sourceExpression sourceRemaining,
      inversionAssignmentBody =
        DTR.Stmt.assign
            sourceVar
            sourceExpression ::
          sourceRemaining ∧
      stateVariableName = sourceVar ∧
      LF.Expr.intLiteral 7 =
        Translation.compileExpr sourceExpression ∧
      [LF.Stmt.schedule
          (Translation.actionNameFor tickMessageName)
          ⟨2⟩] =
        Translation.compileBody sourceRemaining := by

  apply Correctness.compileBody_assign_head

  rfl

def inversionSendBody : DTR.Body := [
  .selfSend
    tickMessageName
    ⟨3⟩,
  .assign
    stateVariableName
    (.intLiteral 9)
]

theorem compiledScheduleBody_can_be_inverted :
    ∃ sourceMessage sourceDelay sourceRemaining,
      inversionSendBody =
        DTR.Stmt.selfSend
            sourceMessage
            sourceDelay ::
          sourceRemaining ∧
      Translation.actionNameFor tickMessageName =
        Translation.actionNameFor sourceMessage ∧
      (⟨3⟩ : Delay) = sourceDelay ∧
      [LF.Stmt.assign
          stateVariableName
          (.intLiteral 9)] =
        Translation.compileBody sourceRemaining := by

  apply Correctness.compileBody_schedule_head

  rfl

end Tests
end Relico
