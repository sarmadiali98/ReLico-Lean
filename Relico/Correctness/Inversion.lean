import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
If a compiled body starts with an LF assignment, then the source body
starts with a DTR assignment that compiled to it.
-/
theorem compileBody_assign_head
    {sourceBody : DTR.Body}
    {targetVar : VarName}
    {targetExpression : LF.Expr}
    {targetRemaining : LF.Body}
    (hCompiled :
      Translation.compileBody sourceBody =
        LF.Stmt.assign
            targetVar
            targetExpression ::
          targetRemaining) :
    ∃ sourceVar sourceExpression sourceRemaining,
      sourceBody =
        DTR.Stmt.assign
            sourceVar
            sourceExpression ::
          sourceRemaining ∧
      targetVar = sourceVar ∧
      targetExpression =
        Translation.compileExpr sourceExpression ∧
      targetRemaining =
        Translation.compileBody sourceRemaining := by

  cases sourceBody with
  | nil =>
      simp [Translation.compileBody] at hCompiled

  | cons sourceStatement sourceRemaining =>
      cases sourceStatement with

      | assign sourceVar sourceExpression =>
          have hCons :
              LF.Stmt.assign
                    sourceVar
                    (Translation.compileExpr
                      sourceExpression) ::
                  Translation.compileBody
                    sourceRemaining
                =
              LF.Stmt.assign
                    targetVar
                    targetExpression ::
                  targetRemaining := by
            simpa [
              Translation.compileBody,
              Translation.compileStmt
            ] using hCompiled

          injection hCons with hHead hTail
          injection hHead with hVar hExpression

          exact
            ⟨sourceVar,
             sourceExpression,
             sourceRemaining,
             rfl,
             hVar.symm,
             hExpression.symm,
             hTail.symm⟩

      | selfSend sourceMessage sourceDelay =>
          simp [
            Translation.compileBody,
            Translation.compileStmt
          ] at hCompiled

/--
If a compiled body starts with an LF schedule statement, then the source
body starts with the DTR self-send that produced it.
-/
theorem compileBody_schedule_head
    {sourceBody : DTR.Body}
    {targetAction : ActionName}
    {targetDelay : Delay}
    {targetRemaining : LF.Body}
    (hCompiled :
      Translation.compileBody sourceBody =
        LF.Stmt.schedule
            targetAction
            targetDelay ::
          targetRemaining) :
    ∃ sourceMessage sourceDelay sourceRemaining,
      sourceBody =
        DTR.Stmt.selfSend
            sourceMessage
            sourceDelay ::
          sourceRemaining ∧
      targetAction =
        Translation.actionNameFor sourceMessage ∧
      targetDelay = sourceDelay ∧
      targetRemaining =
        Translation.compileBody sourceRemaining := by

  cases sourceBody with
  | nil =>
      simp [Translation.compileBody] at hCompiled

  | cons sourceStatement sourceRemaining =>
      cases sourceStatement with

      | assign sourceVar sourceExpression =>
          simp [
            Translation.compileBody,
            Translation.compileStmt
          ] at hCompiled

      | selfSend sourceMessage sourceDelay =>
          have hCons :
              LF.Stmt.schedule
                    (Translation.actionNameFor
                      sourceMessage)
                    sourceDelay ::
                  Translation.compileBody
                    sourceRemaining
                =
              LF.Stmt.schedule
                    targetAction
                    targetDelay ::
                  targetRemaining := by
            simpa [
              Translation.compileBody,
              Translation.compileStmt
            ] using hCompiled

          injection hCons with hHead hTail
          injection hHead with hAction hDelay

          exact
            ⟨sourceMessage,
             sourceDelay,
             sourceRemaining,
             rfl,
             hAction.symm,
             hDelay.symm,
             hTail.symm⟩

end Correctness
end Relico
