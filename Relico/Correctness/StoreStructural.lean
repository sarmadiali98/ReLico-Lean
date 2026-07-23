import Relico.DTR.StoreWellFormed
import Relico.LF.StoreWellFormed
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Expression compilation preserves well-formedness for an arbitrary
state-variable declaration list.
-/
theorem compileExpr_storeWellFormed
    {declaredVariables : List VarName}
    {expression : DTR.Expr}
    (hExpression :
      DTR.Expr.StoreWellFormed
        declaredVariables
        expression) :
    LF.Expr.StoreWellFormed
      declaredVariables
      (Translation.compileExpr
        expression) := by

  cases expression with

  | intLiteral value =>
      trivial

  | stateVar referencedVariable =>
      exact hExpression

/--
Statement compilation preserves declaration-list well-formedness.
-/
theorem compileStmt_storeWellFormed
    {declaredVariables : List VarName}
    {declaredMessageServer : MsgName}
    {statement : DTR.Stmt}
    (hStatement :
      DTR.Stmt.StoreWellFormed
        declaredVariables
        declaredMessageServer
        statement) :
    LF.Stmt.StoreWellFormed
      declaredVariables
      (Translation.actionNameFor
        declaredMessageServer)
      (Translation.compileStmt
        statement) := by

  cases statement with

  | assign target expression =>
      rcases hStatement with
        ⟨hTarget, hExpression⟩

      exact
        ⟨hTarget,
         compileExpr_storeWellFormed
           hExpression⟩

  | selfSend targetMessage delay =>
      exact
        congrArg
          Translation.actionNameFor
          hStatement

/--
Body compilation preserves declaration-list well-formedness.
-/
theorem compileBody_storeWellFormed
    {declaredVariables : List VarName}
    {declaredMessageServer : MsgName}
    {body : DTR.Body}
    (hBody :
      DTR.Body.StoreWellFormed
        declaredVariables
        declaredMessageServer
        body) :
    LF.Body.StoreWellFormed
      declaredVariables
      (Translation.actionNameFor
        declaredMessageServer)
      (Translation.compileBody
        body) := by

  intro compiledStatement hCompiledMember

  simp only [
    Translation.compileBody,
    List.mem_map
  ] at hCompiledMember

  rcases hCompiledMember with
    ⟨sourceStatement,
     hSourceMember,
     rfl⟩

  exact
    compileStmt_storeWellFormed
      (hBody
        sourceStatement
        hSourceMember)

end Correctness
end Relico
