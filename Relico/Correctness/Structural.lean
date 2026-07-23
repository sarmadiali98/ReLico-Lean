import Relico.DTR.WellFormed
import Relico.LF.WellFormed
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Correctness

theorem compileExpr_wellFormed
    {declaredStateVar : VarName}
    {expression : DTR.Expr}
    (hExpression :
      DTR.Expr.WellFormed
        declaredStateVar
        expression) :
    LF.Expr.WellFormed
      declaredStateVar
      (Translation.compileExpr expression) := by
  cases expression with
  | intLiteral value =>
      trivial
  | stateVar referencedStateVar =>
      exact hExpression

theorem compileStmt_wellFormed
    {declaredStateVar : VarName}
    {declaredMessageServer : MsgName}
    {statement : DTR.Stmt}
    (hStatement :
      DTR.Stmt.WellFormed
        declaredStateVar
        declaredMessageServer
        statement) :
    LF.Stmt.WellFormed
      declaredStateVar
      (Translation.actionNameFor declaredMessageServer)
      (Translation.compileStmt statement) := by
  cases statement with
  | assign target expression =>
      rcases hStatement with
        ⟨hTarget, hExpression⟩
      exact
        ⟨hTarget,
         compileExpr_wellFormed hExpression⟩

  | selfSend targetMessage delay =>
      exact
        congrArg
          Translation.actionNameFor
          hStatement

theorem compileBody_wellFormed
    {declaredStateVar : VarName}
    {declaredMessageServer : MsgName}
    {body : DTR.Body}
    (hBody :
      DTR.Body.WellFormed
        declaredStateVar
        declaredMessageServer
        body) :
    LF.Body.WellFormed
      declaredStateVar
      (Translation.actionNameFor declaredMessageServer)
      (Translation.compileBody body) := by
  intro compiledStatement hCompiledStatement

  simp only [
    Translation.compileBody,
    List.mem_map
  ] at hCompiledStatement

  rcases hCompiledStatement with
    ⟨sourceStatement,
     hSourceStatement,
     rfl⟩

  exact
    compileStmt_wellFormed
      (hBody sourceStatement hSourceStatement)

theorem compileReactor_wellFormed
    {reactiveClass : DTR.ReactiveClass}
    (hClassName :
      ClassName.isValid reactiveClass.name)
    (hStateVarName :
      VarName.isValid reactiveClass.stateVar)
    (hConstructorBody :
      DTR.Body.WellFormed
        reactiveClass.stateVar
        reactiveClass.messageServer.name
        reactiveClass.constructor.body)
    (hMessageBody :
      DTR.Body.WellFormed
        reactiveClass.stateVar
        reactiveClass.messageServer.name
        reactiveClass.messageServer.body) :
    LF.Reactor.WellFormed
      (Translation.compileReactor reactiveClass) := by
  refine {
    reactorNameValid := ?_
    stateVarNameValid := ?_
    actionNameValid := ?_
    startupReactionNameValid := ?_
    startupTriggerCorrect := ?_
    startupBodyWellFormed := ?_
    messageReactionNameValid := ?_
    messageTriggerCorrect := ?_
    messageBodyWellFormed := ?_
  }

  · simpa [
      Translation.compileReactor,
      Translation.reactorNameFor,
      ReactorName.isValid,
      ClassName.isValid
    ] using hClassName

  · simpa [
      Translation.compileReactor
    ] using hStateVarName

  · simp [
      Translation.compileReactor,
      Translation.actionNameFor,
      ActionName.isValid
    ]

  · simp [
      Translation.compileReactor,
      Translation.compileStartupReaction,
      Translation.startupReactionName,
      ReactionName.isValid
    ]

  · rfl

  · simpa [
      Translation.compileReactor,
      Translation.compileStartupReaction
    ] using
      compileBody_wellFormed hConstructorBody

  · simp [
      Translation.compileReactor,
      Translation.compileMessageReaction,
      Translation.messageReactionNameFor,
      ReactionName.isValid
    ]

  · rfl

  · simpa [
      Translation.compileReactor,
      Translation.compileMessageReaction
    ] using
      compileBody_wellFormed hMessageBody

theorem translateCore_wellFormed
    {model : DTR.Model}
    (hModel : DTR.Model.WellFormed model) :
    LF.Program.WellFormed
      (Translation.translateCore model) := by
  refine {
    reactorWellFormed := ?_
    instanceNameValid := ?_
    instanceReactorMatches := ?_
  }

  · exact
      compileReactor_wellFormed
        hModel.classNameValid
        hModel.stateVarNameValid
        hModel.constructorBodyWellFormed
        hModel.messageServerBodyWellFormed

  · simpa [
      Translation.translateCore,
      Translation.compileReactorInstance
    ] using hModel.actorNameValid

  · simpa [
      Translation.translateCore,
      Translation.compileReactor,
      Translation.compileReactorInstance
    ] using
      congrArg
        Translation.reactorNameFor
        hModel.actorClassMatches

/--
The first correctness theorem about the executable translator.

If the actual `Translation.translate` function returns a program for
a well-formed source model, that generated program is structurally
well formed.
-/
theorem translate_wellFormed
    {model : DTR.Model}
    {program : LF.Program}
    (hModel : DTR.Model.WellFormed model)
    (hTranslate :
      Translation.translate model =
        .ok program) :
    LF.Program.WellFormed program := by
  simp [Translation.translate] at hTranslate
  subst program
  exact translateCore_wellFormed hModel

end Correctness
end Relico
