import Relico.Tests.DTRWellFormed
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Tests

def expectedReactorName : ReactorName :=
  ⟨"Controller"⟩

def expectedActionName : ActionName :=
  ⟨"tick_action"⟩

def expectedStartupReaction : LF.Reaction where
  name := ⟨"startup"⟩
  trigger := .startup
  body := [
    .assign stateVariableName (.intLiteral 0),
    .schedule expectedActionName { value := 1 }
  ]

def expectedMessageReaction : LF.Reaction where
  name := ⟨"tick_reaction"⟩
  trigger := .logicalAction expectedActionName
  body := [
    .assign stateVariableName (.stateVar stateVariableName),
    .schedule expectedActionName { value := 1 }
  ]

def expectedReactor : LF.Reactor where
  name := expectedReactorName
  stateVar := stateVariableName
  logicalAction := expectedActionName
  startupReaction := expectedStartupReaction
  messageReaction := expectedMessageReaction

def expectedReactorInstance : LF.ReactorInstance where
  name := controllerActorName
  reactorName := expectedReactorName

def expectedProgram : LF.Program where
  reactor := expectedReactor
  reactorInstance := expectedReactorInstance

theorem validModel_translates_to_expectedProgram :
    Translation.translate validModel =
      .ok expectedProgram := by
  rfl

theorem validModel_translation_succeeds :
    ∃ program,
      Translation.translate validModel =
        .ok program := by
  exact Translation.translate_succeeds validModel

structure ExpressionTranslationCase where
  id : String
  source : DTR.Expr
  expected : LF.Expr

def expressionTranslationCases :
    List ExpressionTranslationCase := [
  {
    id := "core.translation.expression.int-literal"
    source := .intLiteral (-7)
    expected := .intLiteral (-7)
  },
  {
    id := "core.translation.expression.state-var"
    source := .stateVar ⟨"counter"⟩
    expected := .stateVar ⟨"counter"⟩
  }
]

def expressionTranslationCasePass
    (case : ExpressionTranslationCase) : Bool :=
    Translation.compileExpr case.source == case.expected

def expressionTranslationCasesPass : Bool :=
  expressionTranslationCases.all expressionTranslationCasePass

#guard expressionTranslationCasesPass

structure StatementTranslationCase where
  id : String
  source : DTR.Stmt
  expected : LF.Stmt

def statementTranslationCases :
    List StatementTranslationCase := [
  {
    id := "core.translation.statement.assign"
    source := .assign ⟨"x"⟩ (.stateVar ⟨"y"⟩)
    expected := .assign ⟨"x"⟩ (.stateVar ⟨"y"⟩)
  },
  {
    id := "core.translation.statement.self-send"
    source := .selfSend ⟨"tick"⟩ ⟨3⟩
    expected := .schedule ⟨"tick_action"⟩ ⟨3⟩
  },
  {
    id := "core.translation.statement.self-send.zero-delay"
    source := .selfSend ⟨"tick"⟩ ⟨0⟩
    expected := .schedule ⟨"tick_action"⟩ ⟨0⟩
  }
]

def statementTranslationCasePass
    (case : StatementTranslationCase) : Bool :=
    Translation.compileStmt case.source == case.expected

def statementTranslationCasesPass : Bool :=
  statementTranslationCases.all statementTranslationCasePass

#guard statementTranslationCasesPass

def startupReactionCaseId : String :=
  "core.translation.reaction.startup"

def startupReactionTranslationPass : Bool :=
  Translation.compileStartupReaction validModel.reactiveClass ==
    expectedStartupReaction

#guard startupReactionTranslationPass

def messageReactionCaseId : String :=
  "core.translation.reaction.message-server"

def messageReactionTranslationPass : Bool :=
  Translation.compileMessageReaction validModel.reactiveClass.messageServer ==
    expectedMessageReaction

#guard messageReactionTranslationPass

def reactorInstanceCaseId : String :=
  "core.translation.instance"

def reactorInstanceTranslationPass : Bool :=
  Translation.compileReactorInstance validModel.actor ==
    expectedReactorInstance

#guard reactorInstanceTranslationPass

def mixedSourceBody : DTR.Body := [
  .assign ⟨"x"⟩ (.intLiteral 4),
  .selfSend ⟨"tick"⟩ ⟨5⟩
]

def expectedMixedTargetBody : LF.Body := [
  .assign ⟨"x"⟩ (.intLiteral 4),
  .schedule ⟨"tick_action"⟩ ⟨5⟩
]

def mixedBodyOrderCaseId : String :=
  "core.translation.body.mixed-order"

#guard Translation.compileBody mixedSourceBody == expectedMixedTargetBody

#guard Translation.compileBody [] == []

def emptyBodyCaseId : String :=
  "core.translation.body.empty"

def exactProgramTranslationPass : Bool :=
  match Translation.translate validModel with
  | .ok program => program == expectedProgram
  | .error _ => false

def totalTranslationApiCaseId : String :=
  "core.translation.api.exact-program"

#guard exactProgramTranslationPass


end Tests
end Relico
