import Relico.DTR.Syntax
import Relico.LF.Syntax
import Relico.Translation.NameGeneration

set_option autoImplicit false

namespace Relico
namespace Translation

inductive TranslationError where
  | unsupported : String → TranslationError
deriving Repr, DecidableEq, BEq, Inhabited

def compileExpr :
    DTR.Expr → LF.Expr
  | .intLiteral value =>
      .intLiteral value
  | .stateVar varName =>
      .stateVar varName

def compileStmt :
    DTR.Stmt → LF.Stmt
  | .assign target expression =>
      .assign target (compileExpr expression)
  | .selfSend messageName delay =>
      .schedule (actionNameFor messageName) delay

def compileBody
    (body : DTR.Body) :
    LF.Body :=
  body.map compileStmt

def compileStartupReaction
    (reactiveClass : DTR.ReactiveClass) :
    LF.Reaction where
  name := startupReactionName
  trigger := .startup
  body := compileBody reactiveClass.constructor.body

def compileMessageReaction
    (messageServer : DTR.MessageServer) :
    LF.Reaction where
  name := messageReactionNameFor messageServer.name
  trigger := .logicalAction (actionNameFor messageServer.name)
  body := compileBody messageServer.body

def compileReactor
    (reactiveClass : DTR.ReactiveClass) :
    LF.Reactor where
  name := reactorNameFor reactiveClass.name
  stateVar := reactiveClass.stateVar
  logicalAction := actionNameFor reactiveClass.messageServer.name
  startupReaction := compileStartupReaction reactiveClass
  messageReaction :=
    compileMessageReaction reactiveClass.messageServer

def compileReactorInstance
    (actor : DTR.ActorInstance) :
    LF.ReactorInstance where
  name := actor.name
  reactorName := reactorNameFor actor.className

def translateCore
    (model : DTR.Model) :
    LF.Program where
  reactor := compileReactor model.reactiveClass
  reactorInstance := compileReactorInstance model.actor

def translate
    (model : DTR.Model) :
    Except TranslationError LF.Program :=
  .ok (translateCore model)

@[simp]
theorem translate_eq_ok
    (model : DTR.Model) :
    translate model = .ok (translateCore model) := by
  rfl

theorem translate_succeeds
    (model : DTR.Model) :
    ∃ program,
      translate model = .ok program := by
  exact ⟨translateCore model, rfl⟩

end Translation
end Relico
