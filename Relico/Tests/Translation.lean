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

#eval Translation.translate validModel

end Tests
end Relico
