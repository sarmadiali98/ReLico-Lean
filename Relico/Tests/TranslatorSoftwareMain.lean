import Relico.Tests.FrontendDecoder
import Relico.Tests.Translation

set_option autoImplicit false

namespace Relico
namespace Tests

def frontendSoftwareCases : List (String × Bool) :=
  (expressionDecoderCases.map fun case =>
    (case.id, expressionDecoderCasePass case)
  )
  ++ (statementDecoderCases.map fun case =>
    (case.id, statementDecoderCasePass case)
  )
  ++ (modelDecoderCases.map fun case =>
    (case.id, modelDecoderCasePass case)
  )
  ++ (jsonDecoderCases.map fun case =>
    (case.id, jsonDecoderCasePass case)
  )

def translationSoftwareCases : List (String × Bool) :=
  (expressionTranslationCases.map fun case =>
    (case.id, expressionTranslationCasePass case)
  )
  ++ (statementTranslationCases.map fun case =>
    (case.id, statementTranslationCasePass case)
  )
  ++ [
    (
      "core.translation.reaction.startup",
      startupReactionTranslationPass
    ),
    (
      "core.translation.reaction.message-server",
      messageReactionTranslationPass
    ),
    (
      "core.translation.instance",
      reactorInstanceTranslationPass
    ),
    (
      "core.translation.body.mixed-order",
      Translation.compileBody mixedSourceBody == expectedMixedTargetBody
    ),
    (
      "core.translation.body.empty",
      Translation.compileBody [] == []
    ),
    (
      "core.translation.api.exact-program",
      exactProgramTranslationPass
    )
  ]

def translatorSoftwareCases : List (String × Bool) :=
  frontendSoftwareCases ++ translationSoftwareCases

def lookupSoftwareCase
    (identifier : String) :
    List (String × Bool) → Option Bool
  | [] => none
  | case :: rest =>
      if case.1 == identifier then
        some case.2
      else
        lookupSoftwareCase identifier rest

def runSoftwareCase
    (identifier : String) : IO UInt32 :=
  match lookupSoftwareCase identifier translatorSoftwareCases with
  | none => do
      IO.eprintln ("unknown translator software test: " ++ identifier)
      pure 2
  | some false => do
      IO.eprintln ("FAIL " ++ identifier)
      pure 1
  | some true => do
      IO.println ("PASS " ++ identifier)
      pure 0

end Tests
end Relico

def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | [identifier] =>
      Relico.Tests.runSoftwareCase identifier
  | _ => do
      IO.eprintln "usage: relico-translator-test TEST_ID"
      pure 2
