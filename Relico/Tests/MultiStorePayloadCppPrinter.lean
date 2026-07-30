import Relico.LF.MultiStorePayloadCppPrinter

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Relico
namespace Tests
namespace MultiStorePayloadCppPrinter

def stateName :
    VarName :=
  ⟨"x"⟩

def parameterName :
    VarName :=
  ⟨"value"⟩

def secondParameterName :
    VarName :=
  ⟨"other"⟩

def actionName :
    ActionName :=
  ⟨"deliver"⟩

def startupReactionName :
    ReactionName :=
  ⟨"startup_reaction"⟩

def messageReactionName :
    ReactionName :=
  ⟨"deliver_reaction"⟩

def reactorName :
    ReactorName :=
  ⟨"PayloadController"⟩

def actorName :
    ActorName :=
  ⟨"controller"⟩

example :
    LF.CppPrinter.renderMultiStorePayloadExpr
        (.parameterVar parameterName) =
      "value" := by
  rfl

example :
    LF.CppPrinter.renderMultiStorePayloadStmt
        (.assign
          stateName
          (.parameterVar parameterName)) =
      .ok
        "x = value;" := by
  rfl

example :
    LF.CppPrinter.renderMultiStorePayloadStmt
        (.schedule
          actionName
          []
          ⟨1⟩) =
      .ok
        "deliver.schedule(1ms);" := by
  rfl

example :
    LF.CppPrinter.renderMultiStorePayloadStmt
        (.schedule
          actionName
          [.intLiteral 7]
          ⟨1⟩) =
      .ok
        "deliver.schedule(7, 1ms);" := by
  rfl

example :
    LF.CppPrinter.renderMultiStorePayloadStmt
        (.schedule
          actionName
          [
            .intLiteral 7,
            .intLiteral 9
          ]
          ⟨1⟩) =
      .error
        ("logical action `deliver` has more than one payload value; " ++
          "the current C++ printer foundation supports at most one integer payload") := by
  rfl

example :
    LF.CppPrinter.renderMultiStorePayloadActionDecl
        {
          name :=
            actionName

          parameters :=
            [parameterName]
        } =
      .ok
        "  logical action deliver: int" := by
  rfl

example :
    LF.CppPrinter.renderMultiStorePayloadActionDecl
        {
          name :=
            actionName

          parameters :=
            [
              parameterName,
              secondParameterName
            ]
        } =
      .error
        ("logical action `deliver` declares more than one parameter; " ++
          "the current C++ printer foundation supports at most one integer payload") := by
  rfl

def startupReaction :
    LF.MultiStorePayloadReaction where

  name :=
    startupReactionName

  trigger :=
    .startup

  parameters :=
    []

  body :=
    [
      .assign
        stateName
        (.intLiteral 0),

      .schedule
        actionName
        [.intLiteral 7]
        ⟨1⟩
    ]

  priority :=
    none

def messageReaction :
    LF.MultiStorePayloadReaction where

  name :=
    messageReactionName

  trigger :=
    .logicalAction
      actionName

  parameters :=
    [parameterName]

  body :=
    [
      .assign
        stateName
        (.parameterVar
          parameterName)
    ]

  priority :=
    none

example :
    LF.CppPrinter.renderMultiStorePayloadReaction
        messageReaction =
      .ok
        ("  reaction(deliver) {=\n" ++
          "    auto value = *deliver.get();\n" ++
          "    x = value;\n" ++
          "  =}") := by
  rfl

def sampleProgram :
    LF.MultiStorePayloadProgram where

  reactor := {
    name :=
      reactorName

    stateVariables :=
      [
        {
          name :=
            stateName

          initialValue :=
            0
        }
      ]

    logicalActions :=
      [
        {
          name :=
            actionName

          parameters :=
            [parameterName]
        }
      ]

    startupReaction :=
      startupReaction

    messageReactions :=
      [messageReaction]
  }

  reactorInstance := {
    name :=
      actorName

    reactorName :=
      reactorName
  }

def expectedSampleProgramSource : String :=
  "target Cpp\n\n" ++
  "reactor PayloadController {\n" ++
  "  state x: int = 0\n" ++
  "  logical action deliver: int\n\n" ++
  "  reaction(startup) -> deliver {=\n" ++
  "    x = 0;\n" ++
  "    deliver.schedule(7, 1ms);\n" ++
  "  =}\n\n" ++
  "  reaction(deliver) {=\n" ++
  "    auto value = *deliver.get();\n" ++
  "    x = value;\n" ++
  "  =}\n" ++
  "}\n\n" ++
  "main reactor {\n" ++
  "  controller = new PayloadController()\n" ++
  "}\n"

example :
    LF.CppPrinter.renderMultiStorePayloadProgram
        sampleProgram =
      .ok
        expectedSampleProgramSource := by
  rfl

end MultiStorePayloadCppPrinter
end Tests
end Relico
