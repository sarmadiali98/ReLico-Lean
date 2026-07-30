import Relico.LF.MultiStoreCppPrinter
import Relico.LF.MultiStorePayloadSyntax
import Relico.LF.PayloadCppPrinter

set_option autoImplicit false

namespace Relico
namespace LF
namespace CppPrinter

/--
Render one payload-aware expression as reactor-cpp target code.

Persistent-state references and reaction-local parameter references are
both ordinary C++ identifiers in the emitted reaction body.
-/
def renderMultiStorePayloadExpr :
    LF.MultiStorePayloadExpr →
    String

  | .intLiteral value =>
      toString value

  | .stateVar variableName =>
      variableName.value

  | .parameterVar parameterName =>
      parameterName.value

/--
Render an ordered payload-expression list without changing component
order.
-/
def renderMultiStorePayloadExprs
    (expressions :
      List LF.MultiStorePayloadExpr) :
    String :=
  String.intercalate
    ", "
    (expressions.map
      renderMultiStorePayloadExpr)

/--
Render one payload-aware statement.

The current executable backend foundation supports:

- no-payload scheduling, using the existing `void` logical-action API;
- one-integer scheduling, using the validated reactor-cpp API in which
  the payload precedes the delay.

Larger payload products are rejected explicitly until the backend
introduces a concrete generated product type.
-/
def renderMultiStorePayloadStmt :
    LF.MultiStorePayloadStmt →
    Except String String

  | .assign target expression =>
      .ok
        (target.value ++
          " = " ++
          renderMultiStorePayloadExpr
            expression ++
          ";")

  | .schedule
      action
      payloadExpressions
      delay =>

      match payloadExpressions with

      | [] =>
          .ok
            (action.value ++
              ".schedule(" ++
              renderDelay delay ++
              ");")

      | [payloadExpression] =>
          .ok
            (action.value ++
              ".schedule(" ++
              renderMultiStorePayloadExpr
                payloadExpression ++
              ", " ++
              renderDelay delay ++
              ");")

      | _ =>
          .error
            ("logical action `" ++
              action.value ++
              "` has more than one payload value; " ++
              "the current C++ printer foundation supports at most one integer payload")

/--
Collect scheduled logical-action names in first-occurrence order.
-/
def scheduledMultiStorePayloadActionNames
    (body : LF.MultiStorePayloadBody) :
    List String :=
  body.foldl
    (fun names statement =>
      match statement with

      | .assign _ _ =>
          names

      | .schedule action _ _ =>
          if names.contains action.value then
            names
          else
            names ++
              [action.value])
    []

/--
Render the LF effect list required for scheduling logical actions.
-/
def renderMultiStorePayloadEffects
    (body : LF.MultiStorePayloadBody) :
    String :=
  match
    scheduledMultiStorePayloadActionNames
      body
  with

  | [] =>
      ""

  | actionNames =>
      " -> " ++
        String.intercalate
          ", "
          actionNames

/--
Render one logical-action declaration.

The current backend foundation maps:

- zero formal parameters to `void`;
- one formal parameter to `int`.

Multiple formal parameters remain represented in the verified LF AST,
but are rejected here until a concrete C++ product representation is
installed.
-/
def renderMultiStorePayloadActionDecl
    (action : LF.MultiStorePayloadAction) :
    Except String String :=
  match action.parameters with

  | [] =>
      .ok
        ("  logical action " ++
          action.name.value ++
          ": void")

  | [_] =>
      .ok
        ("  logical action " ++
          action.name.value ++
          ": int")

  | _ =>
      .error
        ("logical action `" ++
          action.name.value ++
          "` declares more than one parameter; " ++
          "the current C++ printer foundation supports at most one integer payload")

/--
Render ordered logical-action declarations.
-/
def renderMultiStorePayloadActionDecls
    (actions :
      List LF.MultiStorePayloadAction) :
    Except String String := do

  let declarations ←
    actions.mapM
      renderMultiStorePayloadActionDecl

  pure
    (String.intercalate
      "\n"
      declarations)

/--
Render a payload-aware reaction trigger.
-/
def renderMultiStorePayloadTrigger :
    LF.MultiStorePayloadTrigger →
    String

  | .startup =>
      "startup"

  | .logicalAction action =>
      action.value

/--
Render reaction-local payload extraction.

A one-integer logical-action payload is bound to the source formal
parameter name before translated statements execute.
-/
def renderMultiStorePayloadParameterRead
    (reaction :
      LF.MultiStorePayloadReaction) :
    Except String String :=
  match reaction.trigger,
      reaction.parameters
  with

  | .startup, [] =>
      .ok ""

  | .startup, _ =>
      .error
        ("startup reaction `" ++
          reaction.name.value ++
          "` must not declare payload parameters")

  | .logicalAction _, [] =>
      .ok ""

  | .logicalAction action,
      [parameter] =>
      .ok
        ("    auto " ++
          parameter.value ++
          " = *" ++
          action.value ++
          ".get();")

  | .logicalAction action, _ =>
      .error
        ("reaction `" ++
          reaction.name.value ++
          "` for logical action `" ++
          action.value ++
          "` declares more than one parameter; " ++
          "the current C++ printer foundation supports at most one integer payload")

/--
Render one payload-aware reaction body, including trigger-payload
extraction when required.
-/
def renderMultiStorePayloadBody
    (reaction :
      LF.MultiStorePayloadReaction) :
    Except String String := do

  let parameterRead ←
    renderMultiStorePayloadParameterRead
      reaction

  let statements ←
    reaction.body.mapM
      renderMultiStorePayloadStmt

  let statementLines :=
    statements.map
      (fun statement =>
        "    " ++
          statement)

  let lines :=
    if parameterRead == "" then
      statementLines
    else
      parameterRead ::
        statementLines

  pure
    (String.intercalate
      "\n"
      lines)

/--
Render one payload-aware reaction.
-/
def renderMultiStorePayloadReaction
    (reaction :
      LF.MultiStorePayloadReaction) :
    Except String String := do

  let body ←
    renderMultiStorePayloadBody
      reaction

  pure
    ("  reaction(" ++
      renderMultiStorePayloadTrigger
        reaction.trigger ++
      ")" ++
      renderMultiStorePayloadEffects
        reaction.body ++
      " {=\n" ++
      body ++
      "\n  =}")

/--
Render payload-aware message reactions in their existing semantic
priority order.
-/
def renderMultiStorePayloadMessageReactions :
    List LF.MultiStorePayloadReaction →
    Except String String

  | [] =>
      .ok ""

  | [reaction] =>
      renderMultiStorePayloadReaction
        reaction

  | reaction :: remaining => do
      let renderedReaction ←
        renderMultiStorePayloadReaction
          reaction

      let renderedRemaining ←
        renderMultiStorePayloadMessageReactions
          remaining

      pure
        (renderedReaction ++
          "\n\n" ++
          renderedRemaining)

/--
Render a payload-aware finite-store reactor.

Priority metadata is not printed directly. The translator has already
normalized logical actions and message reactions into semantic priority
order.
-/
def renderMultiStorePayloadReactor
    (reactor :
      LF.MultiStorePayloadReactor) :
    Except String String := do

  let actionDeclarations ←
    renderMultiStorePayloadActionDecls
      reactor.logicalActions

  let startupReaction ←
    renderMultiStorePayloadReaction
      reactor.startupReaction

  let messageReactions ←
    renderMultiStorePayloadMessageReactions
      reactor.messageReactions

  let stateDeclarations :=
    renderStateVariableDecls
      reactor.stateVariables

  let declarations :=
    if stateDeclarations == "" then
      actionDeclarations
    else if actionDeclarations == "" then
      stateDeclarations
    else
      stateDeclarations ++
        "\n" ++
        actionDeclarations

  let reactions :=
    if messageReactions == "" then
      startupReaction
    else
      startupReaction ++
        "\n\n" ++
        messageReactions

  pure
    ("reactor " ++
      reactor.name.value ++
      " {\n" ++
      declarations ++
      "\n\n" ++
      reactions ++
      "\n}\n")

/--
Render a complete payload-aware LF/C++ program.
-/
def renderMultiStorePayloadProgram
    (program :
      LF.MultiStorePayloadProgram) :
    Except String String := do

  let reactor ←
    renderMultiStorePayloadReactor
      program.reactor

  pure
    (targetHeader ++
      "\n\n" ++
      reactor ++
      "\n" ++
      renderMain
        program.reactorInstance ++
      "\n")

@[simp]
theorem renderMultiStorePayloadExpr_intLiteral
    (value : Int) :
    renderMultiStorePayloadExpr
        (.intLiteral value) =
      toString value := by
  rfl

@[simp]
theorem renderMultiStorePayloadExpr_stateVar
    (variableName : VarName) :
    renderMultiStorePayloadExpr
        (.stateVar variableName) =
      variableName.value := by
  rfl

@[simp]
theorem renderMultiStorePayloadExpr_parameterVar
    (parameterName : VarName) :
    renderMultiStorePayloadExpr
        (.parameterVar parameterName) =
      parameterName.value := by
  rfl

end CppPrinter
end LF
end Relico
