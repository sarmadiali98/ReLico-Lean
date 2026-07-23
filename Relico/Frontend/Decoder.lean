import Relico.DTR.Syntax
import Relico.Frontend.Schema

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/--
Failures that may occur while decoding or validating parser-bridge
input.
-/
inductive DecodeError where
  | invalidJson (message : String)
  | invalidSchemaVersion (actual : Nat)
  | missingField (field : String)
  | emptyName (field : String)
  | nameMismatch
      (field : String)
      (expected : String)
      (actual : String)
  | unsupportedExpression (kind : String)
  | unsupportedStatement (kind : String)
  deriving Repr, DecidableEq

instance : ToString DecodeError where
  toString
    | .invalidJson message =>
        "invalid JSON: " ++ message

    | .invalidSchemaVersion actual =>
        "unsupported bridge schema version: " ++
          toString actual

    | .missingField field =>
        "missing required field: " ++ field

    | .emptyName field =>
        "name must not be empty: " ++ field

    | .nameMismatch field expected actual =>
        "unexpected " ++ field ++
          ": expected `" ++ expected ++
          "`, received `" ++ actual ++ "`"

    | .unsupportedExpression kind =>
        "unsupported expression kind: " ++ kind

    | .unsupportedStatement kind =>
        "unsupported statement kind: " ++ kind

private def requireField
    {α : Type}
    (field : String)
    (value : Option α) :
    Except DecodeError α :=
  match value with
  | some result =>
      .ok result
  | none =>
      .error (.missingField field)

private def requireName
    (field value : String) :
    Except DecodeError String :=
  if value == "" then
    .error (.emptyName field)
  else
    .ok value

private def requireMatchingName
    (field expected actual : String) :
    Except DecodeError Unit :=
  if actual == expected then
    .ok ()
  else
    .error
      (.nameMismatch
        field
        expected
        actual)

/--
Decode an expression and validate references to the single declared
state variable.
-/
def decodeExpr
    (declaredStateVar : String)
    (expression : RawExpr) :
    Except DecodeError DTR.Expr := do

  match expression.kind with
  | "intLiteral" =>
      let value ←
        requireField
          "expression.value"
          expression.value?

      pure
        (.intLiteral value)

  | "stateVar" =>
      let name ←
        requireField
          "expression.name"
          expression.name?

      requireMatchingName
        "state-variable reference"
        declaredStateVar
        name

      pure
        (.stateVar ⟨name⟩)

  | kind =>
      .error
        (.unsupportedExpression kind)

/--
Decode a statement and validate its target against the declarations of
the current v0 model.
-/
def decodeStmt
    (declaredStateVar : String)
    (declaredMessageServer : String)
    (statement : RawStmt) :
    Except DecodeError DTR.Stmt := do

  match statement.kind with
  | "assign" =>
      let target ←
        requireField
          "statement.target"
          statement.target?

      requireMatchingName
        "assignment target"
        declaredStateVar
        target

      let rawExpression ←
        requireField
          "statement.expression"
          statement.expression?

      let expression ←
        decodeExpr
          declaredStateVar
          rawExpression

      pure
        (.assign
          ⟨target⟩
          expression)

  | "selfSend" =>
      let message ←
        requireField
          "statement.message"
          statement.message?

      requireMatchingName
        "self-send target"
        declaredMessageServer
        message

      let delay ←
        requireField
          "statement.delay"
          statement.delay?

      pure
        (.selfSend
          ⟨message⟩
          ⟨delay⟩)

  | kind =>
      .error
        (.unsupportedStatement kind)

/--
Decode a complete executable body.
-/
def decodeBody
    (declaredStateVar : String)
    (declaredMessageServer : String)
    (body : List RawStmt) :
    Except DecodeError DTR.Body :=
  body.mapM
    (decodeStmt
      declaredStateVar
      declaredMessageServer)

/--
Validate and decode the stable parser-bridge representation into the
current Lean DTR AST.
-/
def decodeRawModel
    (raw : RawModel) :
    Except DecodeError DTR.Model := do

  if raw.schemaVersion == bridgeSchemaVersion then
    pure ()
  else
    throw
      (.invalidSchemaVersion
        raw.schemaVersion)

  let className ←
    requireName
      "className"
      raw.className

  let actorName ←
    requireName
      "actorName"
      raw.actorName

  let actorClass ←
    requireName
      "actorClass"
      raw.actorClass

  let stateVar ←
    requireName
      "stateVar"
      raw.stateVar

  let messageServer ←
    requireName
      "messageServer"
      raw.messageServer

  requireMatchingName
    "actorClass"
    className
    actorClass

  let constructorBody ←
    decodeBody
      stateVar
      messageServer
      raw.constructorBody

  let messageServerBody ←
    decodeBody
      stateVar
      messageServer
      raw.messageServerBody

  pure
    {
      reactiveClass := {
        name := ⟨className⟩
        stateVar := ⟨stateVar⟩
        constructor := {
          body := constructorBody
        }
        messageServer := {
          name := ⟨messageServer⟩
          body := messageServerBody
        }
      }
      actor := {
        name := ⟨actorName⟩
        className := ⟨actorClass⟩
      }
    }

/--
Parse JSON text and decode it into the current Lean DTR AST.
-/
def decodeModelText
    (text : String) :
    Except DecodeError DTR.Model := do

  let json ←
    match Lean.Json.parse text with
    | .ok json =>
        .ok json
    | .error message =>
        .error
          (.invalidJson message)

  let raw ←
    match
      (Lean.fromJson? json :
        Except String RawModel)
    with
    | .ok raw =>
        .ok raw
    | .error message =>
        .error
          (.invalidJson message)

  decodeRawModel raw

end Frontend
end Relico
