import Relico.DTR.StoreSyntax
import Relico.Frontend.Decoder
import Relico.Frontend.StoreSchema

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

private def requireStoreField
    {α : Type}
    (field : String)
    (value : Option α) :
    Except DecodeError α :=
  match value with
  | some result =>
      .ok result
  | none =>
      .error (.missingField field)

private def requireStoreName
    (field value : String) :
    Except DecodeError String :=
  if value == "" then
    .error (.emptyName field)
  else
    .ok value

private def requireStoreMatchingName
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

private def requireDeclaredStoreName
    (field : String)
    (declaredNames : List String)
    (actual : String) :
    Except DecodeError Unit :=
  if declaredNames.contains actual then
    .ok ()
  else
    .error
      (.nameMismatch
        field
        (String.intercalate ", " declaredNames)
        actual)

def decodeStoreExpr
    (declaredStateVariables : List String)
    (expression : RawExpr) :
    Except DecodeError DTR.Expr := do

  match expression.kind with
  | "intLiteral" =>
      let value ←
        requireStoreField
          "expression.value"
          expression.value?

      pure (.intLiteral value)

  | "stateVar" =>
      let name ←
        requireStoreField
          "expression.name"
          expression.name?

      requireDeclaredStoreName
        "state-variable reference"
        declaredStateVariables
        name

      pure (.stateVar ⟨name⟩)

  | kind =>
      .error
        (.unsupportedExpression kind)

def decodeStoreStmt
    (declaredStateVariables : List String)
    (declaredMessageServer : String)
    (statement : RawStmt) :
    Except DecodeError DTR.Stmt := do

  match statement.kind with
  | "assign" =>
      let target ←
        requireStoreField
          "statement.target"
          statement.target?

      requireDeclaredStoreName
        "assignment target"
        declaredStateVariables
        target

      let rawExpression ←
        requireStoreField
          "statement.expression"
          statement.expression?

      let expression ←
        decodeStoreExpr
          declaredStateVariables
          rawExpression

      pure
        (.assign
          ⟨target⟩
          expression)

  | "selfSend" =>
      let message ←
        requireStoreField
          "statement.message"
          statement.message?

      requireStoreMatchingName
        "self-send target"
        declaredMessageServer
        message

      let delay ←
        requireStoreField
          "statement.delay"
          statement.delay?

      pure
        (.selfSend
          ⟨message⟩
          ⟨delay⟩)

  | kind =>
      .error
        (.unsupportedStatement kind)

def decodeStoreBody
    (declaredStateVariables : List String)
    (declaredMessageServer : String)
    (body : List RawStmt) :
    Except DecodeError DTR.Body :=
  body.mapM
    (decodeStoreStmt
      declaredStateVariables
      declaredMessageServer)

def decodeRawStoreModel
    (raw : RawStoreModel) :
    Except DecodeError DTR.StoreModel := do

  if raw.schemaVersion == storeBridgeSchemaVersion then
    pure ()
  else
    throw
      (.invalidSchemaVersion
        raw.schemaVersion)

  let className ←
    requireStoreName
      "className"
      raw.className

  let actorName ←
    requireStoreName
      "actorName"
      raw.actorName

  let actorClass ←
    requireStoreName
      "actorClass"
      raw.actorClass

  let messageServer ←
    requireStoreName
      "messageServer"
      raw.messageServer

  requireStoreMatchingName
    "actorClass"
    className
    actorClass

  if raw.stateVariables.isEmpty then
    throw
      (.missingField
        "stateVariables")
  else
    pure ()

  let stateVariables ←
    raw.stateVariables.mapM
      (fun declaration => do
        let name ←
          requireStoreName
            "stateVariables.name"
            declaration.name

        pure {
          name := ⟨name⟩
          initialValue :=
            declaration.initialValue
        })

  let stateVariableNames :=
    raw.stateVariables.map
      (fun declaration =>
        declaration.name)

  let constructorBody ←
    decodeStoreBody
      stateVariableNames
      messageServer
      raw.constructorBody

  let messageServerBody ←
    decodeStoreBody
      stateVariableNames
      messageServer
      raw.messageServerBody

  pure {
    reactiveClass := {
      name := ⟨className⟩
      stateVariables :=
        stateVariables
      constructor := {
        body :=
          constructorBody
      }
      messageServer := {
        name := ⟨messageServer⟩
        body :=
          messageServerBody
      }
    }
    actor := {
      name := ⟨actorName⟩
      className := ⟨actorClass⟩
    }
  }

def decodeStoreModelText
    (text : String) :
    Except DecodeError DTR.StoreModel := do

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
        Except String RawStoreModel)
    with
    | .ok raw =>
        .ok raw
    | .error message =>
        .error
          (.invalidJson message)

  decodeRawStoreModel raw

end Frontend
end Relico
