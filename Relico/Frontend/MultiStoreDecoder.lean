import Relico.DTR.MultiStoreSyntax
import Relico.Frontend.MultiStoreSchema
import Relico.Frontend.StoreDecoder

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

private def requireMultiStoreName
    (field value : String) :
    Except DecodeError String :=
  if value == "" then
    .error
      (.emptyName field)
  else
    .ok value

private def requireMultiStoreMatchingName
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

private def requireMultiStoreDeclaredName
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
        (String.intercalate
          ", "
          declaredNames)
        actual)

private def requireMultiStoreField
    {α : Type}
    (field : String)
    (value : Option α) :
    Except DecodeError α :=
  match value with

  | some result =>
      .ok result

  | none =>
      .error
        (.missingField field)

private def firstDuplicateString? :
    List String →
    Option String

  | [] =>
      none

  | name :: remaining =>
      if remaining.contains name then
        some name
      else
        firstDuplicateString?
          remaining

private def requireUniqueNames
    (field expected : String)
    (names : List String) :
    Except DecodeError Unit :=
  match firstDuplicateString? names with

  | none =>
      .ok ()

  | some duplicate =>
      .error
        (.nameMismatch
          field
          expected
          duplicate)

/--
Decode a statement against all state-variable and message-server
declarations of the multi-server model.
-/
def decodeMultiStoreStmt
    (declaredStateVariables :
      List String)
    (declaredMessageServers :
      List String)
    (statement : RawStmt) :
    Except DecodeError DTR.Stmt := do

  match statement.kind with

  | "assign" =>
      let target ←
        requireMultiStoreField
          "statement.target"
          statement.target?

      requireMultiStoreDeclaredName
        "assignment target"
        declaredStateVariables
        target

      let rawExpression ←
        requireMultiStoreField
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
        requireMultiStoreField
          "statement.message"
          statement.message?

      requireMultiStoreDeclaredName
        "self-send target"
        declaredMessageServers
        message

      let delay ←
        requireMultiStoreField
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
Decode a body while allowing sends to every message server declared by
the current reactive class.
-/
def decodeMultiStoreBody
    (declaredStateVariables :
      List String)
    (declaredMessageServers :
      List String)
    (body : List RawStmt) :
    Except DecodeError DTR.Body :=
  body.mapM
    (decodeMultiStoreStmt
      declaredStateVariables
      declaredMessageServers)

/--
Validate and decode schema version 3 into the executable multi-server
DTR AST.

The decoded message-server list preserves parser declaration order.
Priority normalization is performed later by translation.
-/
def decodeRawMultiStoreModel
    (raw : RawMultiStoreModel) :
    Except DecodeError DTR.MultiStoreModel := do

  if
    raw.schemaVersion ==
      multiStoreBridgeSchemaVersion
  then
    pure ()
  else
    throw
      (.invalidSchemaVersion
        raw.schemaVersion)

  let className ←
    requireMultiStoreName
      "className"
      raw.className

  let actorName ←
    requireMultiStoreName
      "actorName"
      raw.actorName

  let actorClass ←
    requireMultiStoreName
      "actorClass"
      raw.actorClass

  requireMultiStoreMatchingName
    "actorClass"
    className
    actorClass

  if raw.stateVariables.isEmpty then
    throw
      (.missingField
        "stateVariables")
  else
    pure ()

  if raw.messageServers.isEmpty then
    throw
      (.missingField
        "messageServers")
  else
    pure ()

  let stateVariableNames ←
    raw.stateVariables.mapM
      (fun declaration =>
        requireMultiStoreName
          "stateVariables.name"
          declaration.name)

  requireUniqueNames
    "stateVariables.name"
    "unique state-variable names"
    stateVariableNames

  let messageServerNames ←
    raw.messageServers.mapM
      (fun declaration =>
        requireMultiStoreName
          "messageServers.name"
          declaration.name)

  requireUniqueNames
    "messageServers.name"
    "unique message-server names"
    messageServerNames

  let stateVariables ←
    raw.stateVariables.mapM
      (fun declaration => do
        let name ←
          requireMultiStoreName
            "stateVariables.name"
            declaration.name

        pure {
          name :=
            ⟨name⟩

          initialValue :=
            declaration.initialValue
        })

  let constructorBody ←
    decodeMultiStoreBody
      stateVariableNames
      messageServerNames
      raw.constructorBody

  let messageServers ←
    raw.messageServers.mapM
      (fun declaration => do
        let name ←
          requireMultiStoreName
            "messageServers.name"
            declaration.name

        let body ←
          decodeMultiStoreBody
            stateVariableNames
            messageServerNames
            declaration.body

        pure {
          name :=
            ⟨name⟩

          body :=
            body

          priority :=
            declaration.priority?
        })

  pure {
    reactiveClass := {
      name :=
        ⟨className⟩

      stateVariables :=
        stateVariables

      constructor := {
        body :=
          constructorBody
      }

      messageServers :=
        messageServers
    }

    actor := {
      name :=
        ⟨actorName⟩

      className :=
        ⟨actorClass⟩
    }
  }

/--
Parse schema-version-3 JSON text and decode it into the current
multi-server DTR AST.
-/
def decodeMultiStoreModelText
    (text : String) :
    Except DecodeError DTR.MultiStoreModel := do

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
        Except String RawMultiStoreModel)
    with

    | .ok raw =>
        .ok raw

    | .error message =>
        .error
          (.invalidJson message)

  decodeRawMultiStoreModel
    raw

end Frontend
end Relico
