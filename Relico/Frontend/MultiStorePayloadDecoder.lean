import Relico.DTR.MultiStorePayloadSyntax
import Relico.Frontend.MultiStorePayloadSchema

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

private def requirePayloadField
    {α : Type}
    (field : String)
    (value : Option α) :
    Except String α :=
  match value with

  | some result =>
      .ok result

  | none =>
      .error
        ("missing required field: " ++
          field)

private def requirePayloadName
    (field value : String) :
    Except String String :=
  if value == "" then
    .error
      ("name must not be empty: " ++
        field)
  else
    .ok value

private def requirePayloadMatchingName
    (field expected actual : String) :
    Except String Unit :=
  if actual == expected then
    .ok ()
  else
    .error
      ("unexpected " ++
        field ++
        ": expected `" ++
        expected ++
        "`, received `" ++
        actual ++ "`")

private def requirePayloadDeclaredName
    (field : String)
    (declaredNames : List String)
    (actual : String) :
    Except String Unit :=
  if declaredNames.contains actual then
    .ok ()
  else
    .error
      ("undeclared " ++
        field ++
        ": `" ++
        actual ++ "`")

private def firstDuplicatePayloadName? :
    List String →
    Option String

  | [] =>
      none

  | name :: remaining =>
      if remaining.contains name then
        some name
      else
        firstDuplicatePayloadName?
          remaining

private def requireUniquePayloadNames
    (field : String)
    (names : List String) :
    Except String Unit :=
  match firstDuplicatePayloadName? names with

  | none =>
      .ok ()

  | some duplicate =>
      .error
        ("duplicate " ++
          field ++
          ": `" ++
          duplicate ++ "`")

private def lookupMessageServerArity?
    (target : String) :
    List (String × Nat) →
    Option Nat

  | [] =>
      none

  | (name, arity) :: remaining =>
      if name == target then
        some arity
      else
        lookupMessageServerArity?
          target
          remaining

/--
Decode one expression against the state-variable environment and the ordered
formal-parameter environment of the current message server.
-/
def decodeMultiStorePayloadExpr
    (stateVariables : List String)
    (parameters : List String)
    (raw : RawMultiStorePayloadExpr) :
    Except String
      DTR.MultiStorePayloadExpr := do

  match raw.kind with

  | "intLiteral" =>
      let value ←
        requirePayloadField
          "expression.value"
          raw.value

      pure
        (.intLiteral value)

  | "stateVar" =>
      let name ←
        requirePayloadField
          "expression.name"
          raw.name

      requirePayloadDeclaredName
        "state-variable reference"
        stateVariables
        name

      pure
        (.stateVar ⟨name⟩)

  | "parameterVar" =>
      let name ←
        requirePayloadField
          "expression.name"
          raw.name

      requirePayloadDeclaredName
        "parameter reference"
        parameters
        name

      pure
        (.parameterVar ⟨name⟩)

  | kind =>
      .error
        ("unsupported expression kind: " ++
          kind)

/--
Decode one statement and validate self-send target existence and payload
arity.
-/
def decodeMultiStorePayloadStmt
    (stateVariables : List String)
    (messageServerSignatures :
      List (String × Nat))
    (parameters : List String)
    (raw : RawMultiStorePayloadStmt) :
    Except String
      DTR.MultiStorePayloadStmt := do

  match raw.kind with

  | "assign" =>
      let target ←
        requirePayloadField
          "statement.target"
          raw.target

      requirePayloadDeclaredName
        "assignment target"
        stateVariables
        target

      let rawExpression ←
        requirePayloadField
          "statement.expression"
          raw.expression

      let expression ←
        decodeMultiStorePayloadExpr
          stateVariables
          parameters
          rawExpression

      pure
        (.assign
          ⟨target⟩
          expression)

  | "selfSend" =>
      let message ←
        requirePayloadField
          "statement.message"
          raw.message

      let expectedArity ←
        match
          lookupMessageServerArity?
            message
            messageServerSignatures
        with

        | some arity =>
            .ok arity

        | none =>
            .error
              ("undeclared self-send target: `" ++
                message ++ "`")

      let rawArguments :=
        raw.arguments.getD
          []

      if rawArguments.length == expectedArity then
        pure ()
      else
        throw
          ("payload arity mismatch for `" ++
            message ++
            "`: expected " ++
            toString expectedArity ++
            ", received " ++
            toString rawArguments.length)

      let arguments ←
        rawArguments.mapM
          (decodeMultiStorePayloadExpr
            stateVariables
            parameters)

      let delay ←
        requirePayloadField
          "statement.delay"
          raw.delay

      pure
        (.selfSend
          ⟨message⟩
          arguments
          ⟨delay⟩)

  | kind =>
      .error
        ("unsupported statement kind: " ++
          kind)

def decodeMultiStorePayloadBody
    (stateVariables : List String)
    (messageServerSignatures :
      List (String × Nat))
    (parameters : List String)
    (body :
      List RawMultiStorePayloadStmt) :
    Except String
      DTR.MultiStorePayloadBody :=
  body.mapM
    (decodeMultiStorePayloadStmt
      stateVariables
      messageServerSignatures
      parameters)

/--
Validate and decode schema version 1 into the canonical local payload model.
-/
def decodeRawMultiStorePayloadModel
    (raw : RawMultiStorePayloadModel) :
    Except String
      DTR.MultiStorePayloadModel := do

  if
    raw.schemaVersion ==
      multiStorePayloadBridgeSchemaVersion
  then
    pure ()
  else
    throw
      ("unsupported payload schema version: " ++
        toString raw.schemaVersion)

  requirePayloadMatchingName
    "family"
    multiStorePayloadBridgeFamily
    raw.family

  let className ←
    requirePayloadName
      "className"
      raw.className

  let actorName ←
    requirePayloadName
      "actorName"
      raw.actorName

  let actorClass ←
    requirePayloadName
      "actorClass"
      raw.actorClass

  requirePayloadMatchingName
    "actorClass"
    className
    actorClass

  if raw.stateVariables.isEmpty then
    throw
      "stateVariables must not be empty"
  else
    pure ()

  if raw.messageServers.isEmpty then
    throw
      "messageServers must not be empty"
  else
    pure ()

  let stateVariableNames ←
    raw.stateVariables.mapM
      (fun declaration =>
        requirePayloadName
          "stateVariables.name"
          declaration.name)

  requireUniquePayloadNames
    "state-variable name"
    stateVariableNames

  let messageServerNames ←
    raw.messageServers.mapM
      (fun declaration =>
        requirePayloadName
          "messageServers.name"
          declaration.name)

  requireUniquePayloadNames
    "message-server name"
    messageServerNames

  let messageServerSignatures :=
    List.zip
      messageServerNames
      (raw.messageServers.map
        (fun declaration =>
          declaration.parameters.length))

  let stateVariables ←
    raw.stateVariables.mapM
      (fun declaration => do
        let name ←
          requirePayloadName
            "stateVariables.name"
            declaration.name

        pure {
          name :=
            ⟨name⟩

          initialValue :=
            declaration.initialValue
        })

  let constructorBody ←
    decodeMultiStorePayloadBody
      stateVariableNames
      messageServerSignatures
      []
      raw.constructorBody

  let messageServers ←
    raw.messageServers.mapM
      (fun declaration => do
        let name ←
          requirePayloadName
            "messageServers.name"
            declaration.name

        let parameters ←
          declaration.parameters.mapM
            (requirePayloadName
              "messageServers.parameters")

        requireUniquePayloadNames
          ("formal parameter of `" ++
            name ++
            "`")
          parameters

        let body ←
          decodeMultiStorePayloadBody
            stateVariableNames
            messageServerSignatures
            parameters
            declaration.body

        pure {
          name :=
            ⟨name⟩

          parameters :=
            parameters.map
              (fun parameter =>
                ⟨parameter⟩)

          priority :=
            declaration.priority

          body :=
            body
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
Parse JSON text and decode it into `DTR.MultiStorePayloadModel`.
-/
def decodeMultiStorePayloadModelText
    (text : String) :
    Except String
      DTR.MultiStorePayloadModel := do

  let json ←
    match Lean.Json.parse text with

    | .ok value =>
        .ok value

    | .error message =>
        .error
          ("invalid JSON: " ++
            message)

  let raw ←
    match
      (Lean.fromJson? json :
        Except String
          RawMultiStorePayloadModel)
    with

    | .ok value =>
        .ok value

    | .error message =>
        .error
          ("payload schema decode failed: " ++
            message)

  decodeRawMultiStorePayloadModel
    raw

end Frontend
end Relico
