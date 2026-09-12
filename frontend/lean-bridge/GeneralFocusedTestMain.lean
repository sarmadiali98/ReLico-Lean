import Relico.Frontend.GeneralDecoder
import Relico.Translation.GeneralBasic

set_option autoImplicit false

namespace Relico
namespace GeneralFocusedTests

open Lean

private def emptyScope : Frontend.GeneralScope where
  stateVariables := []
  parameters := []
  locals := []

private def stateScope : Frontend.GeneralScope where
  stateVariables := ["count"]
  parameters := []
  locals := []

private def parameterScope : Frontend.GeneralScope where
  stateVariables := []
  parameters := ["value"]
  locals := []

private def intRaw (value : Int) : Frontend.RawGeneralExpr where
  kind := "intLiteral"
  value := some (toJson value)

private def boolRaw (value : Bool) : Frontend.RawGeneralExpr where
  kind := "boolLiteral"
  value := some (toJson value)

private def variableRaw (name : String) : Frontend.RawGeneralExpr where
  kind := "variable"
  name := some name

private def selfTargetJson : Json :=
  Json.mkObj [("kind", toJson "self")]

private def stateName : VarName :=
  VarName.mk "count"

private def messageName : MsgName :=
  MsgName.mk "tick"

private def bodyContext : Translation.GeneralBodyContext where
  bodyKey := .messageServer messageName
  selfSends := []

private def reasonIs
    (expected : Frontend.GeneralDiagnosticReason)
    {α : Type}
    (result : Frontend.GeneralElab α) : Bool :=
  match result with
  | .error diagnostic => diagnostic.reason == expected
  | .ok _ => false

private def undeclaredVariableCase : Bool :=
  reasonIs
    .undeclaredVariable
    (Frontend.resolveVariable emptyScope "missing" "Worker.run" (some 12))

private def duplicateParameterCase : Bool :=
  let parameter : Frontend.RawGeneralParameter :=
    { name := "value", type := "int" }
  let server : Frontend.RawGeneralMessageServer :=
    {
      body := []
      name := "run"
      parameters := [parameter, parameter]
    }
  reasonIs
    .duplicateParameter
    (Frontend.elaborateMessageServer [] "Worker" server)

private def operatorPrecedenceCase : Bool :=
  let expression : Frontend.RawGeneralExpr :=
    {
      kind := "binary"
      operator := some "**"
      left := some (variableRaw "missing")
      right := some (intRaw 1)
    }
  reasonIs
    .unknownBinaryOperator
    (Frontend.elaborateExpr emptyScope "Worker.run" expression)

private def sendTargetPrecedenceCase : Bool :=
  let statement : Frontend.RawGeneralStmt :=
    {
      kind := "send"
      target := some (Json.mkObj [("kind", toJson "broadcast")])
      messageServer := some "tick"
      after := some (variableRaw "late")
      arguments := some [variableRaw "missing"]
    }
  reasonIs
    .unsupportedSendTargetKind
    (Frontend.elaborateStmt emptyScope "Worker.run" statement)

/-- The send's target is valid and its argument list is empty, so elaboration reaches the
    delay field: a non-literal `after` is refused as `nonConstantDelay` before any value is
    produced. No Rebeca source and no exporter document can carry this shape -- the exporter
    refuses a non-literal after at its own boundary, which is why this diagnostic is pinned
    here rather than by a registry fixture. -/
private def nonConstantDelayCase : Bool :=
  let statement : Frontend.RawGeneralStmt :=
    {
      kind := "send"
      target := some (Json.mkObj [("kind", toJson "self")])
      messageServer := some "tick"
      after := some (variableRaw "late")
      arguments := some []
    }
  reasonIs
    .nonConstantDelay
    (Frontend.elaborateStmt emptyScope "Worker.run" statement)

private def messagePayloadArityCase : Bool :=
  let receiver : DTR.GeneralReactiveClass :=
    {
      name := ClassName.mk "Receiver"
      knownRebecs := []
      stateVariables := []
      constructor := { parameters := [], body := [] }
      messageServers :=
        [{
          name := MsgName.mk "receive"
          parameters :=
            [{ name := VarName.mk "value", declaredType := .int }]
          body := []
        }]
    }
  let sender : DTR.GeneralReactiveClass :=
    {
      name := ClassName.mk "Sender"
      knownRebecs :=
        [{ name := KnownRebecName.mk "peer", className := receiver.name }]
      stateVariables := []
      constructor :=
        {
          parameters := []
          body :=
            [.send
              (.knownRebec (KnownRebecName.mk "peer"))
              (MsgName.mk "receive")
              []
              { value := 0 }]
        }
      messageServers := []
    }
  let model : DTR.GeneralModel :=
    {
      classes := [sender, receiver]
      instances :=
        [
          {
            name := ActorName.mk "sender"
            className := sender.name
            bindings := [(KnownRebecName.mk "peer", ActorName.mk "receiver")]
            arguments := []
          },
          {
            name := ActorName.mk "receiver"
            className := receiver.name
            bindings := []
            arguments := []
          }
        ]
    }
  Frontend.classifyGeneralWellFormedness model ==
    .sendsResolveToMessageServersFailed

private def decodedReasonIs
    (expected : Frontend.GeneralDiagnosticReason)
    (text : String) : Bool :=
  match Frontend.decodeGeneralModelText text with
  | .error diagnostic => diagnostic.reason == expected
  | .ok _ => false

private def runPromotedFixtureCase?
    (identifier : String) : IO (Option Bool) := do
  if identifier == "general.frontend.constructor-argument-arity" then
    let text ← IO.FS.readFile
      "frontend/fixtures/general/lean-reject/invalid-argument-arity.json"
    pure (some (decodedReasonIs .argumentsMatchConstructorFailed text))
  else if identifier == "general.frontend.statement.iteration" then
    let text ← IO.FS.readFile
      "frontend/fixtures/general/control-flow.parser.json"
    pure (some (decodedReasonIs .iterationNotSupported text))
  else
    pure none

private def generatedPortCollisionCase : Bool :=
  let startup : LF.GeneralReaction :=
    {
      name := ReactionName.mk "startup"
      trigger := .startup
      parameters := []
      body := []
    }
  let senderReactorName := ReactorName.mk "Sender"
  let receiverReactorName := ReactorName.mk "Receiver"
  let senderInstanceName := ActorName.mk "sender"
  let receiverInstanceName := ActorName.mk "receiver"
  let firstOutput :=
    Translation.outputPortNameFor
      (MsgName.mk "reportTo")
      (KnownRebecName.mk "hub")
      ""
  let secondOutput :=
    Translation.outputPortNameFor
      (MsgName.mk "report")
      (KnownRebecName.mk "toHub")
      ""
  let firstInput := Translation.inputPortNameFor senderInstanceName firstOutput
  let secondInput := Translation.inputPortNameFor senderInstanceName secondOutput
  let sender : LF.GeneralReactor :=
    {
      name := senderReactorName
      parameters := []
      inputPorts := []
      outputPorts := [{ name := firstOutput, payload := .scalar .int }]
      stateVariables := []
      logicalActions := []
      startupReaction := startup
      messageReactions := []
    }
  let receiver : LF.GeneralReactor :=
    {
      name := receiverReactorName
      parameters := []
      inputPorts := [{ name := firstInput, payload := .scalar .int }]
      outputPorts := []
      stateVariables := []
      logicalActions := []
      startupReaction := { startup with name := ReactionName.mk "receiverStartup" }
      messageReactions := []
    }
  let connectionFrom (outputPort inputPort : PortName) : LF.GeneralConnection :=
    {
      sourceInstance := senderInstanceName
      sourcePort := outputPort
      targetInstance := receiverInstanceName
      targetPort := inputPort
      delay := { value := 0 }
    }
  let program : LF.GeneralProgram :=
    {
      reactors := [sender, receiver]
      instances :=
        [ { name := senderInstanceName, reactorName := senderReactorName, arguments := [] },
          { name := receiverInstanceName, reactorName := receiverReactorName, arguments := [] } ]
      connections :=
        [ connectionFrom firstOutput firstInput,
          connectionFrom secondOutput secondInput ]
    }
  firstOutput == secondOutput &&
    firstInput == secondInput &&
    !program.targetEndpointsUnique &&
    match Translation.guardGeneralProgram program with
    | .error diagnostic => diagnostic.contains "two connections target the same input port"
    | .ok _ => false

private def zeroArityExternalPortCase : Bool :=
  reasonIsString
    "takes no parameters"
    (Translation.generalPortPayloadFor
      (ClassName.mk "Receiver")
      (MsgName.mk "ping")
      [])
where
  reasonIsString {α : Type} (fragment : String) : Except String α → Bool
    | .error diagnostic => diagnostic.contains fragment
    | .ok _ => false

private def conditionalTranslationCase : Bool :=
  let statement : DTR.GeneralStmt :=
    .ifThenElse
      (.boolLiteral true)
      [.assign stateName (.intLiteral 1)]
      [.assign stateName (.intLiteral 2)]
  match Translation.compileGeneralStmt [] bodyContext 0 statement with
  | .ok compiled =>
      compiled ==
        .ifThenElse
          (.boolLiteral true)
          [.assign stateName (.intLiteral 1)]
          [.assign stateName (.intLiteral 2)]
  | .error _ => false

private def localTranslationCase : Bool :=
  match
      Translation.compileGeneralStmt
        []
        bodyContext
        0
        (.localDecl (VarName.mk "tmp") .boolean (.boolLiteral true)) with
  | .ok compiled =>
      compiled == .localDecl (VarName.mk "tmp") .boolean (.boolLiteral true)
  | .error _ => false

private def selfSendTranslationCase : Bool :=
  let send : Translation.GeneralSelfSend :=
    {
      site := { body := bodyContext.bodyKey, index := [0] }
      message := messageName
      delay := { value := 3 }
    }
  let context : Translation.GeneralBodyContext :=
    { bodyKey := bodyContext.bodyKey, selfSends := [send] }
  match
      Translation.compileGeneralStmt
        []
        context
        0
        (.send .selfTarget messageName [.intLiteral 7] { value := 3 }) with
  | .ok compiled =>
      compiled ==
        .schedule
          (Translation.generalActionNameAtSite [send] send.site messageName)
          [.intLiteral 7]
          { value := 3 }
  | .error _ => false

private def externalSendTranslationCase : Bool :=
  let site : Translation.SendSite :=
    { body := bodyContext.bodyKey, index := [0] }
  let entry : Translation.GeneralOutputPortEntry :=
    {
      site := site
      knownRebec := KnownRebecName.mk "peer"
      message := MsgName.mk "receive"
      receiverClass := ClassName.mk "Receiver"
      outputPort := PortName.mk "receiveToPeer"
      payload := .scalar .int
      delay := { value := 5 }
    }
  match
      Translation.compileGeneralStmt
        [entry]
        bodyContext
        0
        (.send
          (.knownRebec entry.knownRebec)
          entry.message
          [.intLiteral 9]
          { value := 5 }) with
  | .ok compiled => compiled == .setPort entry.outputPort [.intLiteral 9]
  | .error _ => false

private def localScopeCase : Bool :=
  let body : List Frontend.RawGeneralStmt :=
    [
      {
        kind := "declare"
        name := some "tmp"
        type := some "int"
        value := some (intRaw 1)
      },
      {
        kind := "assign"
        target := some (toJson "count")
        value := some (variableRaw "tmp")
      }
    ]
  match Frontend.elaborateBody stateScope "Worker.run" body with
  | .ok elaborated =>
      elaborated ==
        [
          .localDecl (VarName.mk "tmp") .int (.intLiteral 1),
          .assign stateName (.parameterVar (VarName.mk "tmp"))
        ]
  | .error _ => false

private def localShadowingPrecedenceCase : Bool :=
  let statement : Frontend.RawGeneralStmt :=
    {
      kind := "declare"
      name := some "value"
      type := some "unsupported"
      value := some (variableRaw "missing")
    }
  reasonIs
    .localShadowsDeclaredName
    (Frontend.elaborateStmt parameterScope "Worker.run" statement)

private def selfTargetCase : Bool :=
  match Frontend.elaborateSendTarget selfTargetJson "Worker.run" (some 4) with
  | .ok target => target == .selfTarget
  | .error _ => false

def cases : List (String × Bool) :=
  [
    ("general.frontend.reference.undeclared", undeclaredVariableCase),
    ("general.frontend.parameter.duplicate", duplicateParameterCase),
    ("general.frontend.precedence.operator-before-operands", operatorPrecedenceCase),
    ("general.frontend.precedence.target-before-arguments-delay", sendTargetPrecedenceCase),
    ("general.frontend.delay.non-constant", nonConstantDelayCase),
    ("general.frontend.send.payload-arity", messagePayloadArityCase),
    ("general.frontend.scope.local-threading", localScopeCase),
    ("general.frontend.precedence.local-shadow-before-type-value", localShadowingPrecedenceCase),
    ("general.frontend.send-target.self", selfTargetCase),
    ("general.routing.external-zero-arity-refusal", zeroArityExternalPortCase),
    ("general.routing.generated-port-collision", generatedPortCollisionCase),
    ("general.translation.statement.conditional", conditionalTranslationCase),
    ("general.translation.statement.local-declaration", localTranslationCase),
    ("general.translation.statement.self-send", selfSendTranslationCase),
    ("general.translation.statement.external-send", externalSendTranslationCase)
  ]

private def lookupCase (identifier : String) : List (String × Bool) → Option Bool
  | [] => none
  | entry :: remaining =>
      if entry.1 == identifier then
        some entry.2
      else
        lookupCase identifier remaining

private def finishCase (identifier : String) : Option Bool → IO UInt32
  | none => do
      IO.eprintln ("unknown focused general test: " ++ identifier)
      pure 2
  | some false => do
      IO.eprintln ("FAIL " ++ identifier)
      pure 1
  | some true => do
      IO.println ("PASS " ++ identifier)
      pure 0

def runCase (identifier : String) : IO UInt32 := do
  match ← runPromotedFixtureCase? identifier with
  | some result => finishCase identifier (some result)
  | none => finishCase identifier (lookupCase identifier cases)

end GeneralFocusedTests
end Relico

def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | [identifier] =>
      Relico.GeneralFocusedTests.runCase identifier
  | _ => do
      IO.eprintln "usage: GeneralFocusedTestMain TEST_ID"
      pure 2
