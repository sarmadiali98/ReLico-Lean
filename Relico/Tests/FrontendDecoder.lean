import Relico.Frontend.Decoder
import Relico.Tests.DTRWellFormed
import Std.Tactic

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Relico
namespace Tests

def validRawConstructorBody :
    List Frontend.RawStmt := [
  {
    kind := "assign"
    target? := some "x"
    expression? := some {
      kind := "intLiteral"
      value? := some 0
    }
  },
  {
    kind := "selfSend"
    message? := some "tick"
    delay? := some 1
  }
]

def validRawMessageServerBody :
    List Frontend.RawStmt := [
  {
    kind := "assign"
    target? := some "x"
    expression? := some {
      kind := "stateVar"
      name? := some "x"
    }
  },
  {
    kind := "selfSend"
    message? := some "tick"
    delay? := some 1
  }
]

def validRawModel :
    Frontend.RawModel where
  schemaVersion :=
    Frontend.bridgeSchemaVersion
  className :=
    "Controller"
  actorName :=
    "controller"
  actorClass :=
    "Controller"
  stateVar :=
    "x"
  messageServer :=
    "tick"
  constructorBody :=
    validRawConstructorBody
  messageServerBody :=
    validRawMessageServerBody

theorem validRawModel_decodes :
    Frontend.decodeRawModel
        validRawModel =
      .ok validModel := by
  rfl

def validBridgeJson : String :=
  "{\n" ++
  "  \"schemaVersion\": 1,\n" ++
  "  \"className\": \"Controller\",\n" ++
  "  \"actorName\": \"controller\",\n" ++
  "  \"actorClass\": \"Controller\",\n" ++
  "  \"stateVar\": \"x\",\n" ++
  "  \"messageServer\": \"tick\",\n" ++
  "  \"constructorBody\": [\n" ++
  "    {\n" ++
  "      \"kind\": \"assign\",\n" ++
  "      \"target\": \"x\",\n" ++
  "      \"expression\": {\n" ++
  "        \"kind\": \"intLiteral\",\n" ++
  "        \"value\": 0\n" ++
  "      }\n" ++
  "    },\n" ++
  "    {\n" ++
  "      \"kind\": \"selfSend\",\n" ++
  "      \"message\": \"tick\",\n" ++
  "      \"delay\": 1\n" ++
  "    }\n" ++
  "  ],\n" ++
  "  \"messageServerBody\": [\n" ++
  "    {\n" ++
  "      \"kind\": \"assign\",\n" ++
  "      \"target\": \"x\",\n" ++
  "      \"expression\": {\n" ++
  "        \"kind\": \"stateVar\",\n" ++
  "        \"name\": \"x\"\n" ++
  "      }\n" ++
  "    },\n" ++
  "    {\n" ++
  "      \"kind\": \"selfSend\",\n" ++
  "      \"message\": \"tick\",\n" ++
  "      \"delay\": 1\n" ++
  "    }\n" ++
  "  ]\n" ++
  "}\n"

def validJsonDecodeTest : Bool :=
  match Frontend.decodeModelText validBridgeJson with
  | .ok model => model == validModel
  | .error _ => false

#guard validJsonDecodeTest

def unsupportedStatementRawModel :
    Frontend.RawModel :=
  {
    validRawModel with
    constructorBody := [
      {
        kind := "while"
      }
    ]
  }

theorem unsupportedStatement_is_rejected :
    Frontend.decodeRawModel
        unsupportedStatementRawModel =
      .error
        (.unsupportedStatement "while") := by
  rfl

structure ExpressionDecoderCase where
  id : String
  input : Frontend.RawExpr
  expected : Except Frontend.DecodeError DTR.Expr

def expressionDecoderCases : List ExpressionDecoderCase := [
  {
    id := "core.frontend.expression.int-literal"
    input := {
      kind := "intLiteral"
      value? := some 7
    }
    expected := .ok (.intLiteral 7)
  },
  {
    id := "core.frontend.expression.negative-int-literal"
    input := {
      kind := "intLiteral"
      value? := some (-1)
    }
    expected := .ok (.intLiteral (-1))
  },
  {
    id := "core.frontend.expression.state-var"
    input := {
      kind := "stateVar"
      name? := some "x"
    }
    expected := .ok (.stateVar ⟨"x"⟩)
  },
  {
    id := "core.frontend.expression.missing-value"
    input := {
      kind := "intLiteral"
    }
    expected := .error (.missingField "expression.value")
  },
  {
    id := "core.frontend.expression.missing-name"
    input := {
      kind := "stateVar"
    }
    expected := .error (.missingField "expression.name")
  },
  {
    id := "core.frontend.expression.name-mismatch"
    input := {
      kind := "stateVar"
      name? := some "y"
    }
    expected := .error
      (.nameMismatch "state-variable reference" "x" "y")
  },
  {
    id := "core.frontend.expression.unsupported"
    input := {
      kind := "binary"
    }
    expected := .error (.unsupportedExpression "binary")
  }
]

def expressionDecoderCasePass
    (case : ExpressionDecoderCase) : Bool :=
    match
      Frontend.decodeExpr "x" case.input,
      case.expected
    with
    | .ok actual, .ok expected => actual == expected
    | .error actual, .error expected => actual == expected
    | _, _ => false

def expressionDecoderCasesPass : Bool :=
  expressionDecoderCases.all expressionDecoderCasePass

#guard expressionDecoderCasesPass

structure StatementDecoderCase where
  id : String
  input : Frontend.RawStmt
  expected : Except Frontend.DecodeError DTR.Stmt

def statementDecoderCases : List StatementDecoderCase := [
  {
    id := "core.frontend.statement.assign"
    input := {
      kind := "assign"
      target? := some "x"
      expression? := some {
        kind := "intLiteral"
        value? := some 1
      }
    }
    expected := .ok (.assign ⟨"x"⟩ (.intLiteral 1))
  },
  {
    id := "core.frontend.statement.self-send"
    input := {
      kind := "selfSend"
      message? := some "tick"
      delay? := some 2
    }
    expected := .ok (.selfSend ⟨"tick"⟩ ⟨2⟩)
  },
  {
    id := "core.frontend.statement.self-send.zero-delay"
    input := {
      kind := "selfSend"
      message? := some "tick"
      delay? := some 0
    }
    expected := .ok (.selfSend ⟨"tick"⟩ ⟨0⟩)
  },
  {
    id := "core.frontend.statement.missing-target"
    input := {
      kind := "assign"
    }
    expected := .error (.missingField "statement.target")
  },
  {
    id := "core.frontend.statement.target-mismatch"
    input := {
      kind := "assign"
      target? := some "y"
    }
    expected := .error
      (.nameMismatch "assignment target" "x" "y")
  },
  {
    id := "core.frontend.statement.missing-expression"
    input := {
      kind := "assign"
      target? := some "x"
    }
    expected := .error (.missingField "statement.expression")
  },
  {
    id := "core.frontend.statement.assign.nested-expression-error"
    input := {
      kind := "assign"
      target? := some "x"
      expression? := some {
        kind := "binary"
      }
    }
    expected := .error (.unsupportedExpression "binary")
  },
  {
    id := "core.frontend.statement.missing-message"
    input := {
      kind := "selfSend"
    }
    expected := .error (.missingField "statement.message")
  },
  {
    id := "core.frontend.statement.message-mismatch"
    input := {
      kind := "selfSend"
      message? := some "missing"
    }
    expected := .error
      (.nameMismatch "self-send target" "tick" "missing")
  },
  {
    id := "core.frontend.statement.missing-delay"
    input := {
      kind := "selfSend"
      message? := some "tick"
    }
    expected := .error (.missingField "statement.delay")
  },
  {
    id := "core.frontend.statement.unsupported"
    input := {
      kind := "while"
    }
    expected := .error (.unsupportedStatement "while")
  }
]

def statementDecoderCasePass
    (case : StatementDecoderCase) : Bool :=
    match
      Frontend.decodeStmt "x" "tick" case.input,
      case.expected
    with
    | .ok actual, .ok expected => actual == expected
    | .error actual, .error expected => actual == expected
    | _, _ => false

def statementDecoderCasesPass : Bool :=
  statementDecoderCases.all statementDecoderCasePass

#guard statementDecoderCasesPass

structure ModelDecoderCase where
  id : String
  input : Frontend.RawModel
  expected : Frontend.DecodeError

def modelDecoderCases : List ModelDecoderCase := [
  {
    id := "core.frontend.model.schema-version"
    input := {
      validRawModel with
      schemaVersion := 99
      className := ""
    }
    expected := .invalidSchemaVersion 99
  },
  {
    id := "core.frontend.model.empty-class-name"
    input := {
      validRawModel with
      className := ""
    }
    expected := .emptyName "className"
  },
  {
    id := "core.frontend.model.empty-actor-name"
    input := {
      validRawModel with
      actorName := ""
    }
    expected := .emptyName "actorName"
  },
  {
    id := "core.frontend.model.empty-actor-class"
    input := {
      validRawModel with
      actorClass := ""
    }
    expected := .emptyName "actorClass"
  },
  {
    id := "core.frontend.model.empty-state-var"
    input := {
      validRawModel with
      stateVar := ""
    }
    expected := .emptyName "stateVar"
  },
  {
    id := "core.frontend.model.empty-message-server"
    input := {
      validRawModel with
      messageServer := ""
    }
    expected := .emptyName "messageServer"
  },
  {
    id := "core.frontend.model.actor-class-mismatch"
    input := {
      validRawModel with
      actorClass := "OtherController"
    }
    expected := .nameMismatch
      "actorClass"
      "Controller"
      "OtherController"
  },
  {
    id := "core.frontend.model.message-server-body-error"
    input := {
      validRawModel with
      messageServerBody := [{
        kind := "selfSend"
        message? := some "tick"
      }]
    }
    expected := .missingField "statement.delay"
  }
]

def modelDecoderCasePass
    (case : ModelDecoderCase) : Bool :=
    match Frontend.decodeRawModel case.input with
    | .error error => error == case.expected
    | .ok _ => false

def modelDecoderCasesPass : Bool :=
  modelDecoderCases.all modelDecoderCasePass

#guard modelDecoderCasesPass

structure JsonDecoderCase where
  id : String
  input : String
  expected : Except Frontend.DecodeError DTR.Model

def jsonDecoderCases : List JsonDecoderCase := [
  {
    id := "core.frontend.json.valid-model"
    input := validBridgeJson
    expected := .ok validModel
  },
  {
    id := "core.frontend.json.semantic-schema-version"
    input := validBridgeJson.replace
      "\"schemaVersion\": 1"
      "\"schemaVersion\": 2"
    expected := .error (.invalidSchemaVersion 2)
  },
  {
    id := "core.frontend.json.malformed"
    input := "{"
    expected := .error (.invalidJson "")
  },
  {
    id := "core.frontend.json.wrong-root"
    input := "[]"
    expected := .error (.invalidJson "")
  },
  {
    id := "core.frontend.json.missing-fields"
    input := "{}"
    expected := .error (.invalidJson "")
  }
]

def jsonDecoderCasePass
    (case : JsonDecoderCase) : Bool :=
  match Frontend.decodeModelText case.input, case.expected with
  | .ok actual, .ok expected => actual == expected
  | .error (.invalidJson _), .error (.invalidJson _) => true
  | .error actual, .error expected => actual == expected
  | _, _ => false

def jsonDecoderCasesPass : Bool :=
  jsonDecoderCases.all jsonDecoderCasePass

#guard jsonDecoderCasesPass

def wrongActorClassRawModel :
    Frontend.RawModel :=
  {
    validRawModel with
    actorClass := "OtherController"
  }

theorem wrongActorClass_is_rejected :
    Frontend.decodeRawModel
        wrongActorClassRawModel =
      .error
        (.nameMismatch
          "actorClass"
          "Controller"
          "OtherController") := by
  rfl

end Tests
end Relico
