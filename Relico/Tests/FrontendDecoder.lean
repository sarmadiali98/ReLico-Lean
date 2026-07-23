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
  match
    Frontend.decodeModelText
      validBridgeJson
  with
  | .ok model =>
      model == validModel
  | .error _ =>
      false

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
