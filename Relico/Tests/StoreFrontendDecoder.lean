import Relico.Frontend.StoreDecoder
import Std.Tactic

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Relico
namespace Tests

def decoderStoreX : VarName :=
  ⟨"x"⟩

def decoderStoreY : VarName :=
  ⟨"y"⟩

def validRawStoreModel :
    Frontend.RawStoreModel where
  schemaVersion :=
    Frontend.storeBridgeSchemaVersion
  className :=
    "TwoStateController"
  actorName :=
    "controller"
  actorClass :=
    "TwoStateController"
  stateVariables := [
    {
      name := "x"
      initialValue := 0
    },
    {
      name := "y"
      initialValue := 0
    }
  ]
  messageServer :=
    "tick"
  constructorBody := [
    {
      kind := "assign"
      target? := some "x"
      expression? := some {
        kind := "intLiteral"
        value? := some 1
      }
    },
    {
      kind := "assign"
      target? := some "y"
      expression? := some {
        kind := "intLiteral"
        value? := some 2
      }
    },
    {
      kind := "selfSend"
      message? := some "tick"
      delay? := some 1
    }
  ]
  messageServerBody := [
    {
      kind := "assign"
      target? := some "y"
      expression? := some {
        kind := "stateVar"
        name? := some "x"
      }
    }
  ]

def expectedDecodedStoreModel :
    DTR.StoreModel where
  reactiveClass := {
    name := ⟨"TwoStateController"⟩
    stateVariables := [
      {
        name := decoderStoreX
        initialValue := 0
      },
      {
        name := decoderStoreY
        initialValue := 0
      }
    ]
    constructor := {
      body := [
        .assign
          decoderStoreX
          (.intLiteral 1),
        .assign
          decoderStoreY
          (.intLiteral 2),
        .selfSend
          ⟨"tick"⟩
          ⟨1⟩
      ]
    }
    messageServer := {
      name := ⟨"tick"⟩
      body := [
        .assign
          decoderStoreY
          (.stateVar decoderStoreX)
      ]
    }
  }
  actor := {
    name := ⟨"controller"⟩
    className := ⟨"TwoStateController"⟩
  }

theorem validRawStoreModel_decodes :
    Frontend.decodeRawStoreModel
        validRawStoreModel =
      .ok expectedDecodedStoreModel := by
  rfl

def undeclaredAssignmentRawStoreModel :
    Frontend.RawStoreModel :=
  {
    validRawStoreModel with
    constructorBody := [
      {
        kind := "assign"
        target? := some "z"
        expression? := some {
          kind := "intLiteral"
          value? := some 0
        }
      }
    ]
  }

theorem undeclaredAssignment_is_rejected :
    Frontend.decodeRawStoreModel
        undeclaredAssignmentRawStoreModel =
      .error
        (.nameMismatch
          "assignment target"
          "x, y"
          "z") := by
  rfl

def undeclaredReferenceRawStoreModel :
    Frontend.RawStoreModel :=
  {
    validRawStoreModel with
    messageServerBody := [
      {
        kind := "assign"
        target? := some "y"
        expression? := some {
          kind := "stateVar"
          name? := some "z"
        }
      }
    ]
  }

theorem undeclaredReference_is_rejected :
    Frontend.decodeRawStoreModel
        undeclaredReferenceRawStoreModel =
      .error
        (.nameMismatch
          "state-variable reference"
          "x, y"
          "z") := by
  rfl

end Tests
end Relico
