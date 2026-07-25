import Relico.Frontend.MultiStoreDecoder
import Relico.Translation.MultiStoreBasic
import Std.Tactic

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Relico
namespace Tests

def frontendMultiX :
    VarName :=
  ⟨"x"⟩

def frontendLowName :
    MsgName :=
  ⟨"low"⟩

def frontendHighName :
    MsgName :=
  ⟨"high"⟩

def validRawMultiStoreModel :
    Frontend.RawMultiStoreModel where

  schemaVersion :=
    Frontend.multiStoreBridgeSchemaVersion

  className :=
    "PriorityController"

  actorName :=
    "controller"

  actorClass :=
    "PriorityController"

  stateVariables := [
    {
      name :=
        "x"

      initialValue :=
        0
    }
  ]

  constructorBody := [
    {
      kind :=
        "selfSend"

      message? :=
        some "high"

      delay? :=
        some 1
    },
    {
      kind :=
        "selfSend"

      message? :=
        some "low"

      delay? :=
        some 1
    }
  ]

  messageServers := [
    {
      name :=
        "low"

      priority? :=
        some 4

      body := [
        {
          kind :=
            "assign"

          target? :=
            some "x"

          expression? :=
            some {
              kind :=
                "intLiteral"

              value? :=
                some 0
            }
        }
      ]
    },
    {
      name :=
        "high"

      priority? :=
        some 1

      body := [
        {
          kind :=
            "selfSend"

          message? :=
            some "low"

          delay? :=
            some 2
        }
      ]
    }
  ]

def expectedDecodedMultiStoreModel :
    DTR.MultiStoreModel where

  reactiveClass := {
    name :=
      ⟨"PriorityController"⟩

    stateVariables := [
      {
        name :=
          frontendMultiX

        initialValue :=
          0
      }
    ]

    constructor := {
      body := [
        .selfSend
          frontendHighName
          ⟨1⟩,

        .selfSend
          frontendLowName
          ⟨1⟩
      ]
    }

    messageServers := [
      {
        name :=
          frontendLowName

        body := [
          .assign
            frontendMultiX
            (.intLiteral 0)
        ]

        priority :=
          some 4
      },
      {
        name :=
          frontendHighName

        body := [
          .selfSend
            frontendLowName
            ⟨2⟩
        ]

        priority :=
          some 1
      }
    ]
  }

  actor := {
    name :=
      ⟨"controller"⟩

    className :=
      ⟨"PriorityController"⟩
  }

theorem validRawMultiStoreModel_decodes :
    Frontend.decodeRawMultiStoreModel
        validRawMultiStoreModel =
      .ok
        expectedDecodedMultiStoreModel := by
  rfl

/--
Decoding retains source declaration order rather than silently sorting
the source AST.
-/
theorem multiStore_decoder_preserves_declaration_order :
    expectedDecodedMultiStoreModel.reactiveClass.messageServers.map
          (fun messageServer =>
            messageServer.name) = [
      frontendLowName,
      frontendHighName
    ] := by
  rfl

theorem multiStore_decoder_preserves_priorities :
    expectedDecodedMultiStoreModel.reactiveClass.messageServers.map
          (fun messageServer =>
            messageServer.priority) = [
      some 4,
      some 1
    ] := by
  rfl

/--
Translation, rather than decoding, derives the generated priority
order.
-/
theorem decoded_multiStore_translation_uses_priority_order :
    (Translation.translateMultiStoreCore
      expectedDecodedMultiStoreModel).reactor.logicalActions = [
      Translation.actionNameFor
        frontendHighName,

      Translation.actionNameFor
        frontendLowName
    ] := by
  rfl

/--
Cross-server self-sends are accepted when their target occurs anywhere
in the class declaration list.
-/
theorem declared_cross_server_send_decodes :
    Frontend.decodeMultiStoreStmt
        ["x"]
        ["low", "high"]
        {
          kind :=
            "selfSend"

          message? :=
            some "low"

          delay? :=
            some 3
        } =
      .ok
        (.selfSend
          frontendLowName
          ⟨3⟩) := by
  rfl

def undeclaredSendRawMultiStoreModel :
    Frontend.RawMultiStoreModel :=
  {
    validRawMultiStoreModel with

    constructorBody := [
      {
        kind :=
          "selfSend"

        message? :=
          some "missing"

        delay? :=
          some 1
      }
    ]
  }

theorem undeclared_multiStore_send_is_rejected :
    Frontend.decodeRawMultiStoreModel
        undeclaredSendRawMultiStoreModel =
      .error
        (.nameMismatch
          "self-send target"
          "low, high"
          "missing") := by
  rfl

def duplicateMessageServerRawModel :
    Frontend.RawMultiStoreModel :=
  {
    validRawMultiStoreModel with

    messageServers := [
      {
        name :=
          "low"

        priority? :=
          some 4

        body :=
          []
      },
      {
        name :=
          "low"

        priority? :=
          some 1

        body :=
          []
      }
    ]
  }

theorem duplicate_message_server_is_rejected :
    Frontend.decodeRawMultiStoreModel
        duplicateMessageServerRawModel =
      .error
        (.nameMismatch
          "messageServers.name"
          "unique message-server names"
          "low") := by
  rfl

def emptyMessageServersRawModel :
    Frontend.RawMultiStoreModel :=
  {
    validRawMultiStoreModel with

    messageServers :=
      []
  }

theorem empty_message_server_list_is_rejected :
    Frontend.decodeRawMultiStoreModel
        emptyMessageServersRawModel =
      .error
        (.missingField
          "messageServers") := by
  rfl

def invalidVersionRawMultiStoreModel :
    Frontend.RawMultiStoreModel :=
  {
    validRawMultiStoreModel with

    schemaVersion :=
      99
  }

theorem invalid_multiStore_schema_is_rejected :
    Frontend.decodeRawMultiStoreModel
        invalidVersionRawMultiStoreModel =
      .error
        (.invalidSchemaVersion
          99) := by
  rfl

end Tests
end Relico
