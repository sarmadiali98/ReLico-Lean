import Relico.Frontend.GlobalMultiStorePayloadDecoder
import Relico.Translation.GlobalMultiStorePayloadActorOrder

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadFrontend

open Frontend
open DTR.GlobalMultiStorePayloadActorPriority

private def frontendFailure
    {α : Type}
    (message : String) :
    IO α :=
  throw
    (IO.userError message)

private def ensure
    (condition : Bool)
    (message : String) :
    IO Unit :=
  if condition then
    pure ()
  else
    frontendFailure message

private def decodeGlobalOrFail
    (raw : RawGlobalMultiStorePayloadModel) :
    IO DecodedGlobalMultiStorePayloadModel :=
  match
    decodeRawGlobalMultiStorePayloadModel
      raw
  with

  | .ok decoded =>
      pure decoded

  | .error message =>
      frontendFailure
        ("global payload decode failed: " ++
          message)

def actorAName : ActorName :=
  ⟨"actora"⟩

def actorBName : ActorName :=
  ⟨"actorb"⟩

def rawLocalModel
    (className actorName actorClass : String)
    (localPriority : Option Nat) :
    RawMultiStorePayloadModel where

  schemaVersion :=
    multiStorePayloadBridgeSchemaVersion

  family :=
    multiStorePayloadBridgeFamily

  className :=
    className

  actorName :=
    actorName

  actorClass :=
    actorClass

  stateVariables :=
    [
      {
        name :=
          "x"

        initialValue :=
          0
      }
    ]

  constructorBody :=
    []

  messageServers :=
    [
      {
        name :=
          "tick"

        parameters :=
          []

        priority :=
          localPriority

        body :=
          []
      }
    ]

def rawActor
    (className actorName : String)
    (actorPriority localPriority : Option Nat) :
    RawGlobalMultiStorePayloadActor where

  priority :=
    actorPriority

  model :=
    rawLocalModel
      className
      actorName
      className
      localPriority

def rawGlobal
    (actors : List RawGlobalMultiStorePayloadActor) :
    RawGlobalMultiStorePayloadModel where

  schemaVersion :=
    globalMultiStorePayloadBridgeSchemaVersion

  family :=
    globalMultiStorePayloadBridgeFamily

  actors :=
    actors

def absentRaw :
    RawGlobalMultiStorePayloadModel :=
  rawGlobal
    [
      rawActor
        "ClassA"
        actorAName.value
        none
        (some 7),

      rawActor
        "ClassB"
        actorBName.value
        none
        (some 9)
    ]

def partialRaw :
    RawGlobalMultiStorePayloadModel :=
  rawGlobal
    [
      rawActor
        "ClassA"
        actorAName.value
        (some 1)
        (some 7),

      rawActor
        "ClassB"
        actorBName.value
        none
        (some 9)
    ]

def completeRaw :
    RawGlobalMultiStorePayloadModel :=
  rawGlobal
    [
      rawActor
        "ClassA"
        actorAName.value
        (some 2)
        (some 7),

      rawActor
        "ClassB"
        actorBName.value
        (some 1)
        (some 9)
    ]

def tiedRaw :
    RawGlobalMultiStorePayloadModel :=
  rawGlobal
    [
      rawActor
        "ClassA"
        actorAName.value
        (some 1)
        (some 7),

      rawActor
        "ClassB"
        actorBName.value
        (some 1)
        (some 9)
    ]

def readyPair :
    List ReadyActor :=
  [
    {
      actorName :=
        actorAName

      logicalTime :=
        0
    },
    {
      actorName :=
        actorBName

      logicalTime :=
        0
    }
  ]

private def checkLocalPriorityPreservation
    (decoded : DecodedGlobalMultiStorePayloadModel)
    (actorName : ActorName)
    (expectedPriority : Option Nat) :
    IO Unit :=
  match
    DTR.GlobalMultiStorePayloadModel.lookupActor
      decoded.model
      actorName
  with

  | none =>
      frontendFailure
        ("actor missing from decoded global model: " ++
          actorName.value)

  | some localModel =>
      match
        localModel.reactiveClass.messageServers
      with

      | [messageServer] =>
          ensure
            (messageServer.priority ==
              expectedPriority)
            ("local message-server priority changed for: " ++
              actorName.value)

      | _ =>
          frontendFailure
            "unexpected local message-server list"

private def checkDecodeFailure
    (label : String)
    (raw : RawGlobalMultiStorePayloadModel) :
    IO Unit :=
  match
    decodeRawGlobalMultiStorePayloadModel
      raw
  with

  | .error _ =>
      IO.println
        s!"PASS_INVALID_{label}"

  | .ok _ =>
      frontendFailure
        ("expected global decoding failure: " ++
          label)

def runGlobalMultiStorePayloadFrontendTests :
    IO UInt32 := do
  try
    ensure
      (globalMultiStorePayloadBridgeSchemaVersion ==
        4)
      "global schema version is not 4"

    let absent ←
      decodeGlobalOrFail
        absentRaw

    ensure
      (Store.keys absent.model.actors ==
        [actorAName, actorBName])
      "actor declaration order changed"

    ensure
      (Store.keys absent.model.topology ==
        [actorAName, actorBName])
      "actor/topology key order differs"

    ensure
      (absent.model.topology ==
        [
          (actorAName, []),
          (actorBName, [])
        ])
      "topology entries are not matching empty bindings"

    ensure
      absent.model.wellFormed
      "decoded global model is not well formed"

    ensure
      (absent.actorPriorityRequest ==
        none)
      "all-absent actor priorities did not decode to none"

    checkLocalPriorityPreservation
      absent
      actorAName
      (some 7)

    checkLocalPriorityPreservation
      absent
      actorBName
      (some 9)

    let partialDecoded ←
      decodeGlobalOrFail
        partialRaw

    ensure
      (partialDecoded.actorPriorityRequest ==
        some
          [
            (actorAName, 1)
          ])
      "partial actor-priority assignment was not preserved"

    ensure
      (eligibleActorNames
          partialDecoded.actorPriorityRequest
          readyPair ==
        [actorAName, actorBName])
      "incomplete actor-priority request filtered an actor"

    let complete ←
      decodeGlobalOrFail
        completeRaw

    ensure
      (complete.actorPriorityRequest ==
        some
          [
            (actorAName, 2),
            (actorBName, 1)
          ])
      "complete actor-priority request changed"

    ensure
      (eligibleActorNames
          complete.actorPriorityRequest
          readyPair ==
        [actorBName])
      "lower natural actor priority was not stronger"

    ensure
      (Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest
          complete.actorPriorityRequest ==
        complete.actorPriorityRequest)
      "actor-priority request compilation changed the request"

    let tied ←
      decodeGlobalOrFail
        tiedRaw

    ensure
      (eligibleActorNames
          tied.actorPriorityRequest
          readyPair ==
        [actorAName, actorBName])
      "equal actor priorities introduced tie-breaking"

    let duplicateRaw :=
      rawGlobal
        [
          rawActor
            "ClassA"
            actorAName.value
            none
            (some 7),

          rawActor
            "ClassB"
            actorAName.value
            none
            (some 9)
        ]

    checkDecodeFailure
      "DUPLICATE_ACTOR_NAME"
      duplicateRaw

    let unknownClassRaw :=
      rawGlobal
        [
          {
            priority :=
              none

            model :=
              rawLocalModel
                "ClassA"
                actorAName.value
                "MissingClass"
                (some 7)
          }
        ]

    checkDecodeFailure
      "UNKNOWN_REACTIVE_CLASS"
      unknownClassRaw

    match
      decodeRawMultiStorePayloadModel
        (rawLocalModel
          "LegacyClass"
          "legacy"
          "LegacyClass"
          (some 5))
    with

    | .error message =>
        frontendFailure
          ("unchanged v1 decoder failed: " ++
            message)

    | .ok legacy =>
        ensure
          (legacy.actor.name.value ==
            "legacy")
          "version-1 actor behavior changed"

        match
          legacy.reactiveClass.messageServers
        with

        | [messageServer] =>
            ensure
              (messageServer.priority ==
                some 5)
              "version-1 local priority behavior changed"

        | _ =>
            frontendFailure
              "version-1 message-server list changed"

    let roundTripText :=
      (Lean.toJson completeRaw).compress

    let roundTrip ←
      match
        decodeGlobalMultiStorePayloadModelText
          roundTripText
      with

      | .ok decoded =>
          pure decoded

      | .error message =>
          frontendFailure
            ("version-4 JSON round trip failed: " ++
              message)

    ensure
      (roundTrip == complete)
      "version-4 JSON round trip changed the decoded result"

    let negativePriorityText :=
      "{" ++
      "\"schemaVersion\":4," ++
      "\"family\":\"globalMultiStorePayload\"," ++
      "\"actors\":[{" ++
      "\"priority\":-1," ++
      "\"model\":{" ++
      "\"schemaVersion\":1," ++
      "\"family\":\"multiStorePayload\"," ++
      "\"className\":\"ClassA\"," ++
      "\"actorName\":\"actora\"," ++
      "\"actorClass\":\"ClassA\"," ++
      "\"stateVariables\":[{" ++
      "\"name\":\"x\"," ++
      "\"initialValue\":0}]," ++
      "\"constructorBody\":[]," ++
      "\"messageServers\":[{" ++
      "\"name\":\"tick\"," ++
      "\"parameters\":[]," ++
      "\"priority\":7," ++
      "\"body\":[]}]}}]}"

    match
      decodeGlobalMultiStorePayloadModelText
        negativePriorityText
    with

    | .error _ =>
        IO.println
          "PASS_INVALID_NEGATIVE_ACTOR_PRIORITY"

    | .ok _ =>
        frontendFailure
          "negative actor priority was accepted"

    IO.println
      "GLOBAL_MULTI_STORE_PAYLOAD_FRONTEND_TESTS_OK"

    pure 0

  catch exception =>
    IO.eprintln
      s!"global multi-store-payload frontend tests failed: {exception}"

    pure 1

end GlobalMultiStorePayloadFrontend
end Tests
end Relico

def main : IO UInt32 :=
  Relico.Tests.GlobalMultiStorePayloadFrontend.runGlobalMultiStorePayloadFrontendTests
