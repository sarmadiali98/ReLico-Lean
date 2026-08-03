import Relico.DTR.GlobalMultiStorePayload
import Relico.DTR.GlobalMultiStorePayloadActorPriority
import Relico.Frontend.GlobalMultiStorePayloadSchema
import Relico.Frontend.MultiStorePayloadDecoder

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/--
The additive global decoder returns the global model and actor-priority request
as separate values. No literal actor-priority field is added to the model.
-/
structure DecodedGlobalMultiStorePayloadModel where
  model :
    DTR.GlobalMultiStorePayloadModel

  actorPriorityRequest :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest

deriving Repr, DecidableEq, BEq, Inhabited

private def requireGlobalPayloadMatchingName
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

private def firstDuplicateGlobalPayloadActorName? :
    List ActorName →
    Option ActorName

  | [] =>
      none

  | actorName :: remaining =>
      if remaining.contains actorName then
        some actorName
      else
        firstDuplicateGlobalPayloadActorName?
          remaining

private def requireUniqueGlobalPayloadActorNames
    (actorNames : List ActorName) :
    Except String Unit :=
  match
    firstDuplicateGlobalPayloadActorName?
      actorNames
  with

  | none =>
      .ok ()

  | some duplicate =>
      .error
        ("duplicate actor name: `" ++
          duplicate.value ++ "`")

/--
Collect exactly the explicit actor-priority assignments in declaration order.
-/
def decodeActorPriorityAssignment :
    List RawGlobalMultiStorePayloadActor →
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment

  | [] =>
      []

  | actor :: remaining =>
      match actor.priority with

      | none =>
          decodeActorPriorityAssignment
            remaining

      | some priority =>
          (
            ⟨actor.model.actorName⟩,
            priority
          ) ::
            decodeActorPriorityAssignment
              remaining

/--
Decode actor-level priority independently from local message-server priority.

All priorities absent becomes `none`. Otherwise the request contains exactly
the explicitly prioritized actors, preserving declaration order. Partial
requests remain partial; the existing actor-priority semantics therefore impose
no filtering until the simultaneous-ready cohort is fully covered.
-/
def decodeActorPriorityRequest
    (actors : List RawGlobalMultiStorePayloadActor) :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest :=
  let assignment :=
    decodeActorPriorityAssignment
      actors

  if assignment.isEmpty then
    none
  else
    some assignment

/--
Validate and decode additive schema version 4.

Each actor entry is decoded through the unchanged version-1 local decoder.
The global actor store and topology retain declaration order, and every actor
receives a matching empty known-rebec binding store in this additive phase.
-/
def decodeRawGlobalMultiStorePayloadModel
    (raw : RawGlobalMultiStorePayloadModel) :
    Except String
      DecodedGlobalMultiStorePayloadModel := do

  if
    raw.schemaVersion ==
      globalMultiStorePayloadBridgeSchemaVersion
  then
    pure ()
  else
    throw
      ("unsupported global payload schema version: " ++
        toString raw.schemaVersion)

  requireGlobalPayloadMatchingName
    "family"
    globalMultiStorePayloadBridgeFamily
    raw.family

  if raw.actors.isEmpty then
    throw
      "actors must not be empty"
  else
    pure ()

  let decodedActors ←
    raw.actors.mapM
      (fun rawActor => do
        let localModel ←
          decodeRawMultiStorePayloadModel
            rawActor.model

        pure
          (
            rawActor,
            localModel
          ))

  let actorNames :=
    decodedActors.map
      (fun actorEntry =>
        actorEntry.2.actor.name)

  requireUniqueGlobalPayloadActorNames
    actorNames

  let actors :
      DTR.GlobalMultiStorePayloadActors :=
    decodedActors.map
      (fun actorEntry =>
        (
          actorEntry.2.actor.name,
          actorEntry.2
        ))

  let topology :
      ActorTopology :=
    decodedActors.map
      (fun actorEntry =>
        (
          actorEntry.2.actor.name,
          ([] : KnownRebecBindings)
        ))

  let model :
      DTR.GlobalMultiStorePayloadModel :=
    {
      actors :=
        actors

      topology :=
        topology
    }

  if model.wellFormed then
    pure ()
  else
    throw
      "decoded global payload model is not well formed"

  pure {
    model :=
      model

    actorPriorityRequest :=
      decodeActorPriorityRequest
        raw.actors
  }

/--
Parse JSON text and decode it into a global model plus a separate
actor-priority request.
-/
def decodeGlobalMultiStorePayloadModelText
    (text : String) :
    Except String
      DecodedGlobalMultiStorePayloadModel := do

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
          RawGlobalMultiStorePayloadModel)
    with

    | .ok value =>
        .ok value

    | .error message =>
        .error
          ("global payload schema decode failed: " ++
            message)

  decodeRawGlobalMultiStorePayloadModel
    raw

end Frontend
end Relico
