import Relico.LF.GlobalMultiStorePayload
import Relico.Correctness.GlobalMultiStorePayloadDeclaredFragment

namespace Relico
namespace Correctness
namespace GlobalMultiStorePayloadActorPriorityBoundary

/--
An actor-priority assignment supplied outside the published source and
target ASTs.
-/
abbrev ActorPriorityAssignment :=
  List (ActorName × Nat)

/--
`none` requests no actor-level priority policy.

A `some` value requests actor-priority metadata that is not represented by
the published global source or target AST.
-/
abbrev ActorPriorityRequest :=
  Option ActorPriorityAssignment

/--
The source global model exposes no actor-priority metadata.
-/
def sourceActorPriorityMetadata
    (_model : DTR.GlobalMultiStorePayloadModel) :
    ActorPriorityRequest :=
  none

/--
The target global program exposes no actor-priority metadata.
-/
def targetActorPriorityMetadata
    (_program : LF.GlobalMultiStorePayloadProgram) :
    ActorPriorityRequest :=
  none

@[simp]
theorem sourceActorPriorityMetadata_eq_none
    (model : DTR.GlobalMultiStorePayloadModel) :
    sourceActorPriorityMetadata model = none := by
  rfl

@[simp]
theorem targetActorPriorityMetadata_eq_none
    (program : LF.GlobalMultiStorePayloadProgram) :
    targetActorPriorityMetadata program = none := by
  rfl

/--
The source and target actor-priority projections agree because both are
absent.
-/
def ActorPriorityMetadataCorresponds
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram) :
    Prop :=
  sourceActorPriorityMetadata model =
    targetActorPriorityMetadata program

theorem actorPriorityMetadataCorresponds
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram) :
    ActorPriorityMetadataCorresponds model program := by
  rfl

/--
The supported fragment accepts exactly the absence of an external
actor-priority request.
-/
def RequestWithinSupportedFragment
    (request : ActorPriorityRequest) :
    Prop :=
  request = none

theorem noActorPriorityRequest_supported :
    RequestWithinSupportedFragment none := by
  rfl

theorem explicitActorPriorityRequest_rejected
    (assignment : ActorPriorityAssignment) :
    ¬RequestWithinSupportedFragment (some assignment) := by
  simp [
    RequestWithinSupportedFragment,
  ]

/--
The E4B actor-priority boundary combines metadata agreement with rejection
of any external actor-priority assignment.
-/
def Boundary
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram)
    (request : ActorPriorityRequest) :
    Prop :=
  ActorPriorityMetadataCorresponds model program ∧
    RequestWithinSupportedFragment request

theorem boundary_iff_request_absent
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram)
    (request : ActorPriorityRequest) :
    Boundary model program request ↔
      request = none := by
  simp [
    Boundary,
    ActorPriorityMetadataCorresponds,
    RequestWithinSupportedFragment,
    sourceActorPriorityMetadata,
    targetActorPriorityMetadata,
  ]

theorem boundary_without_actor_priority
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram) :
    Boundary model program none := by
  exact
    (boundary_iff_request_absent
      model
      program
      none).2 rfl

theorem boundary_rejects_explicit_actor_priority
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram)
    (assignment : ActorPriorityAssignment) :
    ¬Boundary model program (some assignment) := by
  rw [
    boundary_iff_request_absent,
  ]

  simp

/--
Local message-server priority remains represented and is preserved by
translation. It is not reinterpreted as actor-level scheduling priority.
-/
theorem localReactionPriority_preserved
    (server : DTR.MultiStorePayloadMessageServer) :
    (Translation.compileMultiStorePayloadReaction server).priority =
      server.priority :=
  GlobalMultiStorePayloadDeclaredFragment.compileReaction_priority
    server

end GlobalMultiStorePayloadActorPriorityBoundary
end Correctness
end Relico
