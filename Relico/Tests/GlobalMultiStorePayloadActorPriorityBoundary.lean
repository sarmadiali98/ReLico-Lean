import Relico.Correctness.GlobalMultiStorePayloadActorPriorityBoundary

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadActorPriorityBoundary

open Correctness.GlobalMultiStorePayloadActorPriorityBoundary

theorem sourceMetadata_absent
    (model : DTR.GlobalMultiStorePayloadModel) :
    sourceActorPriorityMetadata model = none :=
  sourceActorPriorityMetadata_eq_none model

theorem targetMetadata_absent
    (program : LF.GlobalMultiStorePayloadProgram) :
    targetActorPriorityMetadata program = none :=
  targetActorPriorityMetadata_eq_none program

theorem sourceTargetMetadata_correspond
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram) :
    ActorPriorityMetadataCorresponds model program :=
  actorPriorityMetadataCorresponds model program

theorem absentRequest_supported :
    RequestWithinSupportedFragment none :=
  noActorPriorityRequest_supported

theorem explicitRequest_rejected
    (assignment : ActorPriorityAssignment) :
    ¬RequestWithinSupportedFragment (some assignment) :=
  explicitActorPriorityRequest_rejected assignment

theorem emptyExplicitAssignment_rejected :
    ¬RequestWithinSupportedFragment
      (some ([] : ActorPriorityAssignment)) :=
  explicitActorPriorityRequest_rejected []

theorem boundary_characterization
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram)
    (request : ActorPriorityRequest) :
    Boundary model program request ↔
      request = none :=
  boundary_iff_request_absent
    model
    program
    request

theorem absentBoundary_supported
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram) :
    Boundary model program none :=
  boundary_without_actor_priority
    model
    program

theorem explicitBoundary_rejected
    (model : DTR.GlobalMultiStorePayloadModel)
    (program : LF.GlobalMultiStorePayloadProgram)
    (assignment : ActorPriorityAssignment) :
    ¬Boundary model program (some assignment) :=
  boundary_rejects_explicit_actor_priority
    model
    program
    assignment

theorem localPriority_preserved
    (server : DTR.MultiStorePayloadMessageServer) :
    (Translation.compileMultiStorePayloadReaction server).priority =
      server.priority :=
  localReactionPriority_preserved server

end GlobalMultiStorePayloadActorPriorityBoundary
end Tests
end Relico
