import Relico.DTR.GlobalMultiStorePayloadActorPriority
import Relico.LF.GlobalMultiStorePayloadActorOrder

set_option autoImplicit false

namespace Relico
namespace Translation
namespace GlobalMultiStorePayloadActorOrder

/--
Compile source actor-priority assignments into target actor-order assignments.

Actor names and numeric values are preserved exactly.
-/
def compileActorPriorityAssignment :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment →
    LF.GlobalMultiStorePayloadActorOrder.ActorOrderAssignment

  | [] =>
      []

  | (actorName, priority) :: rest =>
      (actorName, priority) ::
        compileActorPriorityAssignment rest

/--
Compile an optional source priority request.

`none` remains `none`. Present assignments remain present, including empty and
incomplete assignments.
-/
def compileActorPriorityRequest :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest →
    LF.GlobalMultiStorePayloadActorOrder.ActorOrderRequest

  | none =>
      none

  | some assignment =>
      some (
        compileActorPriorityAssignment
          assignment
      )

/--
Compile one ready source actor into one ready target actor.
-/
def compileReadyActor
    (ready :
      DTR.GlobalMultiStorePayloadActorPriority.ReadyActor) :
    LF.GlobalMultiStorePayloadActorOrder.ReadyTargetActor :=
  {
    actorName :=
      ready.actorName

    logicalTime :=
      ready.logicalTime
  }

/--
Compile the complete ready-actor list without reordering or dropping entries.
-/
def compileReadyActors :
    List
      DTR.GlobalMultiStorePayloadActorPriority.ReadyActor →
    List
      LF.GlobalMultiStorePayloadActorOrder.ReadyTargetActor

  | [] =>
      []

  | ready :: rest =>
      compileReadyActor ready ::
        compileReadyActors rest

@[simp]
theorem compileActorPriorityAssignment_nil :
    compileActorPriorityAssignment [] =
      [] :=
  rfl

@[simp]
theorem compileActorPriorityAssignment_cons
    (actorName : ActorName)
    (priority : Nat)
    (rest :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment) :
    compileActorPriorityAssignment
        ((actorName, priority) :: rest) =
      (actorName, priority) ::
        compileActorPriorityAssignment rest :=
  rfl

/--
Assignment compilation is extensionally the identity over the shared nominal
actor and numeric-order representation.
-/
theorem compileActorPriorityAssignment_eq
    (assignment :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment) :
    compileActorPriorityAssignment assignment =
      assignment := by

  induction assignment with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      rcases head with
        ⟨actorName, priority⟩

      simp [
        compileActorPriorityAssignment,
        inductionHypothesis
      ]

theorem compileActorPriorityAssignment_length
    (assignment :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment) :
    (
      compileActorPriorityAssignment
        assignment
    ).length =
      assignment.length := by

  induction assignment with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      rcases head with
        ⟨actorName, priority⟩

      simp [
        compileActorPriorityAssignment,
        inductionHypothesis
      ]

@[simp]
theorem compileActorPriorityRequest_none :
    compileActorPriorityRequest none =
      none :=
  rfl

@[simp]
theorem compileActorPriorityRequest_some
    (assignment :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment) :
    compileActorPriorityRequest
        (some assignment) =
      some (
        compileActorPriorityAssignment
          assignment
      ) :=
  rfl

/--
Request compilation preserves the complete optional assignment value.
-/
theorem compileActorPriorityRequest_eq
    (request :
      DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest) :
    compileActorPriorityRequest request =
      request := by

  cases request with

  | none =>
      rfl

  | some assignment =>
      simp [
        compileActorPriorityRequest,
        compileActorPriorityAssignment_eq
      ]

@[simp]
theorem compileReadyActor_actorName
    (ready :
      DTR.GlobalMultiStorePayloadActorPriority.ReadyActor) :
    (
      compileReadyActor ready
    ).actorName =
      ready.actorName :=
  rfl

@[simp]
theorem compileReadyActor_logicalTime
    (ready :
      DTR.GlobalMultiStorePayloadActorPriority.ReadyActor) :
    (
      compileReadyActor ready
    ).logicalTime =
      ready.logicalTime :=
  rfl

@[simp]
theorem compileReadyActors_nil :
    compileReadyActors [] =
      [] :=
  rfl

@[simp]
theorem compileReadyActors_cons
    (ready :
      DTR.GlobalMultiStorePayloadActorPriority.ReadyActor)
    (rest :
      List
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor) :
    compileReadyActors
        (ready :: rest) =
      compileReadyActor ready ::
        compileReadyActors rest :=
  rfl

theorem compileReadyActors_length
    (ready :
      List
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor) :
    (
      compileReadyActors ready
    ).length =
      ready.length := by

  induction ready with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      simp [
        compileReadyActors,
        inductionHypothesis
      ]

/--
Compilation preserves the ready-list sequence of nominal actor names.
-/
theorem compileReadyActors_actorNames
    (ready :
      List
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor) :
    List.map
        (
          fun candidate :
            LF.GlobalMultiStorePayloadActorOrder.ReadyTargetActor =>
              candidate.actorName
        )
        (compileReadyActors ready) =
      List.map
        (
          fun candidate :
            DTR.GlobalMultiStorePayloadActorPriority.ReadyActor =>
              candidate.actorName
        )
        ready := by

  induction ready with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      simp [
        compileReadyActors,
        compileReadyActor,
        inductionHypothesis
      ]

/--
Compilation preserves the ready-list sequence of logical times.
-/
theorem compileReadyActors_logicalTimes
    (ready :
      List
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor) :
    List.map
        (
          fun candidate :
            LF.GlobalMultiStorePayloadActorOrder.ReadyTargetActor =>
              candidate.logicalTime
        )
        (compileReadyActors ready) =
      List.map
        (
          fun candidate :
            DTR.GlobalMultiStorePayloadActorPriority.ReadyActor =>
              candidate.logicalTime
        )
        ready := by

  induction ready with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      simp [
        compileReadyActors,
        compileReadyActor,
        inductionHypothesis
      ]

end GlobalMultiStorePayloadActorOrder
end Translation
end Relico
