import Relico.LF.GlobalMultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace LF
namespace GlobalMultiStorePayloadActorOrder

/--
Compiled target actor ordering.

Lower natural numbers denote stronger ordering precedence.
-/
abbrev ActorOrderAssignment :=
  List (ActorName × Nat)

/--
No request means that target actor ordering imposes no additional filtering.
-/
abbrev ActorOrderRequest :=
  Option ActorOrderAssignment

/--
One target actor ready to participate in global LF selection.
-/
structure ReadyTargetActor where
  actorName : ActorName
  logicalTime : Nat
deriving Repr, DecidableEq

/--
Return the first compiled ordering value associated with an actor.
-/
def lookupActorOrder :
    ActorOrderAssignment →
    ActorName →
    Option Nat

  | [], _ =>
      none

  | (candidate, order) :: rest, actorName =>
      if candidate = actorName then
        some order
      else
        lookupActorOrder rest actorName

/--
Return the first ready target-actor record for a nominal actor name.
-/
def lookupReadyTargetActor :
    List ReadyTargetActor →
    ActorName →
    Option ReadyTargetActor

  | [], _ =>
      none

  | candidate :: rest, actorName =>
      if candidate.actorName = actorName then
        some candidate
      else
        lookupReadyTargetActor rest actorName

/--
Two ready target actors are simultaneous when their logical times agree.
-/
def targetActorsSimultaneous
    (left right : ReadyTargetActor) :
    Bool :=
  decide (
    left.logicalTime =
      right.logicalTime
  )

/--
A target actor is temporally eligible when no ready target actor is earlier.
-/
def targetEarliestReady
    (ready : List ReadyTargetActor)
    (selected : ReadyTargetActor) :
    Bool :=
  ready.all fun candidate =>
    decide (
      selected.logicalTime ≤
        candidate.logicalTime
    )

/--
The complete simultaneous target cohort of the selected actor.
-/
def sameTimeReadyTargetActors
    (ready : List ReadyTargetActor)
    (selected : ReadyTargetActor) :
    List ReadyTargetActor :=
  ready.filter fun candidate =>
    targetActorsSimultaneous
      selected
      candidate

/--
An ordering assignment covers a simultaneous cohort when every actor in that
cohort has a compiled ordering value.
-/
def targetOrderCoversReadyActors
    (assignment : ActorOrderAssignment)
    (ready : List ReadyTargetActor)
    (selected : ReadyTargetActor) :
    Bool :=
  (
    sameTimeReadyTargetActors
      ready
      selected
  ).all fun candidate =>
    (
      lookupActorOrder
        assignment
        candidate.actorName
    ).isSome

/--
The selected target actor has minimal numeric order in its simultaneous cohort.
-/
def selectedHasMinimalActorOrder
    (assignment : ActorOrderAssignment)
    (ready : List ReadyTargetActor)
    (selected : ReadyTargetActor) :
    Bool :=
  match
    lookupActorOrder
      assignment
      selected.actorName
  with

  | none =>
      false

  | some selectedOrder =>
      (
        sameTimeReadyTargetActors
          ready
          selected
      ).all fun candidate =>
        match
          lookupActorOrder
            assignment
            candidate.actorName
        with

        | none =>
            false

        | some candidateOrder =>
            decide (
              selectedOrder ≤
                candidateOrder
            )

/--
Executable target actor-order eligibility.

Logical time is applied before the compiled actor ordering. Ordering compares
only actors in the selected actor's simultaneous-ready cohort.

Absent and incomplete ordering metadata impose no additional filtering.
-/
def targetActorOrderEligibleBool
    (request : ActorOrderRequest)
    (ready : List ReadyTargetActor)
    (actorName : ActorName) :
    Bool :=
  match
    lookupReadyTargetActor
      ready
      actorName
  with

  | none =>
      false

  | some selected =>
      targetEarliestReady ready selected &&
        (
          match request with

          | none =>
              true

          | some assignment =>
              if
                targetOrderCoversReadyActors
                  assignment
                  ready
                  selected
              then
                selectedHasMinimalActorOrder
                  assignment
                  ready
                  selected
              else
                true
        )

/--
Propositional target actor-order eligibility.
-/
def TargetActorOrderEligible
    (request : ActorOrderRequest)
    (ready : List ReadyTargetActor)
    (actorName : ActorName) :
    Prop :=
  targetActorOrderEligibleBool
      request
      ready
      actorName =
    true

/--
Target actor-order eligibility is decidable through its executable Boolean
definition.
-/
instance instDecidableTargetActorOrderEligible
    (request : ActorOrderRequest)
    (ready : List ReadyTargetActor)
    (actorName : ActorName) :
    Decidable (
      TargetActorOrderEligible
        request
        ready
        actorName
    ) := by

  unfold TargetActorOrderEligible
  infer_instance

/--
All eligible target actor names, preserving ready-list order.
-/
def eligibleTargetActorNames
    (request : ActorOrderRequest)
    (ready : List ReadyTargetActor) :
    List ActorName :=
  List.map
    (fun candidate =>
      candidate.actorName)
    (
      List.filter
        (fun candidate =>
          targetActorOrderEligibleBool
            request
            ready
            candidate.actorName)
        ready
    )

/--
Actor-order-constrained LF dispatch.

The eligibility premise constrains actor selection. The existing
`GlobalMultiStorePayloadDispatch.Step` remains responsible for the actual
chosen-actor target transition.
-/
inductive ActorOrderDispatchStep
    (request : ActorOrderRequest)
    (ready : List ReadyTargetActor)
    (program :
      LF.GlobalMultiStorePayloadProgram)
    (actorName : ActorName) :
    LF.GlobalMultiStorePayloadState →
    LF.PendingAction →
    LF.MultiStorePayloadReaction →
    LF.GlobalMultiStorePayloadState →
    Prop where

  | lift
      {before after :
        LF.GlobalMultiStorePayloadState}
      {selectedAction :
        LF.PendingAction}
      {selectedReaction :
        LF.MultiStorePayloadReaction}
      (hEligible :
        TargetActorOrderEligible
          request
          ready
          actorName)
      (hDispatch :
        LF.GlobalMultiStorePayloadDispatch.Step
          program
          actorName
          before
          selectedAction
          selectedReaction
          after) :

      ActorOrderDispatchStep
        request
        ready
        program
        actorName
        before
        selectedAction
        selectedReaction
        after

/--
Every constrained target step exposes its actor-order eligibility premise.
-/
theorem ActorOrderDispatchStep.eligible
    {request : ActorOrderRequest}
    {ready : List ReadyTargetActor}
    {program :
      LF.GlobalMultiStorePayloadProgram}
    {actorName : ActorName}
    {before after :
      LF.GlobalMultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hStep :
      ActorOrderDispatchStep
        request
        ready
        program
        actorName
        before
        selectedAction
        selectedReaction
        after) :
    TargetActorOrderEligible
      request
      ready
      actorName := by

  cases hStep with

  | lift hEligible hDispatch =>
      exact hEligible

/--
Every constrained target step exposes the unchanged existing LF dispatch.
-/
theorem ActorOrderDispatchStep.dispatch
    {request : ActorOrderRequest}
    {ready : List ReadyTargetActor}
    {program :
      LF.GlobalMultiStorePayloadProgram}
    {actorName : ActorName}
    {before after :
      LF.GlobalMultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hStep :
      ActorOrderDispatchStep
        request
        ready
        program
        actorName
        before
        selectedAction
        selectedReaction
        after) :
    LF.GlobalMultiStorePayloadDispatch.Step
      program
      actorName
      before
      selectedAction
      selectedReaction
      after := by

  cases hStep with

  | lift hEligible hDispatch =>
      exact hDispatch

end GlobalMultiStorePayloadActorOrder
end LF
end Relico
