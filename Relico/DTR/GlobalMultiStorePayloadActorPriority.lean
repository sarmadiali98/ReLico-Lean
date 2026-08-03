import Relico.DTR.GlobalMultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace DTR
namespace GlobalMultiStorePayloadActorPriority

/--
Actor-level priorities. Lower natural numbers denote higher priority.
-/
abbrev ActorPriorityAssignment :=
  List (ActorName × Nat)

/--
No request means that actor priority imposes no additional filtering.
-/
abbrev ActorPriorityRequest :=
  Option ActorPriorityAssignment

/--
One actor that is ready to participate in global selection.
-/
structure ReadyActor where
  actorName : ActorName
  logicalTime : Nat
deriving Repr, DecidableEq

/--
Return the first priority assigned to an actor.
-/
def lookupPriority :
    ActorPriorityAssignment →
    ActorName →
    Option Nat

  | [], _ =>
      none

  | (candidate, priority) :: rest, actorName =>
      if candidate = actorName then
        some priority
      else
        lookupPriority rest actorName

/--
Return the first ready record for an actor.
-/
def lookupReadyActor :
    List ReadyActor →
    ActorName →
    Option ReadyActor

  | [], _ =>
      none

  | candidate :: rest, actorName =>
      if candidate.actorName = actorName then
        some candidate
      else
        lookupReadyActor rest actorName

/--
Two ready actors are simultaneous exactly when their logical times agree.
-/
def simultaneouslyReady
    (left right : ReadyActor) :
    Bool :=
  decide (
    left.logicalTime =
      right.logicalTime
  )

/--
A selected actor is earliest when no ready actor has a smaller logical time.
-/
def earliestReady
    (ready : List ReadyActor)
    (selected : ReadyActor) :
    Bool :=
  ready.all fun candidate =>
    decide (
      selected.logicalTime ≤
        candidate.logicalTime
    )

/--
The actors that compete simultaneously with the selected actor.
-/
def sameTimeReadyActors
    (ready : List ReadyActor)
    (selected : ReadyActor) :
    List ReadyActor :=
  ready.filter fun candidate =>
    simultaneouslyReady
      selected
      candidate

/--
A priority assignment covers the complete simultaneous-ready cohort.
-/
def requestCoversReadyActors
    (assignment : ActorPriorityAssignment)
    (ready : List ReadyActor)
    (selected : ReadyActor) :
    Bool :=
  (
    sameTimeReadyActors
      ready
      selected
  ).all fun candidate =>
    (
      lookupPriority
        assignment
        candidate.actorName
    ).isSome

/--
The selected actor has minimal numeric priority in its simultaneous cohort.
-/
def selectedHasMinimalPriority
    (assignment : ActorPriorityAssignment)
    (ready : List ReadyActor)
    (selected : ReadyActor) :
    Bool :=
  match
    lookupPriority
      assignment
      selected.actorName
  with

  | none =>
      false

  | some selectedPriority =>
      (
        sameTimeReadyActors
          ready
          selected
      ).all fun candidate =>
        match
          lookupPriority
            assignment
            candidate.actorName
        with

        | none =>
            false

        | some candidatePriority =>
            decide (
              selectedPriority ≤
                candidatePriority
            )

/--
Executable global actor eligibility.

Logical time is considered before actor priority. Actor priority compares only
actors in the same simultaneous-ready cohort.

Absent and incomplete requests impose no priority filtering.
-/
def actorPriorityEligibleBool
    (request : ActorPriorityRequest)
    (ready : List ReadyActor)
    (actorName : ActorName) :
    Bool :=
  match
    lookupReadyActor
      ready
      actorName
  with

  | none =>
      false

  | some selected =>
      earliestReady ready selected &&
        (
          match request with

          | none =>
              true

          | some assignment =>
              if
                requestCoversReadyActors
                  assignment
                  ready
                  selected
              then
                selectedHasMinimalPriority
                  assignment
                  ready
                  selected
              else
                true
        )

/--
Propositional form of executable actor eligibility.
-/
def ActorPriorityEligible
    (request : ActorPriorityRequest)
    (ready : List ReadyActor)
    (actorName : ActorName) :
    Prop :=
  actorPriorityEligibleBool
      request
      ready
      actorName =
    true

/--
Actor eligibility is decidable because it is defined by executable Boolean
selection semantics.
-/
instance instDecidableActorPriorityEligible
    (request : ActorPriorityRequest)
    (ready : List ReadyActor)
    (actorName : ActorName) :
    Decidable (
      ActorPriorityEligible
        request
        ready
        actorName
    ) := by

  unfold ActorPriorityEligible
  infer_instance

/--
All eligible actor names, preserving ready-list order.
-/
def eligibleActorNames
    (request : ActorPriorityRequest)
    (ready : List ReadyActor) :
    List ActorName :=
  List.map
    (fun candidate =>
      candidate.actorName)
    (
      List.filter
        (fun candidate =>
          actorPriorityEligibleBool
            request
            ready
            candidate.actorName)
        ready
    )

/--
Actor-priority-constrained global dispatch.

The eligibility premise constrains actor selection. The existing
`GlobalMultiStorePayloadDispatch.Step` performs the actual state transition.
-/
inductive ActorPriorityDispatchStep
    (request : ActorPriorityRequest)
    (ready : List ReadyActor)
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (actorName : ActorName) :
    DTR.GlobalMultiStorePayloadState →
    DTR.PendingMessage →
    DTR.MultiStorePayloadMessageServer →
    DTR.GlobalMultiStorePayloadState →
    Prop where

  | lift
      {before after :
        DTR.GlobalMultiStorePayloadState}
      {selectedMessage :
        DTR.PendingMessage}
      {selectedServer :
        DTR.MultiStorePayloadMessageServer}
      (hEligible :
        ActorPriorityEligible
          request
          ready
          actorName)
      (hDispatch :
        DTR.GlobalMultiStorePayloadDispatch.Step
          model
          actorName
          before
          selectedMessage
          selectedServer
          after) :

      ActorPriorityDispatchStep
        request
        ready
        model
        actorName
        before
        selectedMessage
        selectedServer
        after

theorem ActorPriorityDispatchStep.eligible
    {request : ActorPriorityRequest}
    {ready : List ReadyActor}
    {model :
      DTR.GlobalMultiStorePayloadModel}
    {actorName : ActorName}
    {before after :
      DTR.GlobalMultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hStep :
      ActorPriorityDispatchStep
        request
        ready
        model
        actorName
        before
        selectedMessage
        selectedServer
        after) :
    ActorPriorityEligible
      request
      ready
      actorName := by

  cases hStep with

  | lift hEligible hDispatch =>
      exact hEligible

theorem ActorPriorityDispatchStep.dispatch
    {request : ActorPriorityRequest}
    {ready : List ReadyActor}
    {model :
      DTR.GlobalMultiStorePayloadModel}
    {actorName : ActorName}
    {before after :
      DTR.GlobalMultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hStep :
      ActorPriorityDispatchStep
        request
        ready
        model
        actorName
        before
        selectedMessage
        selectedServer
        after) :
    DTR.GlobalMultiStorePayloadDispatch.Step
      model
      actorName
      before
      selectedMessage
      selectedServer
      after := by

  cases hStep with

  | lift hEligible hDispatch =>
      exact hDispatch

end GlobalMultiStorePayloadActorPriority
end DTR
end Relico
