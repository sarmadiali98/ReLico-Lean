import Relico.Correctness.GlobalMultiStorePayloadActorPriorityBoundary

namespace Relico.Investigation.ActorPriority

abbrev ActorName := String

abbrev ActorPriority := Nat

abbrev ActorPriorityAssignment :=
  List (ActorName × ActorPriority)

abbrev ActorPriorityRequest :=
  Option ActorPriorityAssignment

structure ReadyActor where
  actor : ActorName
  logicalTime : Nat
deriving DecidableEq, BEq, Repr

def lookupPriorityInAssignment :
    ActorPriorityAssignment →
    ActorName →
    Option ActorPriority
  | [], _ =>
      none
  | entry :: remaining, actor =>
      if entry.1 == actor then
        some entry.2
      else
        lookupPriorityInAssignment remaining actor

def lookupPriority
    (request : ActorPriorityRequest)
    (actor : ActorName) :
    Option ActorPriority :=
  match request with
  | none =>
      none
  | some assignment =>
      lookupPriorityInAssignment assignment actor

def requestCovers
    (request : ActorPriorityRequest)
    (ready : List ReadyActor) :
    Bool :=
  match request with
  | none =>
      true
  | some _ =>
      ready.all fun candidate =>
        (lookupPriority request candidate.actor).isSome

def sourceStrictlyPrecedes
    (request : ActorPriorityRequest)
    (left right : ReadyActor) :
    Bool :=
  match
    lookupPriority request left.actor,
    lookupPriority request right.actor
  with
  | some leftPriority, some rightPriority =>
      decide (leftPriority < rightPriority)
  | _, _ =>
      false

def sourceEligible
    (request : ActorPriorityRequest)
    (candidate : ReadyActor)
    (ready : List ReadyActor) :
    Bool :=
  ready.contains candidate &&
    ready.all fun other =>
      !(sourceStrictlyPrecedes request other candidate)

def sourceEligibleActors
    (request : ActorPriorityRequest)
    (ready : List ReadyActor) :
    List ReadyActor :=
  ready.filter fun candidate =>
    sourceEligible request candidate ready

def sourceEligibleActorNames
    (request : ActorPriorityRequest)
    (ready : List ReadyActor) :
    List ActorName :=
  (sourceEligibleActors request ready).map
    ReadyActor.actor

def simultaneous
    (ready : List ReadyActor) :
    Bool :=
  match ready with
  | [] =>
      true
  | first :: remaining =>
      remaining.all fun candidate =>
        candidate.logicalTime == first.logicalTime

def prioritySelectionEnabled
    (request : ActorPriorityRequest)
    (ready : List ReadyActor) :
    Bool :=
  request.isSome &&
    requestCovers request ready &&
    simultaneous ready

end Relico.Investigation.ActorPriority
