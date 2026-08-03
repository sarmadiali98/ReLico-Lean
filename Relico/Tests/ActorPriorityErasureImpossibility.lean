import Relico.Investigation.ActorPriority.ErasureImpossibility

set_option autoImplicit false

namespace Relico.Tests.ActorPriorityErasureImpossibility

open Relico.Investigation.ActorPriority

def workerA : ReadyActor :=
  {
    actor := "workera"
    logicalTime := 0
  }

def workerB : ReadyActor :=
  {
    actor := "workerb"
    logicalTime := 0
  }

def readyPair : List ReadyActor :=
  [
    workerA,
    workerB
  ]

def baseRequest : ActorPriorityRequest :=
  some
    [
      ("workera", 1),
      ("workerb", 2)
    ]

def reversedRequest : ActorPriorityRequest :=
  some
    [
      ("workera", 2),
      ("workerb", 1)
    ]

example :
    sourceActorSelectionObservation
      readyPair
      baseRequest = ["workera"] := by
  decide

example :
    sourceActorSelectionObservation
      readyPair
      reversedRequest = ["workerb"] := by
  decide

example :
    sourceActorSelectionObservation
        readyPair
        baseRequest ≠
      sourceActorSelectionObservation
        readyPair
        reversedRequest := by
  decide

example :
    eraseActorPriorities baseRequest =
      eraseActorPriorities reversedRequest := by
  rfl

example
    (targetObservation :
      Unit → ActorSelectionObservation) :
    ¬ (
      PreservesActorSelection
          eraseActorPriorities
          targetObservation
          readyPair
          baseRequest ∧
        PreservesActorSelection
          eraseActorPriorities
          targetObservation
          readyPair
          reversedRequest
    ) := by
  exact
    actorPriorityErasureCannotPreserveDiscriminatingPair
      eraseActorPriorities
      targetObservation
      readyPair
      baseRequest
      reversedRequest
      rfl
      (by decide)

example
    {Target : Type}
    (translate :
      ActorPriorityRequest → Target)
    (targetObservation :
      Target → ActorSelectionObservation)
    (hBase :
      PreservesActorSelection
        translate
        targetObservation
        readyPair
        baseRequest)
    (hReversed :
      PreservesActorSelection
        translate
        targetObservation
        readyPair
        reversedRequest) :
    translate baseRequest ≠
      translate reversedRequest := by
  exact
    faithfulActorTranslationMustPreservePriorityDistinction
      translate
      targetObservation
      readyPair
      baseRequest
      reversedRequest
      (by decide)
      hBase
      hReversed

end Relico.Tests.ActorPriorityErasureImpossibility
