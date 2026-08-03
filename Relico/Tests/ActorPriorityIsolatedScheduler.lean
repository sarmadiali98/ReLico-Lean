import Relico.Investigation.ActorPriority.IsolatedScheduler

namespace Relico.Tests.ActorPriorityIsolatedScheduler

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

def tiedRequest : ActorPriorityRequest :=
  some
    [
      ("workera", 1),
      ("workerb", 1)
    ]

def absentRequest : ActorPriorityRequest :=
  none

def explicitEmptyRequest : ActorPriorityRequest :=
  some []

example :
    simultaneous readyPair = true := by
  decide

example :
    requestCovers baseRequest readyPair = true := by
  decide

example :
    prioritySelectionEnabled baseRequest readyPair = true := by
  decide

example :
    lookupPriority baseRequest "workera" = some 1 := by
  decide

example :
    sourceStrictlyPrecedes
      baseRequest
      workerA
      workerB = true := by
  decide

example :
    sourceEligibleActorNames
      baseRequest
      readyPair = ["workera"] := by
  decide

example :
    sourceEligibleActorNames
      reversedRequest
      readyPair = ["workerb"] := by
  decide

example :
    sourceEligibleActorNames
      tiedRequest
      readyPair = ["workera", "workerb"] := by
  decide

example :
    sourceEligibleActorNames
      absentRequest
      readyPair = ["workera", "workerb"] := by
  decide

example :
    requestCovers
      explicitEmptyRequest
      readyPair = false := by
  decide

example :
    sourceEligibleActorNames
      explicitEmptyRequest
      readyPair = ["workera", "workerb"] := by
  decide

example :
    sourceEligibleActorNames
      baseRequest
      readyPair ≠
    sourceEligibleActorNames
      reversedRequest
      readyPair := by
  decide

end Relico.Tests.ActorPriorityIsolatedScheduler
