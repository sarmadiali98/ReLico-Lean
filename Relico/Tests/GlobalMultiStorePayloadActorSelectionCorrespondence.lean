import Relico.Correctness.GlobalMultiStorePayloadActorSelectionCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadActorSelectionCorrespondence

open DTR.GlobalMultiStorePayloadActorPriority
open LF.GlobalMultiStorePayloadActorOrder
open Translation.GlobalMultiStorePayloadActorOrder
open Correctness.GlobalMultiStorePayloadActorSelectionCorrespondence

private def actorA : ActorName :=
  ActorName.mk "workera"

private def actorB : ActorName :=
  ActorName.mk "workerb"

private def readyBase : List ReadyActor :=
  [
    {
      actorName := actorA
      logicalTime := 0
    },
    {
      actorName := actorB
      logicalTime := 0
    }
  ]

private def readyDifferentTimes : List ReadyActor :=
  [
    {
      actorName := actorA
      logicalTime := 1
    },
    {
      actorName := actorB
      logicalTime := 0
    }
  ]

private def baseRequest : ActorPriorityRequest :=
  some
    [
      (actorA, 1),
      (actorB, 2)
    ]

private def reversedRequest : ActorPriorityRequest :=
  some
    [
      (actorA, 2),
      (actorB, 1)
    ]

private def tiedRequest : ActorPriorityRequest :=
  some
    [
      (actorA, 1),
      (actorB, 1)
    ]

private def incompleteRequest : ActorPriorityRequest :=
  some
    [
      (actorA, 1)
    ]

private def absentRequest : ActorPriorityRequest :=
  none

example :
    actorPriorityEligibleBool
        baseRequest
        readyBase
        actorA =
      true := by
  native_decide

example :
    actorPriorityEligibleBool
        baseRequest
        readyBase
        actorB =
      false := by
  native_decide

example :
    actorPriorityEligibleBool
        reversedRequest
        readyBase
        actorB =
      true := by
  native_decide

example :
    eligibleActorNames
        tiedRequest
        readyBase =
      [actorA, actorB] := by
  native_decide

example :
    eligibleActorNames
        absentRequest
        readyBase =
      [actorA, actorB] := by
  native_decide

example :
    eligibleActorNames
        incompleteRequest
        readyBase =
      [actorA, actorB] := by
  native_decide

example :
    actorPriorityEligibleBool
        baseRequest
        readyDifferentTimes
        actorB =
      true := by
  native_decide

example :
    targetActorOrderEligibleBool
        (compileActorPriorityRequest baseRequest)
        (compileReadyActors readyBase)
        actorA =
      true := by
  native_decide

example :
    targetActorOrderEligibleBool
        (compileActorPriorityRequest baseRequest)
        (compileReadyActors readyBase)
        actorB =
      false := by
  native_decide

example :
    actorPriorityEligibleBool
        baseRequest
        readyBase
        actorA =
      targetActorOrderEligibleBool
        (compileActorPriorityRequest baseRequest)
        (compileReadyActors readyBase)
        actorA :=
  actorSelectionEligibleBool_compile_eq
    baseRequest
    readyBase
    actorA

example :
    ActorPriorityEligible
        baseRequest
        readyBase
        actorA ↔
      TargetActorOrderEligible
        (compileActorPriorityRequest baseRequest)
        (compileReadyActors readyBase)
        actorA :=
  actorSelectionEligible_compile_iff
    baseRequest
    readyBase
    actorA

example :
    TargetActorOrderEligible
        (compileActorPriorityRequest baseRequest)
        (compileReadyActors readyBase)
        actorA := by
  exact
    actorSelectionEligible_forward
      baseRequest
      readyBase
      actorA
      (by native_decide)

example :
    ActorPriorityEligible
        baseRequest
        readyBase
        actorA := by
  exact
    actorSelectionEligible_backward
      baseRequest
      readyBase
      actorA
      (by native_decide)

example :
    eligibleActorNames
        baseRequest
        readyBase =
      eligibleTargetActorNames
        (compileActorPriorityRequest baseRequest)
        (compileReadyActors readyBase) :=
  eligibleActorNames_compile_eq
    baseRequest
    readyBase

end GlobalMultiStorePayloadActorSelectionCorrespondence
end Tests
end Relico
