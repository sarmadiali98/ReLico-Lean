import Relico.LF.GlobalMultiStorePayloadActorOrder

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadActorOrder

open LF
open LF.GlobalMultiStorePayloadActorOrder

def workerAName : ActorName :=
  ActorName.mk "workera"

def workerBName : ActorName :=
  ActorName.mk "workerb"

def workerCName : ActorName :=
  ActorName.mk "workerc"

def workerA : ReadyTargetActor :=
  {
    actorName := workerAName
    logicalTime := 0
  }

def workerB : ReadyTargetActor :=
  {
    actorName := workerBName
    logicalTime := 0
  }

def workerBLater : ReadyTargetActor :=
  {
    actorName := workerBName
    logicalTime := 1
  }

def readyPair : List ReadyTargetActor :=
  [
    workerA,
    workerB
  ]

def staggeredPair : List ReadyTargetActor :=
  [
    workerA,
    workerBLater
  ]

def baseOrder : ActorOrderRequest :=
  some
    [
      (workerAName, 1),
      (workerBName, 2)
    ]

def reversedOrder : ActorOrderRequest :=
  some
    [
      (workerAName, 2),
      (workerBName, 1)
    ]

def tiedOrder : ActorOrderRequest :=
  some
    [
      (workerAName, 1),
      (workerBName, 1)
    ]

def incompleteOrder : ActorOrderRequest :=
  some
    [
      (workerAName, 1)
    ]

/- Test 1: the base compiled order selects worker A. -/
example :
    eligibleTargetActorNames
      baseOrder
      readyPair =
    [workerAName] := by
  decide

/- Test 2: reversing only the compiled order selects worker B. -/
example :
    eligibleTargetActorNames
      reversedOrder
      readyPair =
    [workerBName] := by
  decide

/- Test 3: tied minimum order retains both target actors. -/
example :
    eligibleTargetActorNames
      tiedOrder
      readyPair =
    [
      workerAName,
      workerBName
    ] := by
  decide

/- Test 4: absent order metadata retains both earliest actors. -/
example :
    eligibleTargetActorNames
      none
      readyPair =
    [
      workerAName,
      workerBName
    ] := by
  decide

/- Test 5: incomplete order metadata does not eliminate uncovered actors. -/
example :
    eligibleTargetActorNames
      incompleteOrder
      readyPair =
    [
      workerAName,
      workerBName
    ] := by
  decide

/- Test 6: logical time precedes target actor ordering. -/
example :
    eligibleTargetActorNames
      reversedOrder
      staggeredPair =
    [workerAName] := by
  decide

/- Test 7: an actor absent from the target ready set is ineligible. -/
example :
    ¬ TargetActorOrderEligible
        baseOrder
        readyPair
        workerCName := by
  decide

/- Test 8: worker B is ineligible under the base compiled order. -/
example :
    ¬ TargetActorOrderEligible
        baseOrder
        readyPair
        workerBName := by
  decide

section WrapperTests

variable
  {program :
    LF.GlobalMultiStorePayloadProgram}
  {before after :
    LF.GlobalMultiStorePayloadState}
  {selectedAction :
    LF.PendingAction}
  {selectedReaction :
    LF.MultiStorePayloadReaction}

/- Test 9: an eligible actor wraps the existing LF Step. -/
example
    (hDispatch :
      LF.GlobalMultiStorePayloadDispatch.Step
        program
        workerAName
        before
        selectedAction
        selectedReaction
        after) :
    ActorOrderDispatchStep
      baseOrder
      readyPair
      program
      workerAName
      before
      selectedAction
      selectedReaction
      after := by

  exact
    ActorOrderDispatchStep.lift
      (by decide)
      hDispatch

/- Test 10: the wrapper exposes eligibility and the unchanged LF Step. -/
example
    (hStep :
      ActorOrderDispatchStep
        baseOrder
        readyPair
        program
        workerAName
        before
        selectedAction
        selectedReaction
        after) :
    TargetActorOrderEligible
        baseOrder
        readyPair
        workerAName ∧
      LF.GlobalMultiStorePayloadDispatch.Step
        program
        workerAName
        before
        selectedAction
        selectedReaction
        after := by

  exact
    ⟨
      hStep.eligible,
      hStep.dispatch
    ⟩

end WrapperTests

end GlobalMultiStorePayloadActorOrder
end Tests
end Relico
