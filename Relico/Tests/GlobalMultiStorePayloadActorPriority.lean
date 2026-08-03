import Relico.DTR.GlobalMultiStorePayloadActorPriority

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadActorPriority

open DTR
open DTR.GlobalMultiStorePayloadActorPriority

def workerAName : ActorName :=
  ActorName.mk "workera"

def workerBName : ActorName :=
  ActorName.mk "workerb"

def workerCName : ActorName :=
  ActorName.mk "workerc"

def workerA : ReadyActor :=
  {
    actorName := workerAName
    logicalTime := 0
  }

def workerB : ReadyActor :=
  {
    actorName := workerBName
    logicalTime := 0
  }

def workerBLater : ReadyActor :=
  {
    actorName := workerBName
    logicalTime := 1
  }

def readyPair : List ReadyActor :=
  [
    workerA,
    workerB
  ]

def staggeredPair : List ReadyActor :=
  [
    workerA,
    workerBLater
  ]

def baseRequest : ActorPriorityRequest :=
  some
    [
      (workerAName, 1),
      (workerBName, 2)
    ]

def reversedRequest : ActorPriorityRequest :=
  some
    [
      (workerAName, 2),
      (workerBName, 1)
    ]

def tiedRequest : ActorPriorityRequest :=
  some
    [
      (workerAName, 1),
      (workerBName, 1)
    ]

def incompleteRequest : ActorPriorityRequest :=
  some
    [
      (workerAName, 1)
    ]

/- Test 1: base assignment selects workera. -/
example :
    eligibleActorNames
      baseRequest
      readyPair =
    [workerAName] := by
  decide

/- Test 2: reversing only priorities selects workerb. -/
example :
    eligibleActorNames
      reversedRequest
      readyPair =
    [workerBName] := by
  decide

/- Test 3: tied minimal priorities retain both actors. -/
example :
    eligibleActorNames
      tiedRequest
      readyPair =
    [
      workerAName,
      workerBName
    ] := by
  decide

/- Test 4: absent priority metadata retains both earliest actors. -/
example :
    eligibleActorNames
      none
      readyPair =
    [
      workerAName,
      workerBName
    ] := by
  decide

/- Test 5: incomplete assignment does not eliminate uncovered actors. -/
example :
    eligibleActorNames
      incompleteRequest
      readyPair =
    [
      workerAName,
      workerBName
    ] := by
  decide

/- Test 6: logical time precedes actor priority. -/
example :
    eligibleActorNames
      reversedRequest
      staggeredPair =
    [workerAName] := by
  decide

/- Test 7: an actor absent from the ready set is ineligible. -/
example :
    ¬ ActorPriorityEligible
        baseRequest
        readyPair
        workerCName := by
  decide

/- Test 8: workerb is ineligible under the base assignment. -/
example :
    ¬ ActorPriorityEligible
        baseRequest
        readyPair
        workerBName := by
  decide

section WrapperTests

variable
  {model :
    DTR.GlobalMultiStorePayloadModel}
  {before after :
    DTR.GlobalMultiStorePayloadState}
  {selectedMessage :
    DTR.PendingMessage}
  {selectedServer :
    DTR.MultiStorePayloadMessageServer}

/- Test 9: an eligible actor wraps the existing chosen-actor Step. -/
example
    (hDispatch :
      DTR.GlobalMultiStorePayloadDispatch.Step
        model
        workerAName
        before
        selectedMessage
        selectedServer
        after) :
    ActorPriorityDispatchStep
      baseRequest
      readyPair
      model
      workerAName
      before
      selectedMessage
      selectedServer
      after := by

  exact
    ActorPriorityDispatchStep.lift
      (by decide)
      hDispatch

/- Test 10: the wrapper exposes eligibility and existing dispatch. -/
example
    (hStep :
      ActorPriorityDispatchStep
        baseRequest
        readyPair
        model
        workerAName
        before
        selectedMessage
        selectedServer
        after) :
    ActorPriorityEligible
        baseRequest
        readyPair
        workerAName ∧
      DTR.GlobalMultiStorePayloadDispatch.Step
        model
        workerAName
        before
        selectedMessage
        selectedServer
        after := by

  exact
    ⟨
      hStep.eligible,
      hStep.dispatch
    ⟩

end WrapperTests

end GlobalMultiStorePayloadActorPriority
end Tests
end Relico
