import Relico.Translation.GlobalMultiStorePayloadActorOrder

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadActorOrderTranslation

open Translation.GlobalMultiStorePayloadActorOrder

def workerAName : ActorName :=
  ActorName.mk "workera"

def workerBName : ActorName :=
  ActorName.mk "workerb"

def sourceBaseAssignment :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment :=
  [
    (workerAName, 1),
    (workerBName, 2)
  ]

def sourceReversedAssignment :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment :=
  [
    (workerAName, 2),
    (workerBName, 1)
  ]

def sourceTiedAssignment :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment :=
  [
    (workerAName, 1),
    (workerBName, 1)
  ]

def sourceIncompleteAssignment :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment :=
  [
    (workerAName, 1)
  ]

def sourceBaseRequest :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest :=
  some sourceBaseAssignment

def sourceReversedRequest :
    DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest :=
  some sourceReversedAssignment

def sourceReadyA :
    DTR.GlobalMultiStorePayloadActorPriority.ReadyActor :=
  {
    actorName := workerAName
    logicalTime := 0
  }

def sourceReadyB :
    DTR.GlobalMultiStorePayloadActorPriority.ReadyActor :=
  {
    actorName := workerBName
    logicalTime := 0
  }

def sourceReadyPair :
    List
      DTR.GlobalMultiStorePayloadActorPriority.ReadyActor :=
  [
    sourceReadyA,
    sourceReadyB
  ]

def targetReadyA :
    LF.GlobalMultiStorePayloadActorOrder.ReadyTargetActor :=
  {
    actorName := workerAName
    logicalTime := 0
  }

def targetReadyB :
    LF.GlobalMultiStorePayloadActorOrder.ReadyTargetActor :=
  {
    actorName := workerBName
    logicalTime := 0
  }

/- Test 1: empty assignments remain empty. -/
example :
    compileActorPriorityAssignment [] =
      [] :=
  rfl

/- Test 2: base actor names and numeric values are preserved. -/
example :
    compileActorPriorityAssignment
        sourceBaseAssignment =
      [
        (workerAName, 1),
        (workerBName, 2)
      ] := by
  decide

/- Test 3: absence remains absence. -/
example :
    compileActorPriorityRequest none =
      none :=
  rfl

/- Test 4: a present base request remains present. -/
example :
    compileActorPriorityRequest
        sourceBaseRequest =
      some
        [
          (workerAName, 1),
          (workerBName, 2)
        ] := by
  decide

/- Test 5: base and reversed priority requests remain distinguishable. -/
example :
    compileActorPriorityRequest
        sourceBaseRequest ≠
      compileActorPriorityRequest
        sourceReversedRequest := by
  decide

/- Test 6: tied source priorities remain tied target orders. -/
example :
    compileActorPriorityAssignment
        sourceTiedAssignment =
      [
        (workerAName, 1),
        (workerBName, 1)
      ] := by
  decide

/- Test 7: incomplete assignments remain incomplete. -/
example :
    compileActorPriorityAssignment
        sourceIncompleteAssignment =
      [
        (workerAName, 1)
      ] := by
  decide

/- Test 8: present empty metadata is not collapsed into absence. -/
example :
    compileActorPriorityRequest
        (
          some
            (
              [] :
                DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityAssignment
            )
        ) =
      some [] :=
  rfl

/- Test 9: ready-actor names are preserved. -/
example :
    (
      compileReadyActor
        sourceReadyA
    ).actorName =
      workerAName :=
  rfl

/- Test 10: ready-actor logical times are preserved. -/
example :
    (
      compileReadyActor
        sourceReadyA
    ).logicalTime =
      0 :=
  rfl

/- Test 11: ready-list order and entries are preserved. -/
example :
    compileReadyActors
        sourceReadyPair =
      [
        targetReadyA,
        targetReadyB
      ] := by
  decide

/- Test 12: compilation does not invent or drop assignment entries. -/
example :
    (
      compileActorPriorityAssignment
        sourceBaseAssignment
    ).length =
      sourceBaseAssignment.length := by

  exact
    compileActorPriorityAssignment_length
      sourceBaseAssignment


/-
Witnesses for the named results proved in the corresponding non-test module.
`Relico/Tests/` is the only directory the obligation extractor scans, so each
result is referenced here to register it as a benchmark obligation.
-/

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityAssignment_nil

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityAssignment_cons

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityAssignment_eq

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest_none

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest_some

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest_eq

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileReadyActor_actorName

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileReadyActor_logicalTime

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors_nil

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors_cons

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors_length

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors_actorNames

#check
  Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors_logicalTimes

end GlobalMultiStorePayloadActorOrderTranslation
end Tests
end Relico
