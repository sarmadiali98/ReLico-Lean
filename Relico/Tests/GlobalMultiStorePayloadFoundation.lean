import Relico.Correctness.GlobalMultiStorePayloadStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadFoundation

def actorA :
    ActorName :=
  ⟨"actorA"⟩

def actorB :
    ActorName :=
  ⟨"actorB"⟩

def actorC :
    ActorName :=
  ⟨"actorC"⟩

def className :
    ClassName :=
  ⟨"Controller"⟩

def knownB :
    KnownRebecName :=
  ⟨"peer"⟩

def emptyReactiveClass :
    DTR.MultiStorePayloadReactiveClass where

  name :=
    className

  stateVariables :=
    []

  constructor := {
    body := []
  }

  messageServers :=
    []

def modelA :
    DTR.MultiStorePayloadModel where

  reactiveClass :=
    emptyReactiveClass

  actor := {
    name :=
      actorA

    className :=
      className
  }

def modelB :
    DTR.MultiStorePayloadModel where

  reactiveClass :=
    emptyReactiveClass

  actor := {
    name :=
      actorB

    className :=
      className
  }

def zeroActorModel :
    DTR.GlobalMultiStorePayloadModel where

  actors :=
    []

  topology :=
    []

def oneActorModel :
    DTR.GlobalMultiStorePayloadModel where

  actors :=
    [
      (
        actorA,
        modelA
      )
    ]

  topology :=
    [
      (
        actorA,
        []
      )
    ]

def twoActorTopology :
    ActorTopology :=
  [
    (
      actorA,
      [
        (
          knownB,
          actorB
        )
      ]
    ),
    (
      actorB,
      []
    )
  ]

def twoActorModel :
    DTR.GlobalMultiStorePayloadModel where

  actors :=
    [
      (
        actorA,
        modelA
      ),
      (
        actorB,
        modelB
      )
    ]

  topology :=
    twoActorTopology

def duplicateActorModel :
    DTR.GlobalMultiStorePayloadModel where

  actors :=
    [
      (
        actorA,
        modelA
      ),
      (
        actorA,
        modelA
      )
    ]

  topology :=
    [
      (
        actorA,
        []
      ),
      (
        actorA,
        []
      )
    ]

def missingSenderTopologyModel :
    DTR.GlobalMultiStorePayloadModel where

  actors :=
    [
      (
        actorA,
        modelA
      ),
      (
        actorB,
        modelB
      )
    ]

  topology :=
    [
      (
        actorA,
        []
      )
    ]

def danglingReceiverModel :
    DTR.GlobalMultiStorePayloadModel where

  actors :=
    [
      (
        actorA,
        modelA
      )
    ]

  topology :=
    [
      (
        actorA,
        [
          (
            knownB,
            actorB
          )
        ]
      )
    ]

def duplicateKnownBindingModel :
    DTR.GlobalMultiStorePayloadModel where

  actors :=
    [
      (
        actorA,
        modelA
      ),
      (
        actorB,
        modelB
      )
    ]

  topology :=
    [
      (
        actorA,
        [
          (
            knownB,
            actorB
          ),
          (
            knownB,
            actorB
          )
        ]
      ),
      (
        actorB,
        []
      )
    ]

theorem actorA_ne_actorB :
    actorA ≠ actorB := by
  decide

/--
Zero actors are a valid structural boundary case.
-/
theorem zero_actor_model_wellFormed :
    DTR.GlobalMultiStorePayloadModel.wellFormed
        zeroActorModel =
      true := by
  rfl

/--
One actor with an explicit empty binding environment is valid.
-/
theorem one_actor_model_wellFormed :
    DTR.GlobalMultiStorePayloadModel.wellFormed
        oneActorModel =
      true := by
  rfl

/--
Two actors with one declared known-rebec binding are valid.
-/
theorem two_actor_model_wellFormed :
    DTR.GlobalMultiStorePayloadModel.wellFormed
        twoActorModel =
      true := by
  rfl

/--
Duplicate actor keys are rejected.
-/
theorem duplicate_actor_model_rejected :
    DTR.GlobalMultiStorePayloadModel.wellFormed
        duplicateActorModel =
      false := by
  rfl

/--
Every actor must have a topology sender entry in the same deterministic order.
-/
theorem missing_topology_sender_rejected :
    DTR.GlobalMultiStorePayloadModel.wellFormed
        missingSenderTopologyModel =
      false := by
  rfl

/--
A topology receiver must name a declared actor.
-/
theorem dangling_receiver_rejected :
    DTR.GlobalMultiStorePayloadModel.wellFormed
        danglingReceiverModel =
      false := by
  rfl

/--
Known-rebec names are unique within one sender environment.
-/
theorem duplicate_known_binding_rejected :
    DTR.GlobalMultiStorePayloadModel.wellFormed
        duplicateKnownBindingModel =
      false := by
  rfl

/--
The positive topology resolves the sender-relative name to actor B.
-/
theorem topology_resolves_declared_receiver :
    ActorTopology.resolve
        twoActorTopology
        actorA
        knownB =
      some actorB := by
  rfl

/--
Unknown actors are not synthesized by global model lookup.
-/
theorem unknown_actor_lookup_is_none :
    DTR.GlobalMultiStorePayloadModel.lookupActor
        twoActorModel
        actorC =
      none := by
  rfl

/--
Actor-wise translation preserves deterministic actor order exactly.
-/
theorem translation_preserves_actor_order :
    Store.keys
        (Translation.translateGlobalMultiStorePayloadCore
          twoActorModel).actorPrograms =
      [
        actorA,
        actorB
      ] := by
  rfl

/--
The abstract topology is unchanged by the E2 structural translation.
-/
theorem translation_preserves_topology :
    (Translation.translateGlobalMultiStorePayloadCore
      twoActorModel).topology =
      twoActorTopology := by
  rfl

def twoActorSourceState :
    DTR.GlobalMultiStorePayloadState where

  currentTime :=
    default

  actorStates :=
    [
      (
        actorA,
        default
      ),
      (
        actorB,
        default
      )
    ]

/--
Updating actor A leaves actor B's state lookup unchanged.
-/
theorem update_preserves_unrelated_actor :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (DTR.GlobalMultiStorePayloadState.updateActor
          twoActorSourceState
          actorA
          default)
        actorB =
      DTR.GlobalMultiStorePayloadState.lookupActor
        twoActorSourceState
        actorB := by
  exact
    DTR.GlobalMultiStorePayloadState.lookupActor_update_ne
      twoActorSourceState
      (actorName :=
        actorA)
      (otherActor :=
        actorB)
      default
      actorA_ne_actorB

/--
A singleton model/state pair packages into the global relation whenever the
published local runtime correspondence and global-time equality are supplied.
-/
theorem singleton_global_runtime_correspondence
    (sourceState :
      DTR.MultiStorePayloadState)
    (targetState :
      LF.MultiStorePayloadState)
    (sourceTime :
      LogicalTime)
    (targetTag :
      LF.Tag)
    (hTime :
      sourceTime =
        targetTag.time)
    (hLocal :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        modelA.reactiveClass.messageServers
        sourceState
        targetState) :
    Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
      oneActorModel
      (Translation.translateGlobalMultiStorePayloadCore
        oneActorModel)
      {
        currentTime :=
          sourceTime

        actorStates :=
          [
            (
              actorA,
              sourceState
            )
          ]
      }
      {
        currentTag :=
          targetTag

        actorStates :=
          [
            (
              actorA,
              targetState
            )
          ]
      } := by

  refine {
    compiledActorPrograms := ?_
    topology := ?_
    currentTime := hTime
    actorStates := ?_
  }

  · rfl

  · rfl

  · exact
      Correctness.GlobalMultiStorePayloadActorStatesCorrespond.cons
        hLocal
        .nil

/--
Mismatched actor domains cannot inhabit the pointwise relation.
-/
theorem mismatched_actor_domains_not_correspond :
    ¬
      Correctness.GlobalMultiStorePayloadActorStatesCorrespond
        [
          (
            actorA,
            modelA
          )
        ]
        [
          (
            actorA,
            default
          )
        ]
        [] := by

  intro hCorrespond
  cases hCorrespond

end GlobalMultiStorePayloadFoundation
end Tests
end Relico
