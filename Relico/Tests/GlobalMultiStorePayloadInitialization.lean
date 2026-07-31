import Relico.Correctness.GlobalMultiStorePayloadInitializationCorrespondence
import Relico.Tests.GlobalMultiStorePayloadFoundation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadInitialization

open GlobalMultiStorePayloadFoundation

def counterName :
    VarName :=
  ⟨"counter"⟩

def storeA :
    StateStore :=
  [
    (
      counterName,
      11
    )
  ]

def storeB :
    StateStore :=
  [
    (
      counterName,
      29
    )
  ]

def zeroInitialStores :
    DTR.GlobalMultiStorePayloadInitialStores :=
  []

def oneInitialStores :
    DTR.GlobalMultiStorePayloadInitialStores :=
  [
    (
      actorA,
      storeA
    )
  ]

def twoInitialStores :
    DTR.GlobalMultiStorePayloadInitialStores :=
  [
    (
      actorA,
      storeA
    ),
    (
      actorB,
      storeB
    )
  ]

def duplicateInitialStores :
    DTR.GlobalMultiStorePayloadInitialStores :=
  [
    (
      actorA,
      storeA
    ),
    (
      actorA,
      storeB
    )
  ]

def missingInitialStores :
    DTR.GlobalMultiStorePayloadInitialStores :=
  [
    (
      actorA,
      storeA
    )
  ]

def extraInitialStores :
    DTR.GlobalMultiStorePayloadInitialStores :=
  [
    (
      actorA,
      storeA
    ),
    (
      actorB,
      storeB
    ),
    (
      actorC,
      []
    )
  ]

def reorderedInitialStores :
    DTR.GlobalMultiStorePayloadInitialStores :=
  [
    (
      actorB,
      storeB
    ),
    (
      actorA,
      storeA
    )
  ]

def zeroStartupEntries :
    DTR.GlobalMultiStorePayloadStartupEntries :=
  []

def oneStartupEntries :
    DTR.GlobalMultiStorePayloadStartupEntries :=
  [
    (
      actorA,
      (
        modelA,
        storeA
      )
    )
  ]

def twoStartupEntries :
    DTR.GlobalMultiStorePayloadStartupEntries :=
  [
    (
      actorA,
      (
        modelA,
        storeA
      )
    ),
    (
      actorB,
      (
        modelB,
        storeB
      )
    )
  ]

theorem zero_initial_stores_wellFormed :
    DTR.GlobalMultiStorePayloadInitialization.initialStoresWellFormed
        zeroActorModel.actors
        zeroInitialStores =
      true := by
  rfl

theorem one_initial_stores_wellFormed :
    DTR.GlobalMultiStorePayloadInitialization.initialStoresWellFormed
        oneActorModel.actors
        oneInitialStores =
      true := by
  rfl

theorem two_initial_stores_wellFormed :
    DTR.GlobalMultiStorePayloadInitialization.initialStoresWellFormed
        twoActorModel.actors
        twoInitialStores =
      true := by
  rfl

theorem duplicate_initial_stores_rejected :
    DTR.GlobalMultiStorePayloadInitialization.initialStoresWellFormed
        twoActorModel.actors
        duplicateInitialStores =
      false := by
  rfl

theorem missing_initial_store_rejected :
    DTR.GlobalMultiStorePayloadInitialization.initialStoresWellFormed
        twoActorModel.actors
        missingInitialStores =
      false := by
  rfl

theorem extra_initial_store_rejected :
    DTR.GlobalMultiStorePayloadInitialization.initialStoresWellFormed
        twoActorModel.actors
        extraInitialStores =
      false := by
  rfl

theorem reordered_initial_stores_rejected :
    DTR.GlobalMultiStorePayloadInitialization.initialStoresWellFormed
        twoActorModel.actors
        reorderedInitialStores =
      false := by
  rfl

theorem zero_alignment :
    DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
        zeroActorModel.actors
        zeroInitialStores =
      some zeroStartupEntries := by
  rfl

theorem one_alignment :
    DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
        oneActorModel.actors
        oneInitialStores =
      some oneStartupEntries := by
  rfl

theorem two_alignment :
    DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
        twoActorModel.actors
        twoInitialStores =
      some twoStartupEntries := by
  rfl

theorem missing_alignment_is_none :
    DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
        twoActorModel.actors
        missingInitialStores =
      none := by
  rfl

theorem extra_alignment_is_none :
    DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
        twoActorModel.actors
        extraInitialStores =
      none := by
  rfl

theorem reordered_alignment_is_none :
    DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
        twoActorModel.actors
        reorderedInitialStores =
      none := by
  rfl

theorem zero_source_initialization_succeeds :
    _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          zeroActorModel
          zeroInitialStores =
      some
        (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            zeroStartupEntries) := by
  rfl

theorem one_source_initialization_succeeds :
    _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          oneActorModel
          oneInitialStores =
      some
        (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            oneStartupEntries) := by
  rfl

theorem two_source_initialization_succeeds :
    _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          twoActorModel
          twoInitialStores =
      some
        (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            twoStartupEntries) := by
  rfl

theorem zero_target_initialization_succeeds :
    _root_.Relico.LF.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          zeroActorModel
          zeroInitialStores =
      some
        (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            zeroStartupEntries) := by
  rfl

theorem one_target_initialization_succeeds :
    _root_.Relico.LF.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          oneActorModel
          oneInitialStores =
      some
        (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            oneStartupEntries) := by
  rfl

theorem two_target_initialization_succeeds :
    _root_.Relico.LF.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          twoActorModel
          twoInitialStores =
      some
        (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            twoStartupEntries) := by
  rfl

theorem duplicate_source_initialization_rejected :
    _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          twoActorModel
          duplicateInitialStores =
      none := by
  rfl

theorem missing_source_initialization_rejected :
    _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          twoActorModel
          missingInitialStores =
      none := by
  rfl

theorem extra_target_initialization_rejected :
    _root_.Relico.LF.GlobalMultiStorePayloadInitialization.initializeGlobalMultiStorePayloadState
          twoActorModel
          extraInitialStores =
      none := by
  rfl

theorem source_actorA_lookup :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            twoStartupEntries)
        actorA =
      some
        (_root_.Relico.DTR.MultiStorePayloadConstructor.startupMultiStorePayloadState
            modelA.reactiveClass.constructor
            storeA) := by
  rfl

theorem source_actorB_lookup :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            twoStartupEntries)
        actorB =
      some
        (_root_.Relico.DTR.MultiStorePayloadConstructor.startupMultiStorePayloadState
            modelB.reactiveClass.constructor
            storeB) := by
  rfl

theorem target_actorA_lookup :
    LF.GlobalMultiStorePayloadState.lookupActor
        (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            twoStartupEntries)
        actorA =
      some
        (LF.startupLFMultiStorePayloadState
          modelA.reactiveClass.constructor
          storeA) := by
  rfl

theorem target_actorB_lookup :
    LF.GlobalMultiStorePayloadState.lookupActor
        (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            twoStartupEntries)
        actorB =
      some
        (LF.startupLFMultiStorePayloadState
          modelB.reactiveClass.constructor
          storeB) := by
  rfl

theorem source_startup_keys :
    Store.keys
        (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            twoStartupEntries).actorStates =
      [
        actorA,
        actorB
      ] := by
  rfl

theorem target_startup_keys :
    Store.keys
        (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
            twoStartupEntries).actorStates =
      [
        actorA,
        actorB
      ] := by
  rfl

theorem source_global_time_is_zero :
    (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
        twoStartupEntries).currentTime =
      0 := by
  rfl

theorem target_global_tag_is_zero :
    (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
        twoStartupEntries).currentTag =
      {
        time :=
          0

        microstep :=
          0
      } := by
  rfl

theorem zero_global_startup_corresponds :
    Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
      zeroActorModel
      (Translation.translateGlobalMultiStorePayloadCore
        zeroActorModel)
      (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
          zeroStartupEntries)
      (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
          zeroStartupEntries) := by

  exact
    Correctness.globalMultiStorePayloadStartupRuntime_correspond
      zeroActorModel
      zeroInitialStores
      zeroStartupEntries
      zero_alignment

theorem one_global_startup_corresponds :
    Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
      oneActorModel
      (Translation.translateGlobalMultiStorePayloadCore
        oneActorModel)
      (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
          oneStartupEntries)
      (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
          oneStartupEntries) := by

  exact
    Correctness.globalMultiStorePayloadStartupRuntime_correspond
      oneActorModel
      oneInitialStores
      oneStartupEntries
      one_alignment

theorem two_global_startup_corresponds :
    Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
      twoActorModel
      (Translation.translateGlobalMultiStorePayloadCore
        twoActorModel)
      (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
          twoStartupEntries)
      (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
          twoStartupEntries) := by

  exact
    Correctness.globalMultiStorePayloadStartupRuntime_correspond
      twoActorModel
      twoInitialStores
      twoStartupEntries
      two_alignment

theorem translated_two_actor_model_wellFormed :
    LF.GlobalMultiStorePayloadProgram.wellFormed
        (Translation.translateGlobalMultiStorePayloadCore
          twoActorModel) =
      true := by

  exact
    Correctness.translateGlobalMultiStorePayloadCore_wellFormed
      two_actor_model_wellFormed

theorem declared_topology_resolution_preserved :
    ActorTopology.resolve
        (Translation.translateGlobalMultiStorePayloadCore
          twoActorModel).topology
        actorA
        knownB =
      ActorTopology.resolve
        twoActorModel.topology
        actorA
        knownB := by

  exact
    Correctness.translateGlobalMultiStorePayloadCore_resolve
      twoActorModel
      actorA
      knownB

theorem unknown_sender_resolution_preserved :
    ActorTopology.resolve
        (Translation.translateGlobalMultiStorePayloadCore
          twoActorModel).topology
        actorC
        knownB =
      ActorTopology.resolve
        twoActorModel.topology
        actorC
        knownB := by

  exact
    Correctness.translateGlobalMultiStorePayloadCore_resolve
      twoActorModel
      actorC
      knownB

def unknownKnownRebec :
    KnownRebecName :=
  ⟨"unknown"⟩

theorem unknown_known_rebec_resolution_preserved :
    ActorTopology.resolve
        (Translation.translateGlobalMultiStorePayloadCore
          twoActorModel).topology
        actorA
        unknownKnownRebec =
      ActorTopology.resolve
        twoActorModel.topology
        actorA
        unknownKnownRebec := by

  exact
    Correctness.translateGlobalMultiStorePayloadCore_resolve
      twoActorModel
      actorA
      unknownKnownRebec

theorem static_correspondence_packages_all_fields :
    Correctness.GlobalMultiStorePayloadStaticCorresponds
      twoActorModel
      (Translation.translateGlobalMultiStorePayloadCore
        twoActorModel) := by

  exact
    Correctness.translateGlobalMultiStorePayloadCore_staticCorresponds
      twoActorModel

end GlobalMultiStorePayloadInitialization
end Tests
end Relico
