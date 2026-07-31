import Relico.Correctness.GlobalMultiStorePayloadStateCorrespondence
import Relico.DTR.GlobalMultiStorePayloadInitialization
import Relico.LF.GlobalMultiStorePayloadInitialization

set_option autoImplicit false

namespace Relico
namespace Correctness

theorem compileGlobalMultiStorePayloadActors_eq_mapValuesWithKey
    (actors :
      DTR.GlobalMultiStorePayloadActors) :
    Translation.compileGlobalMultiStorePayloadActors
        actors =
      Store.mapValuesWithKey
        (fun _ model =>
          Translation.translateMultiStorePayloadCore
            model)
        actors := by

  induction actors with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨actorName, model⟩

      simp [
        Translation.compileGlobalMultiStorePayloadActors,
        Store.mapValuesWithKey,
        inductionHypothesis
      ]

theorem translatedActorEntryCheck
    (actorName :
      ActorName)
    (model :
      DTR.MultiStorePayloadModel) :
    (
      (
        actorName ==
          (Translation.translateMultiStorePayloadCore
            model).reactorInstance.name
      ) &&
      (
        (Translation.translateMultiStorePayloadCore
          model).reactor.name ==
        (Translation.translateMultiStorePayloadCore
          model).reactorInstance.reactorName
      )
    ) =
    (
      (
        actorName ==
          model.actor.name
      ) &&
      (
        model.actor.className ==
          model.reactiveClass.name
      )
    ) := by

  have stringBEqComm
      (left right :
        String) :
      (left == right) =
        (right == left) := by

    cases hForward :
        (left == right) <;>
      cases hBackward :
        (right == left) <;>
        simp_all

  change
    (
      (
        actorName ==
          model.actor.name
      ) &&
      (
        model.reactiveClass.name.value ==
          model.actor.className.value
      )
    ) =
    (
      (
        actorName ==
          model.actor.name
      ) &&
      (
        model.actor.className.value ==
          model.reactiveClass.name.value
      )
    )

  rw [
    stringBEqComm
  ]

theorem actorProgramsMatchKeys_compileGlobalMultiStorePayloadActors
    (actors :
      DTR.GlobalMultiStorePayloadActors) :
    LF.GlobalMultiStorePayloadProgram.actorProgramsMatchKeys
        (Translation.compileGlobalMultiStorePayloadActors
          actors) =
      DTR.GlobalMultiStorePayloadModel.actorsMatchKeysAndClasses
        actors := by

  induction actors with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨actorName, model⟩

      change
        (
          (
            (
              actorName ==
                (Translation.translateMultiStorePayloadCore
                  model).reactorInstance.name
            ) &&
            (
              (Translation.translateMultiStorePayloadCore
                model).reactor.name ==
              (Translation.translateMultiStorePayloadCore
                model).reactorInstance.reactorName
            )
          ) &&
          LF.GlobalMultiStorePayloadProgram.actorProgramsMatchKeys
            (Translation.compileGlobalMultiStorePayloadActors
              remaining)
        ) =
        (
          (
            (
              actorName ==
                model.actor.name
            ) &&
            (
              model.actor.className ==
                model.reactiveClass.name
            )
          ) &&
          DTR.GlobalMultiStorePayloadModel.actorsMatchKeysAndClasses
            remaining
        )

      rw [
        translatedActorEntryCheck,
        inductionHypothesis
      ]

theorem translateGlobalMultiStorePayloadCore_wellFormed_eq
    (model :
      DTR.GlobalMultiStorePayloadModel) :
    LF.GlobalMultiStorePayloadProgram.wellFormed
        (Translation.translateGlobalMultiStorePayloadCore
          model) =
      DTR.GlobalMultiStorePayloadModel.wellFormed
        model := by

  change
    (
      ActorTopology.wellFormed
          (Translation.compileGlobalMultiStorePayloadActors
            model.actors)
          model.topology &&
        LF.GlobalMultiStorePayloadProgram.actorProgramsMatchKeys
          (Translation.compileGlobalMultiStorePayloadActors
            model.actors)
    ) =
    (
      ActorTopology.wellFormed
          model.actors
          model.topology &&
        DTR.GlobalMultiStorePayloadModel.actorsMatchKeysAndClasses
          model.actors
    )

  rw [
    compileGlobalMultiStorePayloadActors_eq_mapValuesWithKey
  ]

  rw [
    ActorTopology.wellFormed_mapValuesWithKey
  ]

  rw [
    ←
      compileGlobalMultiStorePayloadActors_eq_mapValuesWithKey
        model.actors
  ]

  rw [
    actorProgramsMatchKeys_compileGlobalMultiStorePayloadActors
  ]

theorem translateGlobalMultiStorePayloadCore_wellFormed
    {model :
      DTR.GlobalMultiStorePayloadModel}
    (hWellFormed :
      DTR.GlobalMultiStorePayloadModel.wellFormed
          model =
        true) :
    LF.GlobalMultiStorePayloadProgram.wellFormed
        (Translation.translateGlobalMultiStorePayloadCore
          model) =
      true := by

  rw [
    translateGlobalMultiStorePayloadCore_wellFormed_eq,
    hWellFormed
  ]

theorem translateGlobalMultiStorePayloadCore_resolve
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (sender :
      ActorName)
    (knownRebec :
      KnownRebecName) :
    ActorTopology.resolve
        (Translation.translateGlobalMultiStorePayloadCore
          model).topology
        sender
        knownRebec =
      ActorTopology.resolve
        model.topology
        sender
        knownRebec := by
  rfl

/--
Strong static correspondence for the structural E2 translation.
-/
structure GlobalMultiStorePayloadStaticCorresponds
    (source :
      DTR.GlobalMultiStorePayloadModel)
    (target :
      LF.GlobalMultiStorePayloadProgram) :
    Prop where

  compiledActorPrograms :
    target.actorPrograms =
      Translation.compileGlobalMultiStorePayloadActors
        source.actors

  actorKeys :
    Store.keys target.actorPrograms =
      Store.keys source.actors

  topology :
    target.topology =
      source.topology

  topologyResolution :
    ∀
      (sender :
        ActorName)
      (knownRebec :
        KnownRebecName),

      ActorTopology.resolve
          target.topology
          sender
          knownRebec =
        ActorTopology.resolve
          source.topology
          sender
          knownRebec

  wellFormed :
    LF.GlobalMultiStorePayloadProgram.wellFormed
        target =
      DTR.GlobalMultiStorePayloadModel.wellFormed
        source

theorem translateGlobalMultiStorePayloadCore_staticCorresponds
    (model :
      DTR.GlobalMultiStorePayloadModel) :
    GlobalMultiStorePayloadStaticCorresponds
      model
      (Translation.translateGlobalMultiStorePayloadCore
        model) := by

  refine {
    compiledActorPrograms := rfl
    actorKeys := ?_
    topology := rfl
    topologyResolution := ?_
    wellFormed := ?_
  }

  · exact
      Translation.translateGlobalMultiStorePayloadCore_actorKeys
        model

  · intro sender knownRebec

    exact
      translateGlobalMultiStorePayloadCore_resolve
        model
        sender
        knownRebec

  · exact
      translateGlobalMultiStorePayloadCore_wellFormed_eq
        model

/--
Aligned actor startup entries produce pointwise-related source and target
startup states.
-/
theorem globalMultiStorePayloadStartupActorStates_correspond
    {actors :
      DTR.GlobalMultiStorePayloadActors}
    {initialStores :
      DTR.GlobalMultiStorePayloadInitialStores}
    {entries :
      DTR.GlobalMultiStorePayloadStartupEntries}
    (hAlign :
      _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
          actors
          initialStores =
        some entries) :
    GlobalMultiStorePayloadActorStatesCorrespond
      actors
      (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupActorStates
          entries)
      (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupActorStates
          entries) := by

  induction actors generalizing
      initialStores
      entries with

  | nil =>
      cases initialStores with

      | nil =>
          simp [
            DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries,
            Store.zipValuesWithKey
          ] at hAlign

          subst entries

          exact
            .nil

      | cons head remaining =>
          simp [
            DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries,
            Store.zipValuesWithKey
          ] at hAlign

  | cons head remainingModels inductionHypothesis =>
      rcases head with
        ⟨actorName, model⟩

      cases initialStores with

      | nil =>
          simp [
            DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries,
            Store.zipValuesWithKey
          ] at hAlign

      | cons initialHead remainingInitialStores =>
          rcases initialHead with
            ⟨initialActorName, initialStore⟩

          by_cases hActorNames :
              actorName = initialActorName

          · subst initialActorName

            cases hRemaining :
                Store.zipValuesWithKey
                  (fun _ remainingModel remainingInitialStore =>
                    (
                      remainingModel,
                      remainingInitialStore
                    ))
                  remainingModels
                  remainingInitialStores with

            | none =>
                simp [
                  DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries,
                  Store.zipValuesWithKey,
                  hRemaining
                ] at hAlign

            | some remainingEntries =>
                simp [
                  DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries,
                  Store.zipValuesWithKey,
                  hRemaining
                ] at hAlign

                subst entries

                have hRemainingAlign :
                    _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
                          remainingModels
                          remainingInitialStores =
                      some remainingEntries := by

                  simpa [
                    DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
                  ] using
                    hRemaining

                have hTail :=
                  inductionHypothesis
                    hRemainingAlign

                simpa [
                  DTR.GlobalMultiStorePayloadInitialization.startupActorStates,
                  LF.GlobalMultiStorePayloadInitialization.startupActorStates,
                  Store.mapValuesWithKey
                ] using
                  GlobalMultiStorePayloadActorStatesCorrespond.cons
                    (multiStorePayloadStartupStates_correspond
                      model.reactiveClass.messageServers
                      model.reactiveClass.constructor
                      initialStore)
                    hTail

          · simp [
              DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries,
              Store.zipValuesWithKey,
              hActorNames
            ] at hAlign

/--
Global startup-state correspondence over one successfully aligned actor domain.
-/
theorem globalMultiStorePayloadStartupRuntime_correspond
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (initialStores :
      DTR.GlobalMultiStorePayloadInitialStores)
    (entries :
      DTR.GlobalMultiStorePayloadStartupEntries)
    (hAlign :
      _root_.Relico.DTR.GlobalMultiStorePayloadInitialization.alignStartupEntries
          model.actors
          initialStores =
        some entries) :
    GlobalMultiStorePayloadRuntimeStateCorresponds
      model
      (Translation.translateGlobalMultiStorePayloadCore
        model)
      (_root_.Relico.DTR.GlobalMultiStorePayloadInitialization.startupStateFromEntries
          entries)
      (_root_.Relico.LF.GlobalMultiStorePayloadInitialization.startupStateFromEntries
          entries) := by

  refine {
    compiledActorPrograms := rfl
    topology := rfl
    currentTime := rfl
    actorStates := ?_
  }

  exact
    globalMultiStorePayloadStartupActorStates_correspond
      hAlign

end Correctness
end Relico
