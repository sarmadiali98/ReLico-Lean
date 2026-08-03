import Relico.Translation.GlobalMultiStorePayloadActorOrder

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Relico
namespace Correctness
namespace GlobalMultiStorePayloadActorSelectionCorrespondence

open DTR.GlobalMultiStorePayloadActorPriority
open LF.GlobalMultiStorePayloadActorOrder
open Translation.GlobalMultiStorePayloadActorOrder


theorem lookupActorOrder_compileActorPriorityAssignment_eq
    (assignment : ActorPriorityAssignment)
    (actorName : ActorName) :
    lookupActorOrder
        (compileActorPriorityAssignment assignment)
        actorName =
      lookupPriority assignment actorName := by

  induction assignment with

  | nil =>
      simp [
        compileActorPriorityAssignment,
        lookupActorOrder,
        lookupPriority
      ]

  | cons head tail inductionHypothesis =>
      rcases head with
        ⟨candidateName, candidatePriority⟩

      simp [
        compileActorPriorityAssignment,
        lookupActorOrder,
        lookupPriority,
        inductionHypothesis
      ]

theorem lookupReadyTargetActor_compileReadyActors_eq
    (ready : List ReadyActor)
    (actorName : ActorName) :
    lookupReadyTargetActor
        (compileReadyActors ready)
        actorName =
      Option.map
        compileReadyActor
        (lookupReadyActor ready actorName) := by

  induction ready with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      rcases head with
        ⟨candidateName, candidateTime⟩

      by_cases namesEqual :
          candidateName = actorName

      · simp [
          compileReadyActor,
          compileReadyActors,
          lookupReadyTargetActor,
          lookupReadyActor,
          namesEqual
        ]

      · simp [
          compileReadyActor,
          compileReadyActors,
          lookupReadyTargetActor,
          lookupReadyActor,
          namesEqual,
          inductionHypothesis
        ]

theorem all_compileReadyActors_eq
    (ready : List ReadyActor)
    (targetPredicate : ReadyTargetActor → Bool)
    (sourcePredicate : ReadyActor → Bool)
    (pointwise :
      ∀ candidate,
        targetPredicate
            (compileReadyActor candidate) =
          sourcePredicate candidate) :
    (compileReadyActors ready).all
        targetPredicate =
      ready.all sourcePredicate := by

  induction ready with

  | nil =>
      simp [
        compileReadyActors
      ]

  | cons head tail inductionHypothesis =>
      simp [
        compileReadyActors,
        pointwise,
        inductionHypothesis
      ]

theorem targetEarliestReady_compileReadyActors_eq
    (ready : List ReadyActor)
    (selected : ReadyActor) :
    targetEarliestReady
        (compileReadyActors ready)
        (compileReadyActor selected) =
      earliestReady ready selected := by

  unfold targetEarliestReady
  unfold earliestReady

  apply all_compileReadyActors_eq

  intro candidate

  simp [
    compileReadyActor
  ]


theorem filter_compileReadyActors_eq
    (ready : List ReadyActor)
    (targetPredicate : ReadyTargetActor → Bool)
    (sourcePredicate : ReadyActor → Bool)
    (pointwise :
      ∀ candidate,
        targetPredicate
            (compileReadyActor candidate) =
          sourcePredicate candidate) :
    List.filter
        targetPredicate
        (compileReadyActors ready) =
      compileReadyActors
        (List.filter sourcePredicate ready) := by

  induction ready with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      cases predicateValue :
          sourcePredicate head <;>
        simp [
          compileReadyActors,
          pointwise,
          predicateValue,
          inductionHypothesis
        ]

theorem sameTimeReadyTargetActors_compileReadyActors_eq
    (ready : List ReadyActor)
    (selected : ReadyActor) :
    sameTimeReadyTargetActors
        (compileReadyActors ready)
        (compileReadyActor selected) =
      compileReadyActors
        (sameTimeReadyActors ready selected) := by

  unfold sameTimeReadyTargetActors
  unfold sameTimeReadyActors

  apply filter_compileReadyActors_eq

  intro candidate

  rfl


theorem targetOrderCoversReadyActors_compile_eq
    (assignment : ActorPriorityAssignment)
    (ready : List ReadyActor)
    (selected : ReadyActor) :
    targetOrderCoversReadyActors
        (compileActorPriorityAssignment assignment)
        (compileReadyActors ready)
        (compileReadyActor selected) =
      requestCoversReadyActors
        assignment
        ready
        selected := by

  unfold targetOrderCoversReadyActors
  unfold requestCoversReadyActors

  rw [
    sameTimeReadyTargetActors_compileReadyActors_eq
  ]

  apply all_compileReadyActors_eq

  intro candidate

  simp [
    compileReadyActor,
    lookupActorOrder_compileActorPriorityAssignment_eq
  ]


theorem selectedHasMinimalActorOrder_compile_eq
    (assignment : ActorPriorityAssignment)
    (ready : List ReadyActor)
    (selected : ReadyActor) :
    selectedHasMinimalActorOrder
        (compileActorPriorityAssignment assignment)
        (compileReadyActors ready)
        (compileReadyActor selected) =
      selectedHasMinimalPriority
        assignment
        ready
        selected := by

  unfold selectedHasMinimalActorOrder
  unfold selectedHasMinimalPriority

  simp only [
    compileReadyActor_actorName,
    lookupActorOrder_compileActorPriorityAssignment_eq
  ]

  rw [
    sameTimeReadyTargetActors_compileReadyActors_eq
  ]

  cases selectedLookup :
      lookupPriority
        assignment
        selected.actorName with

  | none =>
      simp [
        selectedLookup
      ]

  | some selectedPriority =>
      simp only [
        selectedLookup
      ]

      generalize
        sameTimeReadyActors ready selected =
          candidates

      induction candidates with

      | nil =>
          rfl

      | cons head tail inductionHypothesis =>
          rcases head with
            ⟨candidateName, candidateTime⟩

          cases candidateLookup :
              lookupPriority
                assignment
                candidateName <;>
            simp [
              compileReadyActor,
              compileReadyActors,
              lookupActorOrder_compileActorPriorityAssignment_eq,
              candidateLookup,
              inductionHypothesis
            ]


theorem actorSelectionEligibleBool_compile_eq
    (request : ActorPriorityRequest)
    (ready : List ReadyActor)
    (actorName : ActorName) :
    actorPriorityEligibleBool
        request
        ready
        actorName =
      targetActorOrderEligibleBool
        (compileActorPriorityRequest request)
        (compileReadyActors ready)
        actorName := by

  unfold actorPriorityEligibleBool
  unfold targetActorOrderEligibleBool

  rw [
    lookupReadyTargetActor_compileReadyActors_eq
  ]

  cases sourceLookup :
      lookupReadyActor ready actorName with

  | none =>
      simp [
        sourceLookup
      ]

  | some selected =>
      simp only [
        sourceLookup,
        Option.map_some
      ]

      rw [
        targetEarliestReady_compileReadyActors_eq
      ]

      cases request with

      | none =>
          rfl

      | some assignment =>
          simp only [
            compileActorPriorityRequest
          ]

          rw [
            targetOrderCoversReadyActors_compile_eq,
            selectedHasMinimalActorOrder_compile_eq
          ]

theorem actorSelectionEligible_compile_iff
    (request : ActorPriorityRequest)
    (ready : List ReadyActor)
    (actorName : ActorName) :
    ActorPriorityEligible
        request
        ready
        actorName ↔
      TargetActorOrderEligible
        (compileActorPriorityRequest request)
        (compileReadyActors ready)
        actorName := by

  change
    (
      actorPriorityEligibleBool
          request
          ready
          actorName =
        true
    ) ↔
      (
        targetActorOrderEligibleBool
            (compileActorPriorityRequest request)
            (compileReadyActors ready)
            actorName =
          true
      )

  rw [
    actorSelectionEligibleBool_compile_eq
  ]

theorem actorSelectionEligible_forward
    (request : ActorPriorityRequest)
    (ready : List ReadyActor)
    (actorName : ActorName) :
    ActorPriorityEligible
        request
        ready
        actorName →
      TargetActorOrderEligible
        (compileActorPriorityRequest request)
        (compileReadyActors ready)
        actorName :=
  (
    actorSelectionEligible_compile_iff
      request
      ready
      actorName
  ).mp

theorem actorSelectionEligible_backward
    (request : ActorPriorityRequest)
    (ready : List ReadyActor)
    (actorName : ActorName) :
    TargetActorOrderEligible
        (compileActorPriorityRequest request)
        (compileReadyActors ready)
        actorName →
      ActorPriorityEligible
        request
        ready
        actorName :=
  (
    actorSelectionEligible_compile_iff
      request
      ready
      actorName
  ).mpr


theorem eligibleActorNames_compile_eq
    (request : ActorPriorityRequest)
    (ready : List ReadyActor) :
    eligibleActorNames
        request
        ready =
      eligibleTargetActorNames
        (compileActorPriorityRequest request)
        (compileReadyActors ready) := by

  unfold eligibleActorNames
  unfold eligibleTargetActorNames

  let sourcePredicate :
      ReadyActor → Bool :=
    fun candidate =>
      actorPriorityEligibleBool
        request
        ready
        candidate.actorName

  let targetPredicate :
      ReadyTargetActor → Bool :=
    fun candidate =>
      targetActorOrderEligibleBool
        (compileActorPriorityRequest request)
        (compileReadyActors ready)
        candidate.actorName

  have pointwise :
      ∀ candidate,
        targetPredicate
            (compileReadyActor candidate) =
          sourcePredicate candidate := by

    intro candidate

    dsimp [
      sourcePredicate,
      targetPredicate
    ]

    simpa [
      compileReadyActor_actorName
    ] using
      (
        actorSelectionEligibleBool_compile_eq
          request
          ready
          candidate.actorName
      ).symm

  have filteredEquality :
      List.filter
          targetPredicate
          (compileReadyActors ready) =
        compileReadyActors
          (
            List.filter
              sourcePredicate
              ready
          ) :=
    filter_compileReadyActors_eq
      ready
      targetPredicate
      sourcePredicate
      pointwise

  rw [
    filteredEquality
  ]

  simpa [
    sourcePredicate,
    targetPredicate
  ] using
    (
      compileReadyActors_actorNames
        (
          List.filter
            sourcePredicate
            ready
        )
    ).symm


end GlobalMultiStorePayloadActorSelectionCorrespondence
end Correctness
end Relico
