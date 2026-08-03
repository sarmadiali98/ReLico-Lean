import Relico.Investigation.ActorPriority.IsolatedScheduler

set_option autoImplicit false

namespace Relico.Investigation.ActorPriority

theorem faithfulTranslationMustDistinguishSources
    {Source Target Observation : Type}
    (translate : Source → Target)
    (sourceObservation : Source → Observation)
    (targetObservation : Target → Observation)
    (left right : Source)
    (hDifferent :
      sourceObservation left ≠
        sourceObservation right)
    (hLeft :
      targetObservation (translate left) =
        sourceObservation left)
    (hRight :
      targetObservation (translate right) =
        sourceObservation right) :
    translate left ≠ translate right := by
  intro hSame
  apply hDifferent
  calc
    sourceObservation left =
        targetObservation (translate left) :=
      hLeft.symm
    _ = targetObservation (translate right) := by
      rw [hSame]
    _ = sourceObservation right :=
      hRight

theorem erasingTranslationCannotPreserveBoth
    {Source Target Observation : Type}
    (translate : Source → Target)
    (sourceObservation : Source → Observation)
    (targetObservation : Target → Observation)
    (left right : Source)
    (hErases :
      translate left = translate right)
    (hDifferent :
      sourceObservation left ≠
        sourceObservation right) :
    ¬ (
      targetObservation (translate left) =
          sourceObservation left ∧
        targetObservation (translate right) =
          sourceObservation right
    ) := by
  intro hPreserves
  exact
    (faithfulTranslationMustDistinguishSources
      translate
      sourceObservation
      targetObservation
      left
      right
      hDifferent
      hPreserves.1
      hPreserves.2)
      hErases

abbrev ActorSelectionObservation :=
  List ActorName

def sourceActorSelectionObservation
    (ready : List ReadyActor)
    (request : ActorPriorityRequest) :
    ActorSelectionObservation :=
  sourceEligibleActorNames request ready

def PreservesActorSelection
    {Target : Type}
    (translate : ActorPriorityRequest → Target)
    (targetObservation :
      Target → ActorSelectionObservation)
    (ready : List ReadyActor)
    (request : ActorPriorityRequest) :
    Prop :=
  targetObservation (translate request) =
    sourceActorSelectionObservation ready request

theorem faithfulActorTranslationMustPreservePriorityDistinction
    {Target : Type}
    (translate : ActorPriorityRequest → Target)
    (targetObservation :
      Target → ActorSelectionObservation)
    (ready : List ReadyActor)
    (left right : ActorPriorityRequest)
    (hDifferent :
      sourceActorSelectionObservation ready left ≠
        sourceActorSelectionObservation ready right)
    (hLeft :
      PreservesActorSelection
        translate
        targetObservation
        ready
        left)
    (hRight :
      PreservesActorSelection
        translate
        targetObservation
        ready
        right) :
    translate left ≠ translate right := by
  exact
    faithfulTranslationMustDistinguishSources
      translate
      (sourceActorSelectionObservation ready)
      targetObservation
      left
      right
      hDifferent
      hLeft
      hRight

theorem actorPriorityErasureCannotPreserveDiscriminatingPair
    {Target : Type}
    (translate : ActorPriorityRequest → Target)
    (targetObservation :
      Target → ActorSelectionObservation)
    (ready : List ReadyActor)
    (left right : ActorPriorityRequest)
    (hErases :
      translate left = translate right)
    (hDifferent :
      sourceActorSelectionObservation ready left ≠
        sourceActorSelectionObservation ready right) :
    ¬ (
      PreservesActorSelection
          translate
          targetObservation
          ready
          left ∧
        PreservesActorSelection
          translate
          targetObservation
          ready
          right
    ) := by
  exact
    erasingTranslationCannotPreserveBoth
      translate
      (sourceActorSelectionObservation ready)
      targetObservation
      left
      right
      hErases
      hDifferent

def eraseActorPriorities :
    ActorPriorityRequest → Unit :=
  fun _ => ()

end Relico.Investigation.ActorPriority
