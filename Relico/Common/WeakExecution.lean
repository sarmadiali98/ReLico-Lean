import Relico.Common.WeakTransition

set_option autoImplicit false

namespace Relico
namespace Common

universe u v w

/--
A finite sequence of weak transitions.

The labels record the representative labels of the weak transitions.
Internal prefixes and suffixes contained inside each weak transition are not
added to this list.
-/
inductive WeakSteps
    {State : Type u}
    {Label : Type v}
    (step : LabeledTransition State Label)
    (isTau : Label → Prop) :
    State →
    List Label →
    State →
    Prop where

  | refl
      (state : State) :
      WeakSteps
        step
        isTau
        state
        []
        state

  | cons
      {before middle after : State}
      {label : Label}
      {remainingLabels : List Label}
      (headStep :
        WeakStep
          step
          isTau
          before
          label
          middle)
      (remainingSteps :
        WeakSteps
          step
          isTau
          middle
          remainingLabels
          after) :
      WeakSteps
        step
        isTau
        before
        (label :: remainingLabels)
        after

namespace WeakSteps

variable
    {State : Type u}
    {Label : Type v}
    {step : LabeledTransition State Label}
    {isTau : Label → Prop}

/--
One weak transition induces a singleton finite weak execution.
-/
theorem single
    {source target : State}
    {label : Label}
    (hStep :
      WeakStep
        step
        isTau
        source
        label
        target) :
    WeakSteps
      step
      isTau
      source
      [label]
      target := by

  exact
    WeakSteps.cons
      hStep
      (WeakSteps.refl target)

/--
Finite weak executions compose by concatenating their representative-label
lists.
-/
theorem append
    {source middle target : State}
    {leftLabels rightLabels : List Label}
    (left :
      WeakSteps
        step
        isTau
        source
        leftLabels
        middle)
    (right :
      WeakSteps
        step
        isTau
        middle
        rightLabels
        target) :
    WeakSteps
      step
      isTau
      source
      (leftLabels ++ rightLabels)
      target := by

  induction left with

  | refl state =>
      simpa using right

  | cons headStep remainingSteps inductionHypothesis =>
      exact
        WeakSteps.cons
          headStep
          (inductionHypothesis right)

end WeakSteps

/--
Observable projection distributes over trace concatenation.
-/
@[simp]
theorem observableProjection_append
    {Label : Type v}
    {Observable : Type w}
    (project : Label → Option Observable)
    (left right : List Label) :
    observableProjection
        project
        (left ++ right) =
      observableProjection
          project
          left ++
        observableProjection
          project
          right := by

  simp [observableProjection]

end Common
end Relico
