import Std

set_option autoImplicit false

namespace Relico
namespace Common

universe u v w

/--
A labeled transition relation over states and transition labels.
-/
abbrev LabeledTransition
    (State : Type u)
    (Label : Type v) :=
  State →
  Label →
  State →
  Prop

/--
The reflexive-transitive closure of transitions whose labels satisfy
`isTau`.

A `TauSteps step isTau source target` derivation represents zero or more
internal transitions from `source` to `target`.
-/
inductive TauSteps
    {State : Type u}
    {Label : Type v}
    (step : LabeledTransition State Label)
    (isTau : Label → Prop) :
    State →
    State →
    Prop where

  | refl
      (state : State) :
      TauSteps
        step
        isTau
        state
        state

  | cons
      {source middle target : State}
      {label : Label}
      (headStep :
        step
          source
          label
          middle)
      (headIsTau :
        isTau label)
      (remainingSteps :
        TauSteps
          step
          isTau
          middle
          target) :
      TauSteps
        step
        isTau
        source
        target

namespace TauSteps

variable
    {State : Type u}
    {Label : Type v}
    {step : LabeledTransition State Label}
    {isTau : Label → Prop}

/--
One internal transition induces a `TauSteps` derivation.
-/
theorem single
    {source target : State}
    {label : Label}
    (hStep :
      step
        source
        label
        target)
    (hTau :
      isTau label) :
    TauSteps
      step
      isTau
      source
      target := by

  exact
    TauSteps.cons
      hStep
      hTau
      (TauSteps.refl target)

/--
Internal transition closure is transitive.
-/
theorem trans
    {source middle target : State}
    (left :
      TauSteps
        step
        isTau
        source
        middle)
    (right :
      TauSteps
        step
        isTau
        middle
        target) :
    TauSteps
      step
      isTau
      source
      target := by

  induction left generalizing target with

  | refl state =>
      exact right

  | cons headStep headIsTau remainingSteps inductionHypothesis =>
      exact
        TauSteps.cons
          headStep
          headIsTau
          (inductionHypothesis right)

end TauSteps

/--
A weak internal transition consists of zero or more internal transitions.
-/
abbrev WeakTauStep
    {State : Type u}
    {Label : Type v}
    (step : LabeledTransition State Label)
    (isTau : Label → Prop)
    (source target : State) :
    Prop :=
  TauSteps
    step
    isTau
    source
    target

/--
A weak labeled transition.

For an internal label, zero or more internal transitions are sufficient.

For a visible label, the transition consists of:

1. an internal prefix;
2. one transition carrying the visible label;
3. an internal suffix.
-/
inductive WeakStep
    {State : Type u}
    {Label : Type v}
    (step : LabeledTransition State Label)
    (isTau : Label → Prop) :
    State →
    Label →
    State →
    Prop where

  | tau
      {source target : State}
      {label : Label}
      (hTau :
        isTau label)
      (hSteps :
        TauSteps
          step
          isTau
          source
          target) :
      WeakStep
        step
        isTau
        source
        label
        target

  | visible
      {source before after target : State}
      {label : Label}
      (hVisible :
        ¬ isTau label)
      (hPrefix :
        TauSteps
          step
          isTau
          source
          before)
      (hStep :
        step
          before
          label
          after)
      (hSuffix :
        TauSteps
          step
          isTau
          after
          target) :
      WeakStep
        step
        isTau
        source
        label
        target

namespace WeakStep

variable
    {State : Type u}
    {Label : Type v}
    {step : LabeledTransition State Label}
    {isTau : Label → Prop}

/--
An internal closure induces a weak transition carrying any internal label.
-/
theorem of_tauSteps
    {source target : State}
    {label : Label}
    (hTau :
      isTau label)
    (hSteps :
      TauSteps
        step
        isTau
        source
        target) :
    WeakStep
      step
      isTau
      source
      label
      target := by

  exact
    WeakStep.tau
      hTau
      hSteps

/--
Every exact transition induces a weak transition.
-/
theorem of_step
    {source target : State}
    {label : Label}
    (hStep :
      step
        source
        label
        target) :
    WeakStep
      step
      isTau
      source
      label
      target := by

  classical

  by_cases hTau :
      isTau label

  · exact
      WeakStep.tau
        hTau
        (TauSteps.single
          hStep
          hTau)

  · exact
      WeakStep.visible
        hTau
        (TauSteps.refl source)
        hStep
        (TauSteps.refl target)

/--
An internal label admits a reflexive weak transition.
-/
theorem tau_refl
    {state : State}
    {label : Label}
    (hTau :
      isTau label) :
    WeakStep
      step
      isTau
      state
      label
      state := by

  exact
    WeakStep.tau
      hTau
      (TauSteps.refl state)

end WeakStep

/--
Project a raw transition-label trace onto an observable alphabet.

Returning `none` removes an internal or administrative label. Returning
`some observable` retains the corresponding observable event.
-/
def observableProjection
    {Label : Type v}
    {Observable : Type w}
    (project :
      Label →
      Option Observable)
    (trace :
      List Label) :
    List Observable :=
  List.filterMap
    project
    trace

@[simp]
theorem observableProjection_nil
    {Label : Type v}
    {Observable : Type w}
    (project :
      Label →
      Option Observable) :
    observableProjection
        project
        [] =
      [] := by

  rfl

@[simp]
theorem observableProjection_cons_none
    {Label : Type v}
    {Observable : Type w}
    (project :
      Label →
      Option Observable)
    (label : Label)
    (remaining :
      List Label)
    (hProject :
      project label =
        none) :
    observableProjection
        project
        (label :: remaining) =
      observableProjection
        project
        remaining := by

  simp [
    observableProjection,
    hProject
  ]

@[simp]
theorem observableProjection_cons_some
    {Label : Type v}
    {Observable : Type w}
    (project :
      Label →
      Option Observable)
    (label : Label)
    (observable : Observable)
    (remaining :
      List Label)
    (hProject :
      project label =
        some observable) :
    observableProjection
        project
        (label :: remaining) =
      observable ::
        observableProjection
          project
          remaining := by

  simp [
    observableProjection,
    hProject
  ]

end Common
end Relico
