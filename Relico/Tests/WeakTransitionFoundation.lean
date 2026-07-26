import Relico.Common.WeakTransition

set_option autoImplicit false

namespace Relico
namespace Tests
namespace WeakTransitionFoundation

inductive ExampleLabel where
  | tau
  | visible
deriving Repr, DecidableEq, BEq, Inhabited

inductive ExampleStep :
    Nat →
    ExampleLabel →
    Nat →
    Prop where

  | tau
      (state : Nat) :
      ExampleStep
        state
        ExampleLabel.tau
        (state + 1)

  | visible
      (state : Nat) :
      ExampleStep
        state
        ExampleLabel.visible
        (state + 10)

def exampleIsTau :
    ExampleLabel →
    Prop

  | ExampleLabel.tau =>
      True

  | ExampleLabel.visible =>
      False

def exampleProject :
    ExampleLabel →
    Option ExampleLabel

  | ExampleLabel.tau =>
      none

  | ExampleLabel.visible =>
      some ExampleLabel.visible

theorem tauSteps_zero_two :
    Common.TauSteps
      ExampleStep
      exampleIsTau
      0
      2 := by

  exact
    Common.TauSteps.cons
      (ExampleStep.tau 0)
      True.intro
      (Common.TauSteps.cons
        (ExampleStep.tau 1)
        True.intro
        (Common.TauSteps.refl 2))

theorem tauSteps_zero_three :
    Common.TauSteps
      ExampleStep
      exampleIsTau
      0
      3 := by

  exact
    Common.TauSteps.trans
      tauSteps_zero_two
      (Common.TauSteps.single
        (ExampleStep.tau 2)
        True.intro)

theorem weakTauStep_zero_two :
    Common.WeakTauStep
      ExampleStep
      exampleIsTau
      0
      2 := by

  exact
    tauSteps_zero_two

theorem weakStep_visible_after_tau_prefix :
    Common.WeakStep
      ExampleStep
      exampleIsTau
      0
      ExampleLabel.visible
      12 := by

  exact
    Common.WeakStep.visible
      (by
        simp [
          exampleIsTau
        ])
      tauSteps_zero_two
      (ExampleStep.visible 2)
      (Common.TauSteps.refl 12)

theorem weakStep_tau_stutters :
    Common.WeakStep
      ExampleStep
      exampleIsTau
      0
      ExampleLabel.tau
      0 := by

  exact
    Common.WeakStep.tau_refl
      (step := ExampleStep)
      (isTau := exampleIsTau)
      True.intro

theorem exact_visible_step_is_weak :
    Common.WeakStep
      ExampleStep
      exampleIsTau
      3
      ExampleLabel.visible
      13 := by

  exact
    Common.WeakStep.of_step
      (isTau := exampleIsTau)
      (ExampleStep.visible 3)

theorem observableProjection_removes_tau :
    Common.observableProjection
        exampleProject
        [
          ExampleLabel.tau,
          ExampleLabel.visible,
          ExampleLabel.tau,
          ExampleLabel.visible
        ] =
      [
        ExampleLabel.visible,
        ExampleLabel.visible
      ] := by

  rfl

theorem observableProjection_internal_only_empty :
    Common.observableProjection
        exampleProject
        [
          ExampleLabel.tau,
          ExampleLabel.tau
        ] =
      [] := by

  rfl

end WeakTransitionFoundation
end Tests
end Relico
