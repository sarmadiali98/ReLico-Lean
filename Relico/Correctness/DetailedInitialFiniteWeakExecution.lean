import Relico.Correctness.DetailedInvariantCarryingFiniteWeakExecution
import Relico.Correctness.MultiStoreInitialization
import Relico.DTR.PriorityTimingWellFormed

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
The source model and its executable generated-LF program begin in corresponding
stable detailed states.
-/
theorem concreteDetailedInitialStates_correspond
    (model : DTR.MultiStoreModel) :
    ConcreteDetailedStateCorresponds
      model.reactiveClass.messageServers
      (.stable
        (DTR.MultiStoreModel.initialState
          model))
      (.stable
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            model))) := by

  exact
    DetailedStateCorresponds.stable
      (translateMultiStoreCore_initialStates_correspond
        model)

/--
A structurally well-formed source model satisfying the priority timing
restriction begins in the canonical detailed source runtime invariant.
-/
theorem concreteDetailedInitialSourceRuntimeInvariant
    (model : DTR.MultiStoreModel)
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model)
    (hTiming :
      DTR.MultiStoreModel.PriorityTimingWellFormed
        model) :
    ConcreteDetailedSourceRuntimeInvariant
      (DTR.stateVariableNames
        model.reactiveClass.stateVariables)
      model.reactiveClass.messageServers
      (.stable
        (DTR.MultiStoreModel.initialState
          model)) := by

  exact
    ⟨DTR.MultiStoreModel.initialState_runtimeWellFormed
        model
        hModel,
     hTiming.constructorBody⟩

/--
Every executable generated-LF multi-store program begins in the canonical
detailed target runtime invariant.
-/
theorem concreteDetailedInitialTargetRuntimeInvariant
    (model : DTR.MultiStoreModel) :
    ConcreteDetailedTargetRuntimeInvariant
      model.reactiveClass.messageServers
      (.stable
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            model))) := by

  exact
    LF.MultiStoreProgram.initialState_priorityRuntimeInvariant
      (Translation.translateMultiStoreCore
        model)

/--
Finite forward weak execution correspondence from the canonical translated
initial states.

Initial state correspondence and both initial runtime invariants are discharged
from model construction, structural well-formedness, and the model-level
positive-delay priority timing assumption.
-/
theorem concreteDetailedSteps_forward_from_initial
    {model : DTR.MultiStoreModel}
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {sourceAfter :
      DTR.DetailedMultiStoreState
        model.reactiveClass.messageServers}
    (hSourceSteps :
      DTR.DetailedMultiStoreSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServers
        (.stable
          (DTR.MultiStoreModel.initialState
            model))
        sourceLabels
        sourceAfter)
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model)
    (hTiming :
      DTR.MultiStoreModel.PriorityTimingWellFormed
        model) :
    ∃ targetLabels targetAfter,
      LF.DetailedWeakSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          (Translation.compileLogicalActions
            model.reactiveClass.messageServers)
          (Translation.compileMessageReactions
            model.reactiveClass.messageServers)
          (.stable
            (LF.MultiStoreProgram.initialState
              (Translation.translateMultiStoreCore
                model)))
          targetLabels
          targetAfter ∧
        ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        ConcreteDetailedStateCorresponds
          model.reactiveClass.messageServers
          sourceAfter
          targetAfter ∧
        ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) ∧
        ConcreteDetailedSourceRuntimeInvariant
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServers
          sourceAfter ∧
        ConcreteDetailedTargetRuntimeInvariant
          model.reactiveClass.messageServers
          targetAfter := by

  exact
    concreteDetailedSteps_forward_chosen
      hSourceSteps
      (concreteDetailedInitialStates_correspond
        model)
      (concreteDetailedInitialSourceRuntimeInvariant
        model
        hModel
        hTiming)
      (concreteDetailedInitialTargetRuntimeInvariant
        model)
      hModel.messageServerBodiesWellFormed
      hTiming.messageServerBodies

/--
Finite backward weak execution correspondence from the canonical translated
initial states.

The selected source execution begins at the DTR constructor-entry state. The
result carries final state correspondence, observable-trace correspondence, and
both destination runtime invariants.
-/
theorem concreteDetailedSteps_backward_from_initial
    {model : DTR.MultiStoreModel}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    {targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          model.reactiveClass.messageServers)}
    (hTargetSteps :
      LF.DetailedMultiStoreSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        (Translation.compileLogicalActions
          model.reactiveClass.messageServers)
        (Translation.compileMessageReactions
          model.reactiveClass.messageServers)
        (.stable
          (LF.MultiStoreProgram.initialState
            (Translation.translateMultiStoreCore
              model)))
        targetLabels
        targetAfter)
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model)
    (hTiming :
      DTR.MultiStoreModel.PriorityTimingWellFormed
        model) :
    ∃ sourceLabels sourceAfter,
      DTR.DetailedWeakSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServers
          (.stable
            (DTR.MultiStoreModel.initialState
              model))
          sourceLabels
          sourceAfter ∧
        ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        ConcreteDetailedStateCorresponds
          model.reactiveClass.messageServers
          sourceAfter
          targetAfter ∧
        ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) ∧
        ConcreteDetailedSourceRuntimeInvariant
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServers
          sourceAfter ∧
        ConcreteDetailedTargetRuntimeInvariant
          model.reactiveClass.messageServers
          targetAfter := by

  exact
    concreteDetailedSteps_backward_chosen
      hTargetSteps
      (concreteDetailedInitialStates_correspond
        model)
      (concreteDetailedInitialSourceRuntimeInvariant
        model
        hModel
        hTiming)
      (concreteDetailedInitialTargetRuntimeInvariant
        model)
      hModel.messageServerBodiesWellFormed
      hTiming.messageServerBodies

end Correctness
end Relico
