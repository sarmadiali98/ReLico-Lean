import Relico.Correctness.DetailedInitialFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedInitialFiniteWeakExecution

theorem initial_detailed_state_correspondence_interface
    (model : DTR.MultiStoreModel) :
    Correctness.ConcreteDetailedStateCorresponds
      model.reactiveClass.messageServers
      (.stable
        (DTR.MultiStoreModel.initialState
          model))
      (.stable
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            model))) := by

  exact
    Correctness.concreteDetailedInitialStates_correspond
      model

theorem initial_source_runtime_invariant_interface
    (model : DTR.MultiStoreModel)
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model)
    (hTiming :
      DTR.MultiStoreModel.PriorityTimingWellFormed
        model) :
    Correctness.ConcreteDetailedSourceRuntimeInvariant
      (DTR.stateVariableNames
        model.reactiveClass.stateVariables)
      model.reactiveClass.messageServers
      (.stable
        (DTR.MultiStoreModel.initialState
          model)) := by

  exact
    Correctness.concreteDetailedInitialSourceRuntimeInvariant
      model
      hModel
      hTiming

theorem initial_target_runtime_invariant_interface
    (model : DTR.MultiStoreModel) :
    Correctness.ConcreteDetailedTargetRuntimeInvariant
      model.reactiveClass.messageServers
      (.stable
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            model))) := by

  exact
    Correctness.concreteDetailedInitialTargetRuntimeInvariant
      model

theorem forward_from_initial_interface
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
        Correctness.ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        Correctness.ConcreteDetailedStateCorresponds
          model.reactiveClass.messageServers
          sourceAfter
          targetAfter ∧
        Correctness.ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) ∧
        Correctness.ConcreteDetailedSourceRuntimeInvariant
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServers
          sourceAfter ∧
        Correctness.ConcreteDetailedTargetRuntimeInvariant
          model.reactiveClass.messageServers
          targetAfter := by

  exact
    Correctness.concreteDetailedSteps_forward_from_initial
      hSourceSteps
      hModel
      hTiming

theorem backward_from_initial_interface
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
        Correctness.ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        Correctness.ConcreteDetailedStateCorresponds
          model.reactiveClass.messageServers
          sourceAfter
          targetAfter ∧
        Correctness.ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) ∧
        Correctness.ConcreteDetailedSourceRuntimeInvariant
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServers
          sourceAfter ∧
        Correctness.ConcreteDetailedTargetRuntimeInvariant
          model.reactiveClass.messageServers
          targetAfter := by

  exact
    Correctness.concreteDetailedSteps_backward_from_initial
      hTargetSteps
      hModel
      hTiming

end DetailedInitialFiniteWeakExecution
end Tests
end Relico
