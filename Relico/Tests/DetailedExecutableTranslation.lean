import Relico.Correctness.DetailedExecutableTranslation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedExecutableTranslation

theorem public_detailed_forward_interface
    {model : DTR.MultiStoreModel}
    {program : LF.MultiStoreProgram}
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {sourceAfter :
      DTR.DetailedMultiStoreState
        model.reactiveClass.messageServers}
    (hTranslate :
      Translation.translateMultiStore model =
        .ok program)
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
              program))
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
    Correctness.translateMultiStore_initialDetailedSteps_forward
      hTranslate
      hSourceSteps
      hModel
      hTiming

theorem public_detailed_backward_interface
    {model : DTR.MultiStoreModel}
    {program : LF.MultiStoreProgram}
    (hTranslate :
      Translation.translateMultiStore model =
        .ok program)
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
            program))
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
    Correctness.translateMultiStore_initialDetailedSteps_backward
      hTranslate
      hTargetSteps
      hModel
      hTiming

end DetailedExecutableTranslation
end Tests
end Relico
