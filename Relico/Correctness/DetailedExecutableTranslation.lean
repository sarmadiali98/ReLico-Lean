import Relico.Correctness.DetailedInitialFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Finite detailed forward correctness for the program returned by the public
executable multi-store translator.

For every exact finite DTR detailed execution from constructor entry, the
returned generated-LF program has a corresponding finite weak execution from
startup entry.

The representative labels, observable traces, final detailed states, and final
runtime invariants correspond.
-/
theorem translateMultiStore_initialDetailedSteps_forward
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

  have hProgram :
      Translation.translateMultiStoreCore
          model =
        program := by

    simpa [
      Translation.translateMultiStore
    ] using
      hTranslate

  subst program

  exact
    concreteDetailedSteps_forward_from_initial
      hSourceSteps
      hModel
      hTiming

/--
Finite detailed backward correctness for the program returned by the public
executable multi-store translator.

For every exact finite generated-LF detailed execution from startup entry,
there is a corresponding finite DTR weak execution from constructor entry.

The representative labels, observable traces, final detailed states, and final
runtime invariants correspond.
-/
theorem translateMultiStore_initialDetailedSteps_backward
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

  have hProgram :
      Translation.translateMultiStoreCore
          model =
        program := by

    simpa [
      Translation.translateMultiStore
    ] using
      hTranslate

  subst program

  exact
    concreteDetailedSteps_backward_from_initial
      hTargetSteps
      hModel
      hTiming

end Correctness
end Relico
