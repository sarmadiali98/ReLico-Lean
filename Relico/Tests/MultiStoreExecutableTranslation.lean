import Relico.Correctness.MultiStoreExecutableTranslation
import Relico.Tests.MultiStoreInitialization

set_option autoImplicit false

namespace Relico
namespace Tests

theorem twoMessage_initial_refl_execution_forward :
    ∃ targetLabels targetAfter,
      LF.MultiStoreMachineSteps
          (DTR.stateVariableNames
            twoMessageModel.reactiveClass.stateVariables)
          (Translation.compileLogicalActions
            twoMessageModel.reactiveClass.messageServers)
          (Translation.compileMessageReactions
            twoMessageModel.reactiveClass.messageServers)
          (LF.MultiStoreProgram.initialState
            (Translation.translateMultiStoreCore
              twoMessageModel))
          targetLabels
          targetAfter ∧
      Correctness.MultiStoreMachineTraceCorresponds
        []
        targetLabels ∧
      Correctness.StoreStateCorresponds
        (DTR.MultiStoreModel.initialState
          twoMessageModel)
        targetAfter := by

  have hSourceSteps :
      DTR.MultiStoreMachineSteps
        (DTR.stateVariableNames
          twoMessageModel.reactiveClass.stateVariables)
        twoMessageModel.reactiveClass.messageServers
        (DTR.MultiStoreModel.initialState
          twoMessageModel)
        []
        (DTR.MultiStoreModel.initialState
          twoMessageModel) :=

    DTR.MultiStoreMachineSteps.refl
      _

  have hCompatible :
      Correctness.MultiStoreForwardMachineStepsCompatible
        (DTR.stateVariableNames
          twoMessageModel.reactiveClass.stateVariables)
        twoMessageModel.reactiveClass.messageServers
        hSourceSteps
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            twoMessageModel)) := by

    simp [
      Correctness.MultiStoreForwardMachineStepsCompatible,
      Correctness.MultiStoreForwardMachineLabelsCompatible
    ]

  exact
    Correctness.translateMultiStoreCore_initialMachineSteps_forward
      hSourceSteps
      hCompatible

theorem twoMessage_public_initial_refl_execution_forward :
    ∃ targetLabels targetAfter,
      LF.MultiStoreMachineSteps
          (DTR.stateVariableNames
            twoMessageModel.reactiveClass.stateVariables)
          (Translation.compileLogicalActions
            twoMessageModel.reactiveClass.messageServers)
          (Translation.compileMessageReactions
            twoMessageModel.reactiveClass.messageServers)
          (LF.MultiStoreProgram.initialState
            (Translation.translateMultiStoreCore
              twoMessageModel))
          targetLabels
          targetAfter ∧
      Correctness.MultiStoreMachineTraceCorresponds
        []
        targetLabels ∧
      Correctness.StoreStateCorresponds
        (DTR.MultiStoreModel.initialState
          twoMessageModel)
        targetAfter := by

  have hSourceSteps :
      DTR.MultiStoreMachineSteps
        (DTR.stateVariableNames
          twoMessageModel.reactiveClass.stateVariables)
        twoMessageModel.reactiveClass.messageServers
        (DTR.MultiStoreModel.initialState
          twoMessageModel)
        []
        (DTR.MultiStoreModel.initialState
          twoMessageModel) :=

    DTR.MultiStoreMachineSteps.refl
      _

  have hCompatible :
      Correctness.MultiStoreForwardMachineStepsCompatible
        (DTR.stateVariableNames
          twoMessageModel.reactiveClass.stateVariables)
        twoMessageModel.reactiveClass.messageServers
        hSourceSteps
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            twoMessageModel)) := by

    simp [
      Correctness.MultiStoreForwardMachineStepsCompatible,
      Correctness.MultiStoreForwardMachineLabelsCompatible
    ]

  exact
    Correctness.translateMultiStore_initialMachineSteps_forward
      (program :=
        Translation.translateMultiStoreCore
          twoMessageModel)
      (by rfl)
      hSourceSteps
      hCompatible

theorem twoMessageModel_priorityTimingWellFormed :
    DTR.MultiStoreModel.PriorityTimingWellFormed
      twoMessageModel := by

  exact {
    constructorBody := by
      simp [
        twoMessageModel,
        twoMessageReactiveClass,
        twoMessageConstructor,
        DTR.Body.PriorityTimingWellFormed,
        DTR.Stmt.PriorityTimingWellFormed
      ]

    messageServerBodies := by
      intro messageServer hMember

      have hConcreteMember :
          messageServer =
              tickMessageServer ∨
            messageServer =
              resetMessageServer := by

        simpa [
          twoMessageModel,
          twoMessageReactiveClass,
          twoMessageServers
        ] using
          hMember

      rcases hConcreteMember with
        rfl | rfl

      · simp [
          tickMessageServer,
          DTR.Body.PriorityTimingWellFormed,
          DTR.Stmt.PriorityTimingWellFormed
        ]

      · simp [
          resetMessageServer,
          DTR.Body.PriorityTimingWellFormed,
          DTR.Stmt.PriorityTimingWellFormed
        ]
  }

theorem twoMessage_initial_refl_execution_backward :
    ∃ sourceLabels sourceAfter,
      DTR.MultiStoreMachineSteps
          (DTR.stateVariableNames
            twoMessageModel.reactiveClass.stateVariables)
          twoMessageModel.reactiveClass.messageServers
          (DTR.MultiStoreModel.initialState
            twoMessageModel)
          sourceLabels
          sourceAfter ∧
      Correctness.MultiStoreMachineTraceCorresponds
        sourceLabels
        [] ∧
      Correctness.StoreStateCorresponds
        sourceAfter
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            twoMessageModel)) ∧
      DTR.StoreState.MultiStoreRuntimeWellFormed
        (DTR.stateVariableNames
          twoMessageModel.reactiveClass.stateVariables)
        twoMessageModel.reactiveClass.messageServers
        sourceAfter := by

  exact
    Correctness.translateMultiStoreCore_initialMachineSteps_backward
      twoMessageModel_wellFormed
      twoMessageModel_priorityTimingWellFormed
      (LF.MultiStoreMachineSteps.refl
        _)

theorem twoMessage_public_initial_refl_execution_backward :
    ∃ sourceLabels sourceAfter,
      DTR.MultiStoreMachineSteps
          (DTR.stateVariableNames
            twoMessageModel.reactiveClass.stateVariables)
          twoMessageModel.reactiveClass.messageServers
          (DTR.MultiStoreModel.initialState
            twoMessageModel)
          sourceLabels
          sourceAfter ∧
      Correctness.MultiStoreMachineTraceCorresponds
        sourceLabels
        [] ∧
      Correctness.StoreStateCorresponds
        sourceAfter
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            twoMessageModel)) ∧
      DTR.StoreState.MultiStoreRuntimeWellFormed
        (DTR.stateVariableNames
          twoMessageModel.reactiveClass.stateVariables)
        twoMessageModel.reactiveClass.messageServers
        sourceAfter := by

  exact
    Correctness.translateMultiStore_initialMachineSteps_backward
      twoMessageModel_wellFormed
      twoMessageModel_priorityTimingWellFormed
      (program :=
        Translation.translateMultiStoreCore
          twoMessageModel)
      (by rfl)
      (LF.MultiStoreMachineSteps.refl
        _)

end Tests
end Relico
