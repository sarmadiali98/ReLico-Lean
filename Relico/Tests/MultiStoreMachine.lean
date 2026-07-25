import Relico.Correctness.MultiStoreMachine
import Relico.Tests.MultiStoreDispatch
import Relico.Tests.MultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

/--
The cross-server self-send is a combined source-machine statement
step.
-/
theorem multi_source_statement_machine_step :
    DTR.MultiStoreMachineStep
      multiStatementVariables
      twoMessageServers
      multiStatementSourceBefore
      (DTR.MultiStoreMachineLabel.statement
        (DTR.Label.send
          resetMessageName
          1))
      multiStatementSourceAfter := by

  exact
    DTR.MultiStoreMachineStep.statement
      multi_source_cross_server_send

/--
The compiled schedule is the corresponding generated-LF machine
statement step.
-/
theorem multi_target_statement_machine_step :
    LF.MultiStoreMachineStep
      multiStatementVariables
      multiStatementActions
      (Translation.compileMessageReactions
        twoMessageServers)
      multiStatementTargetBefore
      (LF.MultiStoreMachineLabel.statement
        (LF.Label.schedule
          (Translation.actionNameFor
            resetMessageName)
          multiStatementScheduledTag))
      multiStatementTargetAfter := by

  exact
    LF.MultiStoreMachineStep.statement
      multi_target_cross_server_schedule

theorem multiStatementMachineCompatible :
    Correctness.MultiStoreForwardMachineCompatible
      (DTR.MultiStoreMachineLabel.statement
        (DTR.Label.send
          resetMessageName
          1))
      multiStatementSourceAfter
      multiStatementTargetBefore := by

  simp [
    Correctness.MultiStoreForwardMachineCompatible
  ]

theorem multi_statement_machine_forward :
    ∃ targetLabel targetStateAfter,
      LF.MultiStoreMachineStep
          multiStatementVariables
          multiStatementActions
          (Translation.compileMessageReactions
            twoMessageServers)
          multiStatementTargetBefore
          targetLabel
          targetStateAfter ∧
      Correctness.MultiStoreMachineLabelCorresponds
        (DTR.MultiStoreMachineLabel.statement
          (DTR.Label.send
            resetMessageName
            1))
        targetLabel ∧
      Correctness.StoreStateCorresponds
        multiStatementSourceAfter
        targetStateAfter := by

  exact
    Correctness.multiStoreMachineStep_forward
      multi_source_statement_machine_step
      multiStatementInitialStatesCorrespond
      multiStatementMachineCompatible

theorem multi_statement_machine_backward :
    ∃ sourceLabel sourceStateAfter,
      DTR.MultiStoreMachineStep
          multiStatementVariables
          twoMessageServers
          multiStatementSourceBefore
          sourceLabel
          sourceStateAfter ∧
      Correctness.MultiStoreMachineLabelCorresponds
        sourceLabel
        (LF.MultiStoreMachineLabel.statement
          (LF.Label.schedule
            (Translation.actionNameFor
              resetMessageName)
            multiStatementScheduledTag)) ∧
      Correctness.StoreStateCorresponds
        sourceStateAfter
        multiStatementTargetAfter := by

  exact
    Correctness.multiStoreMachineStep_backward
      multi_target_statement_machine_step
      multiStatementInitialStatesCorrespond
      multiStatementSourceBodyWellFormed

/--
Dispatch of the second declared server is a combined source-machine
step.
-/
theorem multi_source_dispatch_machine_step :
    DTR.MultiStoreMachineStep
      multiStatementVariables
      twoMessageServers
      multiDtrDispatchBefore
      (DTR.MultiStoreMachineLabel.dispatch
        multiDispatchMessage
        resetMessageServer)
      multiDtrDispatchAfter := by

  exact
    DTR.MultiStoreMachineStep.dispatch
      multi_dtr_dispatch_selects_reset

/--
The matching generated reaction dispatch is a combined target-machine
step.
-/
theorem multi_target_dispatch_machine_step :
    LF.MultiStoreMachineStep
      multiStatementVariables
      multiStatementActions
      (Translation.compileMessageReactions
        twoMessageServers)
      multiLfDispatchBefore
      (LF.MultiStoreMachineLabel.dispatch
        multiDispatchAction
        (Translation.compileMessageReaction
          resetMessageServer))
      multiLfDispatchAfter := by

  exact
    LF.MultiStoreMachineStep.dispatch
      multi_lf_dispatch_selects_reset_reaction

theorem multiDispatchMachineCompatible :
    Correctness.MultiStoreForwardMachineCompatible
      (DTR.MultiStoreMachineLabel.dispatch
        multiDispatchMessage
        resetMessageServer)
      multiDtrDispatchAfter
      multiLfDispatchBefore := by

  simpa [
    Correctness.MultiStoreForwardMachineCompatible,
    multiDtrDispatchAfter
  ] using
    multiDispatchForwardCompatible

theorem multiDispatchSourceBodyWellFormed :
    DTR.Body.MultiStoreWellFormed
      multiStatementVariables
      multiStatementServerNames
      multiDtrDispatchBefore.activeBody := by

  simp [
    multiDtrDispatchBefore,
    DTR.Body.MultiStoreWellFormed
  ]

theorem multi_dispatch_machine_forward :
    ∃ targetLabel targetStateAfter,
      LF.MultiStoreMachineStep
          multiStatementVariables
          multiStatementActions
          (Translation.compileMessageReactions
            twoMessageServers)
          multiLfDispatchBefore
          targetLabel
          targetStateAfter ∧
      Correctness.MultiStoreMachineLabelCorresponds
        (DTR.MultiStoreMachineLabel.dispatch
          multiDispatchMessage
          resetMessageServer)
        targetLabel ∧
      Correctness.StoreStateCorresponds
        multiDtrDispatchAfter
        targetStateAfter := by

  exact
    Correctness.multiStoreMachineStep_forward
      multi_source_dispatch_machine_step
      multiDispatchStatesCorrespond
      multiDispatchMachineCompatible

theorem multi_dispatch_machine_backward :
    ∃ sourceLabel sourceStateAfter,
      DTR.MultiStoreMachineStep
          multiStatementVariables
          twoMessageServers
          multiDtrDispatchBefore
          sourceLabel
          sourceStateAfter ∧
      Correctness.MultiStoreMachineLabelCorresponds
        sourceLabel
        (LF.MultiStoreMachineLabel.dispatch
          multiDispatchAction
          (Translation.compileMessageReaction
            resetMessageServer)) ∧
      Correctness.StoreStateCorresponds
        sourceStateAfter
        multiLfDispatchAfter := by

  exact
    Correctness.multiStoreMachineStep_backward
      multi_target_dispatch_machine_step
      multiDispatchStatesCorrespond
      multiDispatchSourceBodyWellFormed

end Tests
end Relico
