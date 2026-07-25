import Relico.Correctness.MultiStoreMachineTrace
import Relico.Tests.MultiStoreMachine

set_option autoImplicit false

namespace Relico
namespace Tests

/--
The second-server dispatch forms a finite source multi-server machine
execution.
-/
theorem multi_source_dispatch_machine_steps :
    DTR.MultiStoreMachineSteps
      multiStatementVariables
      twoMessageServers
      multiDtrDispatchBefore
      [
        DTR.MultiStoreMachineLabel.dispatch
          multiDispatchMessage
          resetMessageServer
      ]
      multiDtrDispatchAfter := by

  exact
    DTR.MultiStoreMachineSteps.cons
      multi_source_dispatch_machine_step
      (DTR.MultiStoreMachineSteps.refl
        multiDtrDispatchAfter)

/--
The matching generated reaction dispatch forms the corresponding
finite target execution.
-/
theorem multi_target_dispatch_machine_steps :
    LF.MultiStoreMachineSteps
      multiStatementVariables
      multiStatementActions
      (Translation.compileMessageReactions
        twoMessageServers)
      multiLfDispatchBefore
      [
        LF.MultiStoreMachineLabel.dispatch
          multiDispatchAction
          (Translation.compileMessageReaction
            resetMessageServer)
      ]
      multiLfDispatchAfter := by

  exact
    LF.MultiStoreMachineSteps.cons
      multi_target_dispatch_machine_step
      (LF.MultiStoreMachineSteps.refl
        multiLfDispatchAfter)

/--
Every body in the two-server model is valid for the complete variable
and message-server declaration sets.
-/
theorem twoMessageServerBodies_runtimeWellFormed :
    ∀ messageServer,
      messageServer ∈
        twoMessageServers →
      DTR.Body.MultiStoreWellFormed
        multiStatementVariables
        multiStatementServerNames
        messageServer.body := by

  intro messageServer hMember

  have hModelMember :
      messageServer ∈
        twoMessageModel.reactiveClass.messageServers := by

    simpa [
      twoMessageModel,
      twoMessageReactiveClass
    ] using
      hMember

  have hBody :=
    twoMessageModel_wellFormed.messageServerBodiesWellFormed
      messageServer
      hModelMember

  simpa [
    multiStatementVariables,
    multiStatementServerNames,
    twoMessageModel,
    twoMessageReactiveClass
  ] using
    hBody

/--
The concrete source dispatch state satisfies the multi-server runtime
invariant.
-/
theorem multiDispatchSource_runtimeWellFormed :
    DTR.StoreState.MultiStoreRuntimeWellFormed
      multiStatementVariables
      twoMessageServers
      multiDtrDispatchBefore := by

  exact {
    coverage := by
      change
        StateStore.Covers
          multiStatementVariables
          multiDispatchStore

      intro variableName hMember

      simp [
        multiStatementVariables,
        twoStateDeclarations,
        DTR.stateVariableNames
      ] at hMember

      rcases hMember with
        rfl | rfl

      · exact
          ⟨1, by
            simp [
              multiDispatchStore,
              StateStore.lookup,
              Store.lookup,
              twoStateX,
              twoStateY
            ]⟩

      · exact
          ⟨2, by
            simp [
              multiDispatchStore,
              StateStore.lookup,
              Store.lookup,
              twoStateX,
              twoStateY
            ]⟩

    activeBody := by
      simp [
        multiDtrDispatchBefore,
        DTR.Body.MultiStoreWellFormed
      ]

    pendingTargets := by
      intro pendingMessage hMember

      simp [
        multiDtrDispatchBefore
      ] at hMember

      subst pendingMessage

      simp [
        multiDispatchMessage,
        twoMessageServers,
        DTR.messageServerNames,
        tickMessageServer,
        resetMessageServer
      ]
  }

/--
The one-dispatch source execution preserves complete multi-server
runtime well-formedness.
-/
theorem multi_dispatch_trace_preserves_runtimeWellFormed :
    DTR.StoreState.MultiStoreRuntimeWellFormed
      multiStatementVariables
      twoMessageServers
      multiDtrDispatchAfter := by

  exact
    Correctness.dtrMultiStoreMachineSteps_preserve_runtimeWellFormed
      multi_source_dispatch_machine_steps
      twoMessageServerBodies_runtimeWellFormed
      multiDispatchSource_runtimeWellFormed

/--
Compatibility evidence for the concrete one-dispatch source
execution.
-/
theorem multiDispatchMachineStepsCompatible :
    Correctness.MultiStoreForwardMachineStepsCompatible
      multiStatementVariables
      twoMessageServers
      multi_source_dispatch_machine_steps
      multiLfDispatchBefore := by

  unfold
    Correctness.MultiStoreForwardMachineStepsCompatible

  simp only [
    Correctness.MultiStoreForwardMachineLabelsCompatible
  ]

  intro sourceMiddle
  intro hSourceHead
  intro hSourceTail

  cases hSourceTail with

  | refl state =>
      refine
        ⟨multiDispatchMachineCompatible,
         ?_⟩

      intro targetLabel
      intro targetMiddle
      intro hTargetStep
      intro hLabels
      intro hStates

      rfl

/--
Forward finite-execution correspondence applies to the compatible
second-server dispatch.
-/
theorem multi_dispatch_machine_steps_forward :
    ∃ targetLabels targetAfter,
      LF.MultiStoreMachineSteps
          multiStatementVariables
          multiStatementActions
          (Translation.compileMessageReactions
            twoMessageServers)
          multiLfDispatchBefore
          targetLabels
          targetAfter ∧
      Correctness.MultiStoreMachineTraceCorresponds
        [
          DTR.MultiStoreMachineLabel.dispatch
            multiDispatchMessage
            resetMessageServer
        ]
        targetLabels ∧
      Correctness.StoreStateCorresponds
        multiDtrDispatchAfter
        targetAfter := by

  exact
    Correctness.multiStoreMachineSteps_forward_of_compatible
      multi_source_dispatch_machine_steps
      multiDispatchStatesCorrespond
      multiDispatchMachineStepsCompatible

/--
Backward finite-execution correspondence recovers a source execution
and preserves its runtime invariant.
-/
theorem multi_dispatch_machine_steps_backward :
    ∃ sourceLabels sourceAfter,
      DTR.MultiStoreMachineSteps
          multiStatementVariables
          twoMessageServers
          multiDtrDispatchBefore
          sourceLabels
          sourceAfter ∧
      Correctness.MultiStoreMachineTraceCorresponds
        sourceLabels
        [
          LF.MultiStoreMachineLabel.dispatch
            multiDispatchAction
            (Translation.compileMessageReaction
              resetMessageServer)
        ] ∧
      Correctness.StoreStateCorresponds
        sourceAfter
        multiLfDispatchAfter ∧
      DTR.StoreState.MultiStoreRuntimeWellFormed
        multiStatementVariables
        twoMessageServers
        sourceAfter := by

  exact
    Correctness.multiStoreMachineSteps_backward
      multi_target_dispatch_machine_steps
      multiDispatchStatesCorrespond
      twoMessageServerBodies_runtimeWellFormed
      multiDispatchSource_runtimeWellFormed

end Tests
end Relico
