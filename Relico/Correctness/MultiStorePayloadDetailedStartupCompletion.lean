import Relico.Correctness.MultiStorePayloadDetailedStartupEntry
import Relico.Correctness.MultiStorePayloadDetailedFiniteWeakExecution
import Relico.Correctness.MultiStorePayloadDetailedObservableWeakExecution

set_option autoImplicit false

namespace Relico

namespace DTR

/--
A runtime state has completed its currently active startup body.

Pending messages remain unrestricted.
-/
def MultiStorePayloadState.StartupBodyComplete
    (state : MultiStorePayloadState) :
    Prop :=
  state.activeBody = []

/--
Strict detailed completion requires the stable phase and an empty active body.

Dispatch-ready phases are deliberately not classified as complete.
-/
def DetailedMultiStorePayloadState.StartupBodyComplete
    {messageServers :
      List MultiStorePayloadMessageServer}
    (state :
      DetailedMultiStorePayloadState messageServers) :
    Prop :=
  match state with
  | .stable baseState =>
      baseState.StartupBodyComplete
  | .dispatchReady _ _ _ _ _ =>
      False

end DTR

namespace LF

/--
A target runtime state has completed its currently active startup body.

Pending actions remain unrestricted.
-/
def MultiStorePayloadState.StartupBodyComplete
    (state : MultiStorePayloadState) :
    Prop :=
  state.activeBody = []

/--
Strict target completion requires a stable detailed phase.

The administrative `afterTime` and `dispatchReady` phases are not classified
as complete.
-/
def DetailedMultiStorePayloadState.StartupBodyComplete
    {messageReactions :
      List MultiStorePayloadReaction}
    (state :
      DetailedMultiStorePayloadState messageReactions) :
    Prop :=
  match state with
  | .stable baseState =>
      baseState.StartupBodyComplete
  | .afterTime _ _ _ _ _ =>
      False
  | .dispatchReady _ _ _ _ _ =>
      False

end LF

namespace Correctness

/--
Compilation reflects and preserves active-body emptiness.
-/
theorem multiStorePayloadStartupBody_compile_eq_nil_iff
    (body :
      DTR.MultiStorePayloadBody) :
    Translation.compileMultiStorePayloadBody body = [] ↔
      body = [] := by

  simp [
    Translation.compileMultiStorePayloadBody
  ]

/--
Corresponding base runtime states agree on startup-body completion.
-/
theorem multiStorePayloadRuntimeStartupBodyComplete_iff
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hStates :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    sourceState.StartupBodyComplete ↔
      targetState.StartupBodyComplete := by

  unfold
    DTR.MultiStorePayloadState.StartupBodyComplete

  unfold
    LF.MultiStorePayloadState.StartupBodyComplete

  rw [
    hStates.states.states.activeBody
  ]

  simp [
    Translation.compileMultiStorePayloadBody
  ]

/--
Explicit stable-to-stable detailed correspondence preserves and reflects
startup-body completion.
-/
theorem multiStorePayloadDetailedStableStartupBodyComplete_iff
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (DTR.DetailedMultiStorePayloadState.stable
          sourceState)
        (LF.DetailedMultiStorePayloadState.stable
          targetState)) :
    (DTR.DetailedMultiStorePayloadState.stable
        (messageServers := messageServers)
        sourceState).StartupBodyComplete ↔
      (LF.DetailedMultiStorePayloadState.stable
        (messageReactions :=
          Translation.compileMultiStorePayloadMessageReactions
            messageServers)
        targetState).StartupBodyComplete := by

  cases hStates with
  | stable hRuntime =>
      simpa [
        DTR.DetailedMultiStorePayloadState.StartupBodyComplete,
        LF.DetailedMultiStorePayloadState.StartupBodyComplete
      ] using
        (multiStorePayloadRuntimeStartupBodyComplete_iff
          hRuntime)

/--
When a corresponding target endpoint is explicitly stable, target completion
implies strict source detailed completion.

The indexed correspondence excludes every non-stable source phase here.
-/
theorem multiStorePayloadSourceStartupBodyComplete_of_targetStable
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    {targetState :
      LF.MultiStorePayloadState}
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        sourceState
        (LF.DetailedMultiStorePayloadState.stable
          targetState))
    (hTargetComplete :
      targetState.StartupBodyComplete) :
    sourceState.StartupBodyComplete := by

  cases hStates with
  | stable hRuntime =>
      simpa [
        DTR.DetailedMultiStorePayloadState.StartupBodyComplete
      ] using
        (multiStorePayloadRuntimeStartupBodyComplete_iff
          hRuntime).mpr
          hTargetComplete

/--
When a source endpoint is stable and complete, a corresponding target endpoint
is complete whenever that target endpoint is also stable.

This theorem intentionally does not claim that arbitrary corresponding target
endpoints are stable.
-/
theorem multiStorePayloadTargetStartupBodyComplete_of_sourceStable_targetStable
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetDetailedState :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (DTR.DetailedMultiStorePayloadState.stable
          sourceState)
        targetDetailedState)
    (hSourceComplete :
      sourceState.StartupBodyComplete)
    {targetState :
      LF.MultiStorePayloadState}
    (hTargetStable :
      targetDetailedState =
        LF.DetailedMultiStorePayloadState.stable
          targetState) :
    targetState.StartupBodyComplete := by

  subst targetDetailedState

  cases hStates with
  | stable hRuntime =>
      exact
        (multiStorePayloadRuntimeStartupBodyComplete_iff
          hRuntime).mp
          hSourceComplete

/--
Forward finite startup execution preserves the published simulation result.

When its existential target endpoint is stable, source startup-body completion
projects to target startup-body completion.
-/
theorem multiStorePayloadStartupFinite_forward_completion_when_target_stable
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore)
    {sourceAfter :
      DTR.MultiStorePayloadState}
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    (hSourceSteps :
      DTR.DetailedMultiStorePayloadSteps
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        sourceLabels
        (DTR.DetailedMultiStorePayloadState.stable
          sourceAfter))
    (hCompatible :
      MultiStorePayloadDetailedForwardStepsCompatible
        messageServers
        hSourceSteps
        (LF.startupDetailedLFMultiStorePayloadState
          messageServers
          constructor
          initialStateStore))
    (hSourceComplete :
      sourceAfter.StartupBodyComplete) :
    ∃
      targetLabels
        targetAfter,
      LF.DetailedMultiStorePayloadWeakSteps
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          (LF.startupDetailedLFMultiStorePayloadState
            messageServers
            constructor
            initialStateStore)
          targetLabels
          targetAfter ∧
        MultiStorePayloadDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          (DTR.DetailedMultiStorePayloadState.stable
            sourceAfter)
          targetAfter ∧
        ∀
          targetState,
          targetAfter =
              LF.DetailedMultiStorePayloadState.stable
                targetState →
            targetState.StartupBodyComplete := by

  obtain ⟨
    targetLabels,
    targetAfter,
    hTargetSteps,
    hTrace,
    hStates
  ⟩ :=
    multiStorePayloadStartupFinite_forward
      constructor
      initialStateStore
      hSourceSteps
      hCompatible

  refine ⟨
    targetLabels,
    targetAfter,
    hTargetSteps,
    hTrace,
    hStates,
    ?_
  ⟩

  intro targetState hTargetStable

  exact
    multiStorePayloadTargetStartupBodyComplete_of_sourceStable_targetStable
      hStates
      hSourceComplete
      hTargetStable

/--
Backward finite startup execution ending in a stable, completed LF state
produces a strictly completed source endpoint.
-/
theorem multiStorePayloadStartupFinite_backward_completion
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore)
    {targetAfter :
      LF.MultiStorePayloadState}
    {targetLabels :
      List LF.DetailedMultiStorePayloadLabel}
    (hTargetSteps :
      LF.DetailedMultiStorePayloadSteps
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        (LF.startupDetailedLFMultiStorePayloadState
          messageServers
          constructor
          initialStateStore)
        targetLabels
        (LF.DetailedMultiStorePayloadState.stable
          targetAfter))
    (hCompatible :
      MultiStorePayloadDetailedBackwardStepsCompatible
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        hTargetSteps)
    (hTargetComplete :
      targetAfter.StartupBodyComplete) :
    ∃
      sourceLabels
        sourceAfter,
      DTR.DetailedMultiStorePayloadWeakSteps
          messageServers
          (constructor.startupDetailedMultiStorePayloadState
            messageServers
            initialStateStore)
          sourceLabels
          sourceAfter ∧
        MultiStorePayloadDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          sourceAfter
          (LF.DetailedMultiStorePayloadState.stable
            targetAfter) ∧
        sourceAfter.StartupBodyComplete := by

  obtain ⟨
    sourceLabels,
    sourceAfter,
    hSourceSteps,
    hTrace,
    hStates
  ⟩ :=
    multiStorePayloadStartupFinite_backward
      constructor
      initialStateStore
      hTargetSteps
      hCompatible

  refine ⟨
    sourceLabels,
    sourceAfter,
    hSourceSteps,
    hTrace,
    hStates,
    ?_
  ⟩

  exact
    multiStorePayloadSourceStartupBodyComplete_of_targetStable
      hStates
      hTargetComplete

/--
Observable forward startup correspondence with the same stable-target
completion projection.
-/
theorem multiStorePayloadStartupObservable_forward_completion_when_target_stable
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore)
    {sourceAfter :
      DTR.MultiStorePayloadState}
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    (hSourceSteps :
      DTR.DetailedMultiStorePayloadSteps
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        sourceLabels
        (DTR.DetailedMultiStorePayloadState.stable
          sourceAfter))
    (hCompatible :
      MultiStorePayloadDetailedForwardStepsCompatible
        messageServers
        hSourceSteps
        (LF.startupDetailedLFMultiStorePayloadState
          messageServers
          constructor
          initialStateStore))
    (hSourceComplete :
      sourceAfter.StartupBodyComplete) :
    ∃
      targetLabels
        targetAfter,
      LF.DetailedMultiStorePayloadWeakSteps
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          (LF.startupDetailedLFMultiStorePayloadState
            messageServers
            constructor
            initialStateStore)
          targetLabels
          targetAfter ∧
        MultiStorePayloadDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          (DTR.DetailedMultiStorePayloadState.stable
            sourceAfter)
          targetAfter ∧
        MultiStorePayloadDetailedObservableTraceCorresponds
          (DTR.detailedMultiStorePayloadObservableTrace
            sourceLabels)
          (LF.detailedMultiStorePayloadObservableTrace
            targetLabels) ∧
        ∀
          targetState,
          targetAfter =
              LF.DetailedMultiStorePayloadState.stable
                targetState →
            targetState.StartupBodyComplete := by

  obtain ⟨
    targetLabels,
    targetAfter,
    hTargetSteps,
    hTrace,
    hStates,
    hObservable
  ⟩ :=
    multiStorePayloadStartupObservable_forward
      constructor
      initialStateStore
      hSourceSteps
      hCompatible

  refine ⟨
    targetLabels,
    targetAfter,
    hTargetSteps,
    hTrace,
    hStates,
    hObservable,
    ?_
  ⟩

  intro targetState hTargetStable

  exact
    multiStorePayloadTargetStartupBodyComplete_of_sourceStable_targetStable
      hStates
      hSourceComplete
      hTargetStable

/--
Observable backward startup correspondence ending in a stable, completed
target state produces a strictly completed source endpoint.
-/
theorem multiStorePayloadStartupObservable_backward_completion
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore)
    {targetAfter :
      LF.MultiStorePayloadState}
    {targetLabels :
      List LF.DetailedMultiStorePayloadLabel}
    (hTargetSteps :
      LF.DetailedMultiStorePayloadSteps
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        (LF.startupDetailedLFMultiStorePayloadState
          messageServers
          constructor
          initialStateStore)
        targetLabels
        (LF.DetailedMultiStorePayloadState.stable
          targetAfter))
    (hCompatible :
      MultiStorePayloadDetailedBackwardStepsCompatible
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        hTargetSteps)
    (hTargetComplete :
      targetAfter.StartupBodyComplete) :
    ∃
      sourceLabels
        sourceAfter,
      DTR.DetailedMultiStorePayloadWeakSteps
          messageServers
          (constructor.startupDetailedMultiStorePayloadState
            messageServers
            initialStateStore)
          sourceLabels
          sourceAfter ∧
        MultiStorePayloadDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          sourceAfter
          (LF.DetailedMultiStorePayloadState.stable
            targetAfter) ∧
        MultiStorePayloadDetailedObservableTraceCorresponds
          (DTR.detailedMultiStorePayloadObservableTrace
            sourceLabels)
          (LF.detailedMultiStorePayloadObservableTrace
            targetLabels) ∧
        sourceAfter.StartupBodyComplete := by

  obtain ⟨
    sourceLabels,
    sourceAfter,
    hSourceSteps,
    hTrace,
    hStates,
    hObservable
  ⟩ :=
    multiStorePayloadStartupObservable_backward
      constructor
      initialStateStore
      hTargetSteps
      hCompatible

  refine ⟨
    sourceLabels,
    sourceAfter,
    hSourceSteps,
    hTrace,
    hStates,
    hObservable,
    ?_
  ⟩

  exact
    multiStorePayloadSourceStartupBodyComplete_of_targetStable
      hStates
      hTargetComplete

end Correctness
end Relico
