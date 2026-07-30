import Relico.Translation.MultiStorePayloadBasic
import Relico.Correctness.MultiStorePayloadDetailedInitialization
import Relico.Correctness.MultiStorePayloadDetailedFiniteWeakExecution
import Relico.Correctness.MultiStorePayloadDetailedObservableWeakExecution

set_option autoImplicit false

namespace Relico

namespace DTR

/--
Canonical source constructor-entry state.

This is distinct from the empty canonical initial state: the constructor body
has been installed as the active body, but no invocation or pending message
has been introduced.
-/
def MultiStorePayloadConstructor.startupMultiStorePayloadState
    (constructor : MultiStorePayloadConstructor)
    (initialStateStore : StateStore) :
    MultiStorePayloadState :=
  {
    currentTime := 0
    stateStore := initialStateStore
    parameters := []
    pendingMessages := []
    activeBody := constructor.body
  }

/--
Detailed source constructor-entry state.
-/
def MultiStorePayloadConstructor.startupDetailedMultiStorePayloadState
    (constructor : MultiStorePayloadConstructor)
    (messageServers : List MultiStorePayloadMessageServer)
    (initialStateStore : StateStore) :
    DetailedMultiStorePayloadState messageServers :=
  DetailedMultiStorePayloadState.stable
    (constructor.startupMultiStorePayloadState
      initialStateStore)

end DTR

namespace LF

/--
Canonical generated-LF startup-entry state.

The active body is taken directly from the generated startup reaction. No
startup transition or pending action is added.
-/
def startupLFMultiStorePayloadState
    (constructor : DTR.MultiStorePayloadConstructor)
    (initialStateStore : StateStore) :
    MultiStorePayloadState :=
  {
    currentTag := {
      time := 0
      microstep := 0
    }
    stateStore := initialStateStore
    parameters := []
    pendingActions := []
    activeBody :=
      (Translation.compileMultiStorePayloadStartupReaction
        constructor).body
  }

/--
Detailed generated-LF startup-entry state.
-/
def startupDetailedLFMultiStorePayloadState
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore) :
    DetailedMultiStorePayloadState
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers) :=
  DetailedMultiStorePayloadState.stable
    (startupLFMultiStorePayloadState
      constructor
      initialStateStore)

end LF

namespace Correctness

/--
The generated startup reaction has the expected canonical shape.
-/
theorem multiStorePayloadStartupReaction_shape
    (constructor :
      DTR.MultiStorePayloadConstructor) :
    (Translation.compileMultiStorePayloadStartupReaction
        constructor).name =
        Translation.startupReactionName ∧
      (Translation.compileMultiStorePayloadStartupReaction
        constructor).trigger =
        LF.MultiStorePayloadTrigger.startup ∧
      (Translation.compileMultiStorePayloadStartupReaction
        constructor).parameters = [] ∧
      (Translation.compileMultiStorePayloadStartupReaction
        constructor).body =
        Translation.compileMultiStorePayloadBody
          constructor.body := by

  exact ⟨rfl, rfl, rfl, rfl⟩

/--
Runtime correspondence of canonical source constructor entry and generated-LF
startup entry.
-/
theorem multiStorePayloadStartupStates_correspond
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore) :
    MultiStorePayloadRuntimeStateCorresponds
      messageServers
      (constructor.startupMultiStorePayloadState
        initialStateStore)
      (LF.startupLFMultiStorePayloadState
        constructor
        initialStateStore) := by

  exact {
    states := {
      states := {
        currentTime := rfl
        stateStore := rfl
        parameters := rfl
        pendingQueues :=
          PayloadQueueCorresponds.nil
        activeBody := rfl
      }
      pendingEvents :=
        multiStorePayloadSelectionCompatible_nil
          messageServers
    }
    pendingNotPast :=
      LF.MultiStorePayloadState.pendingNotPast_of_pendingActions_nil
          rfl
  }

/--
Detailed runtime correspondence at constructor/startup entry.
-/
theorem detailedMultiStorePayloadStartupStates_correspond
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (constructor.startupDetailedMultiStorePayloadState
        messageServers
        initialStateStore)
      (LF.startupDetailedLFMultiStorePayloadState
        messageServers
        constructor
        initialStateStore) := by

  exact
    MultiStorePayloadDetailedRuntimeStateCorresponds.stable
      (multiStorePayloadStartupStates_correspond
        messageServers
        constructor
        initialStateStore)

/--
Canonical startup-entry package. It connects the generated startup reaction
to the active generated-LF startup body without introducing a startup
transition.
-/
theorem multiStorePayloadStartupEntry_package
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        (LF.startupDetailedLFMultiStorePayloadState
          messageServers
          constructor
          initialStateStore) ∧
      (constructor.startupMultiStorePayloadState
          initialStateStore).activeBody =
          constructor.body ∧
      (LF.startupLFMultiStorePayloadState
          constructor
          initialStateStore).activeBody =
          (Translation.compileMultiStorePayloadStartupReaction
            constructor).body ∧
      (Translation.compileMultiStorePayloadStartupReaction
          constructor).body =
          Translation.compileMultiStorePayloadBody
            constructor.body := by

  exact ⟨
    detailedMultiStorePayloadStartupStates_correspond
      messageServers
      constructor
      initialStateStore,
    rfl,
    rfl,
    rfl
  ⟩

/--
Conditional forward finite weak-execution correspondence from canonical
constructor/startup entry.
-/
theorem multiStorePayloadStartupFinite_forward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore)
    {sourceAfter :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    (hSourceSteps :
      DTR.DetailedMultiStorePayloadSteps
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        sourceLabels
        sourceAfter)
    (hCompatible :
      MultiStorePayloadDetailedForwardStepsCompatible
        messageServers
        hSourceSteps
        (LF.startupDetailedLFMultiStorePayloadState
          messageServers
          constructor
          initialStateStore)) :
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
          sourceAfter
          targetAfter := by

  exact
    multiStorePayloadDetailedSteps_forward_of_compatible
      hSourceSteps
      (detailedMultiStorePayloadStartupStates_correspond
        messageServers
        constructor
        initialStateStore)
      hCompatible

/--
Conditional backward finite weak-execution correspondence from canonical
generated-LF startup entry.
-/
theorem multiStorePayloadStartupFinite_backward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore)
    {targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
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
        targetAfter)
    (hCompatible :
      MultiStorePayloadDetailedBackwardStepsCompatible
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        hTargetSteps) :
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
          targetAfter := by

  exact
    multiStorePayloadDetailedSteps_backward_of_compatible
      hTargetSteps
      (detailedMultiStorePayloadStartupStates_correspond
        messageServers
        constructor
        initialStateStore)
      hCompatible

/--
Conditional forward observable-trace correspondence from canonical
constructor/startup entry.
-/
theorem multiStorePayloadStartupObservable_forward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore)
    {sourceAfter :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    (hSourceSteps :
      DTR.DetailedMultiStorePayloadSteps
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        sourceLabels
        sourceAfter)
    (hCompatible :
      MultiStorePayloadDetailedForwardStepsCompatible
        messageServers
        hSourceSteps
        (LF.startupDetailedLFMultiStorePayloadState
          messageServers
          constructor
          initialStateStore)) :
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
          sourceAfter
          targetAfter ∧
        MultiStorePayloadDetailedObservableTraceCorresponds
          (DTR.detailedMultiStorePayloadObservableTrace
            sourceLabels)
          (LF.detailedMultiStorePayloadObservableTrace
            targetLabels) := by

  exact
    multiStorePayloadDetailedSteps_forward_observable_of_compatible
      hSourceSteps
      (detailedMultiStorePayloadStartupStates_correspond
        messageServers
        constructor
        initialStateStore)
      hCompatible

/--
Conditional backward observable-trace correspondence from canonical
generated-LF startup entry.
-/
theorem multiStorePayloadStartupObservable_backward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (constructor :
      DTR.MultiStorePayloadConstructor)
    (initialStateStore :
      StateStore)
    {targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
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
        targetAfter)
    (hCompatible :
      MultiStorePayloadDetailedBackwardStepsCompatible
        messageServers
        (constructor.startupDetailedMultiStorePayloadState
          messageServers
          initialStateStore)
        hTargetSteps) :
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
          targetAfter ∧
        MultiStorePayloadDetailedObservableTraceCorresponds
          (DTR.detailedMultiStorePayloadObservableTrace
            sourceLabels)
          (LF.detailedMultiStorePayloadObservableTrace
            targetLabels) := by

  exact
    multiStorePayloadDetailedSteps_backward_observable_of_compatible
      hTargetSteps
      (detailedMultiStorePayloadStartupStates_correspond
        messageServers
        constructor
        initialStateStore)
      hCompatible

end Correctness
end Relico
