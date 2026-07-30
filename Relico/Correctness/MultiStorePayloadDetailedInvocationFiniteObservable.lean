import Relico.Correctness.MultiStorePayloadDetailedInvocationEntry
import Relico.Correctness.MultiStorePayloadDetailedObservableWeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Forward finite weak-execution correspondence starting from the canonical
payload-aware multi-store invocation states.

The existing derivation-indexed compatibility premise is retained unchanged.
-/
theorem multiStorePayloadInvocationFinite_forward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    {sourceAfter :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    (hSourceSteps :
      DTR.DetailedMultiStorePayloadSteps
        messageServers
        (DTR.MultiStorePayloadMessageServer.invocationDetailedMultiStorePayloadState
            messageServers
            server
            initialStateStore
            payload
            delay)
        sourceLabels
        sourceAfter)
    (hCompatible :
      MultiStorePayloadDetailedForwardStepsCompatible
        messageServers
        hSourceSteps
        (LF.invocationDetailedLFMultiStorePayloadState
          messageServers
          server
          initialStateStore
          payload
          delay)) :
    ∃
      targetLabels
        targetAfter,
      LF.DetailedMultiStorePayloadWeakSteps
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          (LF.invocationDetailedLFMultiStorePayloadState
            messageServers
            server
            initialStateStore
            payload
            delay)
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
      (detailedMultiStorePayloadInvocationStates_correspond
        messageServers
        server
        initialStateStore
        payload
        delay)
      hCompatible

/--
Backward finite weak-execution correspondence starting from the canonical
payload-aware generated-LF invocation state.
-/
theorem multiStorePayloadInvocationFinite_backward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
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
        (LF.invocationDetailedLFMultiStorePayloadState
          messageServers
          server
          initialStateStore
          payload
          delay)
        targetLabels
        targetAfter)
    (hCompatible :
      MultiStorePayloadDetailedBackwardStepsCompatible
        messageServers
        (DTR.MultiStorePayloadMessageServer.invocationDetailedMultiStorePayloadState
            messageServers
            server
            initialStateStore
            payload
            delay)
        hTargetSteps) :
    ∃
      sourceLabels
        sourceAfter,
      DTR.DetailedMultiStorePayloadWeakSteps
          messageServers
          (DTR.MultiStorePayloadMessageServer.invocationDetailedMultiStorePayloadState
              messageServers
              server
              initialStateStore
              payload
              delay)
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
      (detailedMultiStorePayloadInvocationStates_correspond
        messageServers
        server
        initialStateStore
        payload
        delay)
      hCompatible

/--
Forward observable-trace correspondence starting from the canonical
payload-aware multi-store invocation states.
-/
theorem multiStorePayloadInvocationObservable_forward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    {sourceAfter :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    (hSourceSteps :
      DTR.DetailedMultiStorePayloadSteps
        messageServers
        (DTR.MultiStorePayloadMessageServer.invocationDetailedMultiStorePayloadState
            messageServers
            server
            initialStateStore
            payload
            delay)
        sourceLabels
        sourceAfter)
    (hCompatible :
      MultiStorePayloadDetailedForwardStepsCompatible
        messageServers
        hSourceSteps
        (LF.invocationDetailedLFMultiStorePayloadState
          messageServers
          server
          initialStateStore
          payload
          delay)) :
    ∃
      targetLabels
        targetAfter,
      LF.DetailedMultiStorePayloadWeakSteps
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          (LF.invocationDetailedLFMultiStorePayloadState
            messageServers
            server
            initialStateStore
            payload
            delay)
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
      (detailedMultiStorePayloadInvocationStates_correspond
        messageServers
        server
        initialStateStore
        payload
        delay)
      hCompatible

/--
Backward observable-trace correspondence starting from the canonical
payload-aware generated-LF invocation state.
-/
theorem multiStorePayloadInvocationObservable_backward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
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
        (LF.invocationDetailedLFMultiStorePayloadState
          messageServers
          server
          initialStateStore
          payload
          delay)
        targetLabels
        targetAfter)
    (hCompatible :
      MultiStorePayloadDetailedBackwardStepsCompatible
        messageServers
        (DTR.MultiStorePayloadMessageServer.invocationDetailedMultiStorePayloadState
            messageServers
            server
            initialStateStore
            payload
            delay)
        hTargetSteps) :
    ∃
      sourceLabels
        sourceAfter,
      DTR.DetailedMultiStorePayloadWeakSteps
          messageServers
          (DTR.MultiStorePayloadMessageServer.invocationDetailedMultiStorePayloadState
              messageServers
              server
              initialStateStore
              payload
              delay)
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
      (detailedMultiStorePayloadInvocationStates_correspond
        messageServers
        server
        initialStateStore
        payload
        delay)
      hCompatible


end Correctness
end Relico
