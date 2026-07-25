import Relico.Common.Occurrence
import Relico.DTR.MultiStoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace DTR
namespace StoreState

/--
Runtime well-formedness for a finite-store DTR state with multiple
declared message servers.

The invariant records:

- coverage of every declared state variable;
- structural validity of the active body against every declared server;
- membership of every pending-message target in the declared server
  name list.
-/
structure MultiStoreRuntimeWellFormed
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (state : DTR.StoreState) :
    Prop where

  coverage :
    DTR.StoreState.Covers
      declaredVariables
      state

  activeBody :
    DTR.Body.MultiStoreWellFormed
      declaredVariables
      (DTR.messageServerNames
        messageServers)
      state.activeBody

  pendingTargets :
    ∀ pendingMessage,
      pendingMessage ∈
        state.pendingMessages →
      pendingMessage.name ∈
        DTR.messageServerNames
          messageServers

end StoreState

namespace MultiStoreMachineStep

/--
Every combined multi-server machine step preserves runtime
well-formedness when every declared message-server body is structurally
well formed.
-/
theorem preserves_runtimeWellFormed
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {before after : DTR.StoreState}
    {label : DTR.MultiStoreMachineLabel}
    (hStep :
      DTR.MultiStoreMachineStep
        declaredVariables
        messageServers
        before
        label
        after)
    (hMessageBodies :
      ∀ messageServer,
        messageServer ∈
          messageServers →
        DTR.Body.MultiStoreWellFormed
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          messageServer.body)
    (hBefore :
      DTR.StoreState.MultiStoreRuntimeWellFormed
        declaredVariables
        messageServers
        before) :
    DTR.StoreState.MultiStoreRuntimeWellFormed
      declaredVariables
      messageServers
      after := by

  cases hStep with

  | statement hStatement =>
      exact {
        coverage :=
          DTR.MultiStoreStep.preserves_coverage
            hStatement
            hBefore.coverage

        activeBody :=
          DTR.MultiStoreStep.preserves_body_multiStoreWellFormed
            hStatement
            hBefore.activeBody

        pendingTargets :=
          DTR.MultiStoreStep.preserves_pendingTargets
            hStatement
            hBefore.pendingTargets
      }

  | dispatch hDispatch =>
      cases hDispatch with

      | fire
          currentTime
          stateStore
          pendingMessages
          remainingMessages
          selectedMessage
          selectedServer
          hServerDeclared
          hRemoved
          hEarliest
          hNotPast
          hTarget =>

          exact {
            coverage :=
              hBefore.coverage

            activeBody :=
              hMessageBodies
                _
                hServerDeclared

            pendingTargets := by
              intro pendingMessage hMember

              apply
                hBefore.pendingTargets
                  pendingMessage

              exact
                Occurrence.RemovesOne.remaining_mem
                  hRemoved
                  hMember
          }

end MultiStoreMachineStep
end DTR
end Relico
