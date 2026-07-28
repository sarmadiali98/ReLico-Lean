/-
Copyright (c) 2026.

Invariant-carrying runtime correspondence for the direct DTR-to-LF
translation.

The structural cross-language relation remains
`DirectLFStoreStateCorresponds`.

`DirectLFRuntimeStateCorresponds` adds the ordinary LF pending-not-past
scheduler invariant without changing either operational semantics.
-/

import Relico.Correctness.DirectLFStatementBackward
import Relico.LF.PendingNotPast

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Runtime correspondence used at operational dispatch boundaries.

The structural state relation and target scheduler consistency are kept as
separate fields:

- `states` records DTR/LF correspondence;
- `pendingNotPast` records ordinary LF scheduler consistency.

This package contains proof data only. It does not extend either runtime
state.
-/
structure DirectLFRuntimeStateCorresponds
    (messageServers :
      List DTR.MessageServer)
    (sourceState :
      DTR.StoreState)
    (targetState :
      LF.StoreState) :
    Prop where

  states :
    DirectLFStoreStateCorresponds
      messageServers
      sourceState
      targetState

  pendingNotPast :
    LF.StoreState.PendingNotPast
      targetState

/--
The runtime package retains structural occurrence-preserving bag/action-queue
correspondence.
-/
theorem DirectLFRuntimeStateCorresponds.toBagQueueCorresponds
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState}
    (hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFBagQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions :=
  hRuntime.states.toBagQueueCorresponds

/--
The runtime package retains selection compatibility.
-/
theorem DirectLFRuntimeStateCorresponds.selectionCompatible
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState}
    (hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions :=
  hRuntime.states.pendingEvents

/--
Forward ordinary statement simulation preserves the runtime package.

The structural component is supplied by
`directLF_multiStore_step_forward`; the LF pending-not-past component follows
from the generic LF statement-preservation theorem.
-/
theorem directLF_multiStore_step_forward_runtime
    {declaredVariables :
      List VarName}
    {messageServers :
      List DTR.MessageServer}
    {sourceState sourceStateAfter :
      DTR.StoreState}
    {sourceLabel :
      DTR.Label}
    {targetState :
      LF.StoreState}
    (hSourceStep :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceState
        sourceLabel
        sourceStateAfter)
    (hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState)
    (hStatementAppend :
      DirectLFStatementAppendCompatible
        messageServers
        sourceState
        targetState) :
    ∃ targetLabel targetStateAfter,
      LF.MultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          targetState
          targetLabel
          targetStateAfter ∧
        LabelCorresponds
          sourceLabel
          targetLabel ∧
        DirectLFRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter := by

  obtain
    ⟨targetLabel,
     targetStateAfter,
     hTargetStep,
     hLabels,
     hStatesAfter⟩ :=
      directLF_multiStore_step_forward
        hSourceStep
        hRuntime.states
        hStatementAppend

  refine
    ⟨targetLabel,
     targetStateAfter,
     hTargetStep,
     hLabels,
     ?_⟩

  exact {
    states :=
      hStatesAfter

    pendingNotPast :=
      LF.MultiStoreStep.preserves_pendingNotPast
        hTargetStep
        hRuntime.pendingNotPast
  }

/--
Backward ordinary statement simulation preserves the runtime package.

The source step is reconstructed by
`directLF_multiStore_step_backward`; target scheduler consistency is preserved
by the already-given LF step.
-/
theorem directLF_multiStore_step_backward_runtime
    {declaredVariables :
      List VarName}
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState targetStateAfter :
      LF.StoreState}
    {targetLabel :
      LF.Label}
    (hTargetStep :
      LF.MultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        targetState
        targetLabel
        targetStateAfter)
    (hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState)
    (hStatementAppend :
      DirectLFStatementAppendCompatible
        messageServers
        sourceState
        targetState)
    (hSourceBodyWellFormed :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceState.activeBody) :
    ∃ sourceLabel sourceStateAfter,
      DTR.MultiStoreStep
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          sourceState
          sourceLabel
          sourceStateAfter ∧
        LabelCorresponds
          sourceLabel
          targetLabel ∧
        DirectLFRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter := by

  obtain
    ⟨sourceLabel,
     sourceStateAfter,
     hSourceStep,
     hLabels,
     hStatesAfter⟩ :=
      directLF_multiStore_step_backward
        hTargetStep
        hRuntime.states
        hStatementAppend
        hSourceBodyWellFormed

  refine
    ⟨sourceLabel,
     sourceStateAfter,
     hSourceStep,
     hLabels,
     ?_⟩

  exact {
    states :=
      hStatesAfter

    pendingNotPast :=
      LF.MultiStoreStep.preserves_pendingNotPast
        hTargetStep
        hRuntime.pendingNotPast
  }

end Correctness
end Relico
