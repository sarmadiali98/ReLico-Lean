import Relico.Correctness.DetailedFiniteWeakExecution
import Relico.Correctness.PriorityEligibility
import Relico.Correctness.PriorityMachineTiming
import Relico.Correctness.MultiStoreInitialization

set_option autoImplicit false

namespace Relico

namespace LF
namespace StoreState

/--
Full generated-LF timing invariant for the positive-delay,
priority-sensitive fragment.

The previous `PendingMicrostepsZero` invariant constrains only queued
occurrences. Forward dispatch also needs the current tag at microstep zero so
that an equal-metric-time queued occurrence at microstep zero is not in the
past.
-/
structure PriorityRuntimeInvariant
    (state : LF.StoreState) :
    Prop where

  currentMicrostepZero :
    state.currentTag.microstep =
      0

  pendingMicrostepsZero :
    LF.StoreState.PendingMicrostepsZero
      state

end StoreState

namespace MultiStoreProgram

/--
Every generated multi-store program begins with current microstep zero and an
empty pending-action queue.
-/
theorem initialState_priorityRuntimeInvariant
    (program : LF.MultiStoreProgram) :
    LF.StoreState.PriorityRuntimeInvariant
      (LF.MultiStoreProgram.initialState
        program) := by

  refine {
    currentMicrostepZero := ?_
    pendingMicrostepsZero := ?_
  }

  · rfl

  · intro action hAction

    simp [
      LF.MultiStoreProgram.initialState
    ] at hAction

end MultiStoreProgram
end LF

namespace Correctness

/--
One generated-LF multi-store machine step preserves current-microstep zero
when every queued action in the pre-state has microstep zero.

Statement steps leave the current tag unchanged. Dispatch changes the current
tag to the selected action tag, whose microstep is zero by queue membership.
-/
theorem targetMultiStoreMachineStep_preserves_currentMicrostepZero
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {before after : LF.StoreState}
    {label : LF.MultiStoreMachineLabel}
    (hStep :
      LF.MultiStoreMachineStep
        declaredVariables
        logicalActions
        messageReactions
        before
        label
        after)
    (hCurrent :
      before.currentTag.microstep =
        0)
    (hPending :
      LF.StoreState.PendingMicrostepsZero
        before) :
    after.currentTag.microstep =
      0 := by

  cases hStep with

  | statement hStatement =>
      cases hStatement with

      | assign
          currentTag
          stateStore
          pendingActions
          target
          expression
          evaluatedValue
          remaining
          hTarget
          hEvaluate =>

          exact hCurrent

      | schedule
          currentTag
          stateStore
          pendingActions
          targetAction
          delay
          remaining
          hTarget =>

          exact hCurrent

  | dispatch hDispatch =>
      cases hDispatch with

      | fire
          currentTag
          stateStore
          pendingActions
          remainingActions
          selectedAction
          selectedReaction
          hReactionDeclared
          hRemoved
          hPriorityEligible
          hNotPast
          hTrigger =>

          exact
            hPending
              _
              (Occurrence.RemovesOne.selected_mem
                hRemoved)

/--
One corresponding generated-LF machine step preserves the full target
priority runtime invariant.

Positive-delay source timing supplies preservation of queued-action
microstep zero. The preceding theorem supplies preservation of the current
tag's microstep.
-/
theorem targetMultiStoreMachineStep_preserves_priorityRuntimeInvariant
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState targetStateAfter : LF.StoreState}
    {targetLabel : LF.MultiStoreMachineLabel}
    (hTargetStep :
      LF.MultiStoreMachineStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hSourceTiming :
      DTR.Body.PriorityTimingWellFormed
        sourceState.activeBody)
    (hTargetInvariant :
      LF.StoreState.PriorityRuntimeInvariant
        targetState) :
    LF.StoreState.PriorityRuntimeInvariant
      targetStateAfter := by

  exact {
    currentMicrostepZero :=
      targetMultiStoreMachineStep_preserves_currentMicrostepZero
        hTargetStep
        hTargetInvariant.currentMicrostepZero
        hTargetInvariant.pendingMicrostepsZero

    pendingMicrostepsZero :=
      targetMultiStoreMachineStep_preserves_pendingMicrostepsZero
        hTargetStep
        hStates
        hSourceTiming
        hTargetInvariant.pendingMicrostepsZero
  }

/--
A source priority-aware dispatch from corresponding states automatically
satisfies the existing forward dispatch compatibility predicate when the
target priority runtime invariant holds.

Queue correspondence identifies the matching target occurrence and residual
queue. Source earliest-time eligibility transports to target earliest-tag
eligibility because all queued target occurrences have microstep zero.

The source not-past premise transports to the LF complete-tag order. At equal
metric time, both the current tag and selected action have microstep zero.
-/
theorem storeForwardDispatchCompatible_of_priorityRuntimeInvariant
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {targetBefore : LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hStates :
      StoreStateCorresponds
        sourceBefore
        targetBefore)
    (hTargetInvariant :
      LF.StoreState.PriorityRuntimeInvariant
        targetBefore) :
    StoreForwardDispatchCompatible
      selectedMessage
      sourceAfter.pendingMessages
      targetBefore := by

  cases hSourceDispatch with

  | fire
      currentTime
      stateStore
      pendingMessages
      remainingMessages
      selectedMessage
      selectedServer
      hServerDeclared
      hRemoved
      hPriorityEligible
      hNotPast
      hTarget =>

      rcases
          QueueCorresponds.remove_source
            hStates.pendingEvents
            hRemoved
        with
          ⟨selectedAction,
           targetRemaining,
           hTargetRemoved,
           hSelectedCorresponds,
           hRemainingCorresponds⟩

      have hTargetSelected :
          selectedAction ∈
            targetBefore.pendingActions :=

        Occurrence.RemovesOne.selected_mem
          hTargetRemoved

      have hTargetEarliest :
          LF.IsEarliest
            selectedAction
            targetBefore.pendingActions :=

        sourceEarliest_implies_targetEarliest_of_allMicrostepsZero
          hStates.pendingEvents
          hSelectedCorresponds
          hTargetSelected
          (DTR.IsPriorityEligible.isEarliest
            hPriorityEligible)
          hTargetInvariant.pendingMicrostepsZero

      have hSelectedMicrostepZero :
          selectedAction.tag.microstep =
            0 :=

        hTargetInvariant.pendingMicrostepsZero
          selectedAction
          hTargetSelected

      have hTargetTimeOrder :
          targetBefore.currentTag.time ≤
            selectedAction.tag.time := by

        calc
          targetBefore.currentTag.time =
              currentTime :=
            hStates.currentTime

          _ ≤ selectedMessage.arrivalTime :=
            hNotPast

          _ = selectedAction.tag.time :=
            hSelectedCorresponds.logicalTime.symm

      have hTargetNotPast :
          LF.Tag.PrecedesOrEqual
            targetBefore.currentTag
            selectedAction.tag := by

        rcases
            Nat.lt_or_eq_of_le
              hTargetTimeOrder
          with
            hEarlier | hSameTime

        · exact
            Or.inl
              hEarlier

        · exact
            Or.inr
              ⟨hSameTime,
               by
                 simpa [
                   hTargetInvariant.currentMicrostepZero,
                   hSelectedMicrostepZero
                 ]⟩

      exact
        ⟨selectedAction,
         targetRemaining,
         hTargetRemoved,
         hSelectedCorresponds,
         hRemainingCorresponds,
         hTargetEarliest,
         hTargetNotPast⟩

/--
The future-time detailed forward phase obtains its scheduler premise from the
full target priority runtime invariant.
-/
theorem concreteDetailedForward_timeAdvance_phaseCompatible
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore : LF.StoreState}
    (hStates :
      ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hTargetInvariant :
      LF.StoreState.PriorityRuntimeInvariant
        targetBefore) :
    ConcreteDetailedForwardPhaseCompatible
      (.stable sourceBefore)
      (.timeAdvance
        sourceBefore.currentTime
        sourceAfter.currentTime)
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        sourceDispatch)
      (.stable targetBefore) := by

  simpa [
    ConcreteDetailedForwardPhaseCompatible
  ] using
    storeForwardDispatchCompatible_of_priorityRuntimeInvariant
      sourceDispatch
      (concreteDetailed_stable_iff.mp
        hStates)
      hTargetInvariant

/--
The same-time direct-consumption detailed forward phase obtains its scheduler
premise from the full target priority runtime invariant.
-/
theorem concreteDetailedForward_consumeNow_phaseCompatible
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    (sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    {targetBefore : LF.StoreState}
    (hStates :
      ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hTargetInvariant :
      LF.StoreState.PriorityRuntimeInvariant
        targetBefore) :
    ConcreteDetailedForwardPhaseCompatible
      (messageServers :=
        messageServers)
      (.stable sourceBefore)
      (.consume
        selectedMessage
        selectedServer)
      (.stable sourceAfter)
      (.stable targetBefore) := by

  simpa [
    ConcreteDetailedForwardPhaseCompatible
  ] using
    storeForwardDispatchCompatible_of_priorityRuntimeInvariant
      sourceDispatch
      (concreteDetailed_stable_iff.mp
        hStates)
      hTargetInvariant

end Correctness
end Relico
