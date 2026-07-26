import Relico.Correctness.DetailedStateCorrespondence
import Relico.Correctness.MultiStoreForward
import Relico.Correctness.MultiStoreBackward
import Relico.Correctness.MultiStoreDispatch

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Concrete correspondence between a source message server and the generated LF
reaction produced by the executable translator.
-/
def CompiledMessageReactionCorresponds
    (sourceServer : DTR.MessageServer)
    (targetReaction : LF.Reaction) :
    Prop :=
  targetReaction =
    Translation.compileMessageReaction
      sourceServer

/--
Concrete specialization of the phase-level dispatch witness.

It uses the existing executable multi-store correspondence relations:

- `StoreStateCorresponds`;
- `PendingCorresponds`;
- `CompiledMessageReactionCorresponds`.
-/
abbrev ConcreteDetailedDispatchWitnessCorresponds
    (dtrBefore : DTR.StoreState)
    (selectedMessage : DTR.PendingMessage)
    (selectedServer : DTR.MessageServer)
    (dtrAfter : DTR.StoreState)
    (lfBefore : LF.StoreState)
    (selectedAction : LF.PendingAction)
    (selectedReaction : LF.Reaction)
    (lfAfter : LF.StoreState) :
    Prop :=
  DetailedDispatchWitnessCorresponds
    StoreStateCorresponds
    PendingCorresponds
    CompiledMessageReactionCorresponds
    dtrBefore
    selectedMessage
    selectedServer
    dtrAfter
    lfBefore
    selectedAction
    selectedReaction
    lfAfter

/--
Concrete specialization of detailed cross-language state correspondence for
the executable multi-store translator.
-/
abbrev ConcreteDetailedStateCorresponds
    (messageServers : List DTR.MessageServer) :
    DTR.DetailedMultiStoreState
        messageServers →
    LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers) →
    Prop :=
  DetailedStateCorresponds
    StoreStateCorresponds
    PendingCorresponds
    CompiledMessageReactionCorresponds
    messageServers
    (Translation.compileMessageReactions
      messageServers)

/--
Concrete stable-state correspondence is exactly the established executable
store-state relation.
-/
theorem concreteDetailed_stable_iff
    {messageServers : List DTR.MessageServer}
    {dtrState : DTR.StoreState}
    {lfState : LF.StoreState} :
    ConcreteDetailedStateCorresponds
          messageServers
          (.stable dtrState)
          (.stable lfState) ↔
      StoreStateCorresponds
        dtrState
        lfState := by

  exact
    DetailedStateCorresponds.stable_iff

/--
Construct a concrete detailed dispatch witness from the established
multi-store correspondence facts.
-/
theorem concreteDetailedDispatchWitness_mk
    {dtrBefore dtrAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {lfBefore lfAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hBefore :
      StoreStateCorresponds
        dtrBefore
        lfBefore)
    (hSelected :
      PendingCorresponds
        selectedMessage
        selectedAction)
    (hReaction :
      selectedReaction =
        Translation.compileMessageReaction
          selectedServer)
    (hAfter :
      StoreStateCorresponds
        dtrAfter
        lfAfter) :
    ConcreteDetailedDispatchWitnessCorresponds
      dtrBefore
      selectedMessage
      selectedServer
      dtrAfter
      lfBefore
      selectedAction
      selectedReaction
      lfAfter := by

  exact {
    beforeState :=
      hBefore

    selectedOccurrence :=
      hSelected

    selectedHandler :=
      hReaction

    afterState :=
      hAfter
  }

/--
A concrete dispatch witness preserves metric time before and after dispatch.
-/
theorem concreteDetailedDispatchWitness_times
    {dtrBefore dtrAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {lfBefore lfAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hWitness :
      ConcreteDetailedDispatchWitnessCorresponds
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    lfBefore.currentTag.time =
        dtrBefore.currentTime ∧
      lfAfter.currentTag.time =
        dtrAfter.currentTime := by

  exact
    ⟨hWitness.beforeState.currentTime,
     hWitness.afterState.currentTime⟩

/--
A concrete dispatch witness identifies the translated selected occurrence.
-/
theorem concreteDetailedDispatchWitness_occurrence
    {dtrBefore dtrAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {lfBefore lfAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hWitness :
      ConcreteDetailedDispatchWitnessCorresponds
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    selectedAction.name =
          Translation.actionNameFor
            selectedMessage.name ∧
      selectedAction.tag.time =
          selectedMessage.arrivalTime := by

  exact
    ⟨hWitness.selectedOccurrence.actionName,
     hWitness.selectedOccurrence.logicalTime⟩

/--
A concrete dispatch witness identifies the exact generated reaction.
-/
theorem concreteDetailedDispatchWitness_reaction
    {dtrBefore dtrAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {lfBefore lfAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hWitness :
      ConcreteDetailedDispatchWitnessCorresponds
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    selectedReaction =
      Translation.compileMessageReaction
        selectedServer := by

  exact
    hWitness.selectedHandler

/--
Forward preservation of concrete detailed correspondence across one internal
DTR statement transition.

The established executable statement theorem supplies the matching LF
statement transition and the corresponding stable post-state.
-/
theorem concreteDetailed_statement_forward
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {sourceLabel : DTR.Label}
    {targetBefore : LF.StoreState}
    (hSourceStep :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    ∃ targetLabel targetAfter,
      LF.MultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          targetBefore
          targetLabel
          targetAfter ∧
        LabelCorresponds
          sourceLabel
          targetLabel ∧
        LF.DetailedMultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          (.stable targetBefore)
          .tau
          (.stable targetAfter) ∧
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceAfter)
          (.stable targetAfter) := by

  have hStable :
      StoreStateCorresponds
        sourceBefore
        targetBefore :=
    concreteDetailed_stable_iff.mp
      hStates

  rcases
      multiStore_step_forward
        hSourceStep
        hStable
    with
      ⟨targetLabel,
       targetAfter,
       hTargetStep,
       hLabels,
       hFinalStates⟩

  exact
    ⟨targetLabel,
     targetAfter,
     hTargetStep,
     hLabels,
     LF.DetailedMultiStoreStep.statement
       hTargetStep,
     DetailedStateCorresponds.stable
       hFinalStates⟩

/--
Backward preservation of concrete detailed correspondence across one internal
generated-LF statement transition.
-/
theorem concreteDetailed_statement_backward
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {targetLabel : LF.Label}
    (hTargetStep :
      LF.MultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hSourceBodyWellFormed :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceBefore.activeBody) :
    ∃ sourceLabel sourceAfter,
      DTR.MultiStoreStep
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          sourceBefore
          sourceLabel
          sourceAfter ∧
        LabelCorresponds
          sourceLabel
          targetLabel ∧
        DTR.DetailedMultiStoreStep
          declaredVariables
          messageServers
          (.stable sourceBefore)
          .tau
          (.stable sourceAfter) ∧
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceAfter)
          (.stable targetAfter) := by

  have hStable :
      StoreStateCorresponds
        sourceBefore
        targetBefore :=
    concreteDetailed_stable_iff.mp
      hStates

  rcases
      multiStore_step_backward
        hTargetStep
        hStable
        hSourceBodyWellFormed
    with
      ⟨sourceLabel,
       sourceAfter,
       hSourceStep,
       hLabels,
       hFinalStates⟩

  exact
    ⟨sourceLabel,
     sourceAfter,
     hSourceStep,
     hLabels,
     DTR.DetailedMultiStoreStep.statement
       hSourceStep,
     DetailedStateCorresponds.stable
       hFinalStates⟩

/--
Concrete wrapper around the established conditional forward dispatch theorem.

The result directly supplies the phase-level witness needed by detailed weak
simulation.
-/
theorem concreteDetailed_dispatch_forward_of_compatible
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
      ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hCompatible :
      StoreForwardDispatchCompatible
        selectedMessage
        sourceAfter.pendingMessages
        targetBefore) :
    ∃ selectedAction selectedReaction targetAfter,
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter ∧
        ConcreteDetailedDispatchWitnessCorresponds
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          selectedReaction
          targetAfter := by

  have hStable :
      StoreStateCorresponds
        sourceBefore
        targetBefore :=
    concreteDetailed_stable_iff.mp
      hStates

  rcases
      multiStore_dispatch_forward_of_compatible
        hSourceDispatch
        hStable
        hCompatible
    with
      ⟨selectedAction,
       selectedReaction,
       targetAfter,
       hTargetDispatch,
       hReaction,
       hPending,
       hFinalStates⟩

  refine
    ⟨selectedAction,
     selectedReaction,
     targetAfter,
     hTargetDispatch,
     ?_⟩

  exact
    concreteDetailedDispatchWitness_mk
      hStable
      hPending
      hReaction
      hFinalStates

/--
Concrete wrapper around the established backward dispatch theorem.
-/
theorem concreteDetailed_dispatch_backward
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hStates :
      ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hTargetMicrostepsZero :
      LF.StoreState.PendingMicrostepsZero
        targetBefore) :
    ∃ selectedMessage sourceServer sourceAfter,
      DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter ∧
        ConcreteDetailedDispatchWitnessCorresponds
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter
          targetBefore
          selectedAction
          selectedReaction
          targetAfter := by

  have hStable :
      StoreStateCorresponds
        sourceBefore
        targetBefore :=
    concreteDetailed_stable_iff.mp
      hStates

  rcases
      multiStore_dispatch_backward
        hTargetDispatch
        hStable
        hTargetMicrostepsZero
    with
      ⟨selectedMessage,
       sourceServer,
       sourceAfter,
       hSourceDispatch,
       hReaction,
       hPending,
       hFinalStates⟩

  refine
    ⟨selectedMessage,
     sourceServer,
     sourceAfter,
     hSourceDispatch,
     ?_⟩

  exact
    concreteDetailedDispatchWitness_mk
      hStable
      hPending
      hReaction
      hFinalStates

/--
Concrete phase preservation for the internal LF microstep following future
metric-time advancement.

The DTR side remains in the same dispatch-ready phase while LF advances
internally from `afterTime` to `dispatchReady`.
-/
theorem concreteDetailed_future_microstep_preserves
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {dtrBefore dtrAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {dtrDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter}
    {lfBefore lfAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    {lfDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        lfBefore
        selectedAction
        selectedReaction
        lfAfter}
    (hDtrFuture :
      dtrBefore.currentTime <
        dtrAfter.currentTime)
    (hLfFuture :
      lfBefore.currentTag.time <
        lfAfter.currentTag.time)
    (hPositiveMicrostep :
      0 <
        lfAfter.currentTag.microstep)
    (hWitness :
      ConcreteDetailedDispatchWitnessCorresponds
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    ConcreteDetailedStateCorresponds
        messageServers
        (.dispatchReady
          dtrBefore
          selectedMessage
          selectedServer
          dtrAfter
          dtrDispatch)
        (.afterTime
          lfBefore
          selectedAction
          selectedReaction
          lfAfter
          lfDispatch) ∧
      LF.DetailedMultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        (.afterTime
          lfBefore
          selectedAction
          selectedReaction
          lfAfter
          lfDispatch)
        (.microstepAdvance
          {
            time :=
              lfAfter.currentTag.time

            microstep :=
              0
          }
          lfAfter.currentTag)
        (.dispatchReady
          lfBefore
          selectedAction
          selectedReaction
          lfAfter
          lfDispatch) ∧
      ConcreteDetailedStateCorresponds
        messageServers
        (.dispatchReady
          dtrBefore
          selectedMessage
          selectedServer
          dtrAfter
          dtrDispatch)
        (.dispatchReady
          lfBefore
          selectedAction
          selectedReaction
          lfAfter
          lfDispatch) := by

  exact
    ⟨DetailedStateCorresponds.futureAfterTime
        hDtrFuture
        hLfFuture
        hWitness,
     LF.DetailedMultiStoreStep.microstepAfterTime
       lfDispatch
       hPositiveMicrostep,
     DetailedStateCorresponds.futureReady
       hDtrFuture
       hLfFuture
       hPositiveMicrostep
       hWitness⟩

/--
Concrete phase preservation for a same-metric-time LF dispatch whose selected
action is at a later microstep.

LF performs an internal microstep transition while DTR stutters in its stable
pre-dispatch state.
-/
theorem concreteDetailed_sameTime_microstep_preserves
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {dtrBefore dtrAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    (dtrDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter)
    {lfBefore lfAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    {lfDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        lfBefore
        selectedAction
        selectedReaction
        lfAfter}
    (hDtrSameTime :
      dtrBefore.currentTime =
        dtrAfter.currentTime)
    (hLfSameTime :
      lfBefore.currentTag.time =
        lfAfter.currentTag.time)
    (hLfLaterMicrostep :
      lfBefore.currentTag.microstep <
        lfAfter.currentTag.microstep)
    (hWitness :
      ConcreteDetailedDispatchWitnessCorresponds
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    ConcreteDetailedStateCorresponds
        messageServers
        (.stable dtrBefore)
        (.stable lfBefore) ∧
      LF.DetailedMultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        (.stable lfBefore)
        (.microstepAdvance
          lfBefore.currentTag
          lfAfter.currentTag)
        (.dispatchReady
          lfBefore
          selectedAction
          selectedReaction
          lfAfter
          lfDispatch) ∧
      ConcreteDetailedStateCorresponds
        messageServers
        (.stable dtrBefore)
        (.dispatchReady
          lfBefore
          selectedAction
          selectedReaction
          lfAfter
          lfDispatch) := by

  exact
    ⟨DetailedStateCorresponds.stable
        hWitness.beforeState,
     LF.DetailedMultiStoreStep.microstepSameTime
       lfDispatch
       hLfSameTime
       hLfLaterMicrostep,
     DetailedStateCorresponds.sameTimeMicrostepAhead
       dtrDispatch
       hDtrSameTime
       hLfSameTime
       hLfLaterMicrostep
       hWitness⟩

end Correctness
end Relico
