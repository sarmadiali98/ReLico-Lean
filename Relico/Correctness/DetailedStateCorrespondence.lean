import Relico.Correctness.DetailedWeakFoundation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Cross-language correspondence data for one selected dispatch.

The relation is parameterized by the existing stable-state, pending-event,
and handler correspondence predicates. Subsequent checkpoints instantiate
those parameters with the executable translation correctness relations.
-/
structure DetailedDispatchWitnessCorresponds
    (stableRel :
      DTR.StoreState →
      LF.StoreState →
      Prop)
    (messageRel :
      DTR.PendingMessage →
      LF.PendingAction →
      Prop)
    (handlerRel :
      DTR.MessageServer →
      LF.Reaction →
      Prop)
    (dtrBefore : DTR.StoreState)
    (selectedMessage : DTR.PendingMessage)
    (selectedServer : DTR.MessageServer)
    (dtrAfter : DTR.StoreState)
    (lfBefore : LF.StoreState)
    (selectedAction : LF.PendingAction)
    (selectedReaction : LF.Reaction)
    (lfAfter : LF.StoreState) :
    Prop where

  beforeState :
    stableRel
      dtrBefore
      lfBefore

  selectedOccurrence :
    messageRel
      selectedMessage
      selectedAction

  selectedHandler :
    handlerRel
      selectedServer
      selectedReaction

  afterState :
    stableRel
      dtrAfter
      lfAfter

/--
Phase-aware correspondence between detailed DTR and generated-LF states.

There are four supported configurations.

1. Stable DTR and LF states correspond through `stableRel`.
2. After matching future metric-time transitions, DTR is dispatch-ready while
   LF is in its `afterTime` phase.
3. After the LF internal microstep phase, both sides are dispatch-ready.
4. For same-metric-time dispatch to a later LF microstep, DTR remains stable
   while LF internally reaches its dispatch-ready phase.

The fourth constructor is the stuttering configuration needed for weak
simulation: the LF microstep transition is internal and does not require a
DTR transition.
-/
inductive DetailedStateCorresponds
    (stableRel :
      DTR.StoreState →
      LF.StoreState →
      Prop)
    (messageRel :
      DTR.PendingMessage →
      LF.PendingAction →
      Prop)
    (handlerRel :
      DTR.MessageServer →
      LF.Reaction →
      Prop)
    (messageServers :
      List DTR.MessageServer)
    (messageReactions :
      List LF.Reaction) :
    DTR.DetailedMultiStoreState
        messageServers →
    LF.DetailedMultiStoreState
        messageReactions →
    Prop where

  | stable
      {dtrState : DTR.StoreState}
      {lfState : LF.StoreState}
      (hStable :
        stableRel
          dtrState
          lfState) :
      DetailedStateCorresponds
        stableRel
        messageRel
        handlerRel
        messageServers
        messageReactions
        (.stable dtrState)
        (.stable lfState)

  | futureAfterTime
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
          messageReactions
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
      (hWitness :
        DetailedDispatchWitnessCorresponds
          stableRel
          messageRel
          handlerRel
          dtrBefore
          selectedMessage
          selectedServer
          dtrAfter
          lfBefore
          selectedAction
          selectedReaction
          lfAfter) :
      DetailedStateCorresponds
        stableRel
        messageRel
        handlerRel
        messageServers
        messageReactions
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
          lfDispatch)

  | futureReady
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
          messageReactions
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
        DetailedDispatchWitnessCorresponds
          stableRel
          messageRel
          handlerRel
          dtrBefore
          selectedMessage
          selectedServer
          dtrAfter
          lfBefore
          selectedAction
          selectedReaction
          lfAfter) :
      DetailedStateCorresponds
        stableRel
        messageRel
        handlerRel
        messageServers
        messageReactions
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
          lfDispatch)

  | sameTimeMicrostepAhead
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
          messageReactions
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
        DetailedDispatchWitnessCorresponds
          stableRel
          messageRel
          handlerRel
          dtrBefore
          selectedMessage
          selectedServer
          dtrAfter
          lfBefore
          selectedAction
          selectedReaction
          lfAfter) :
      DetailedStateCorresponds
        stableRel
        messageRel
        handlerRel
        messageServers
        messageReactions
        (.stable dtrBefore)
        (.dispatchReady
          lfBefore
          selectedAction
          selectedReaction
          lfAfter
          lfDispatch)

namespace DetailedStateCorresponds

variable
    {stableRel :
      DTR.StoreState →
      LF.StoreState →
      Prop}
    {messageRel :
      DTR.PendingMessage →
      LF.PendingAction →
      Prop}
    {handlerRel :
      DTR.MessageServer →
      LF.Reaction →
      Prop}
    {messageServers :
      List DTR.MessageServer}
    {messageReactions :
      List LF.Reaction}

/--
Correspondence between two stable detailed states is exactly the supplied
stable-state relation.
-/
theorem stable_iff
    {dtrState : DTR.StoreState}
    {lfState : LF.StoreState} :
    DetailedStateCorresponds
          stableRel
          messageRel
          handlerRel
          messageServers
          messageReactions
          (.stable dtrState)
          (.stable lfState) ↔
      stableRel
        dtrState
        lfState := by

  constructor

  · intro hCorresponds

    cases hCorresponds with

    | stable hStable =>
        exact hStable

  · intro hStable

    exact
      DetailedStateCorresponds.stable
        hStable

/--
Construct correspondence immediately after matching future metric-time
transitions.
-/
theorem future_afterTime
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
        messageReactions
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
    (hWitness :
      DetailedDispatchWitnessCorresponds
        stableRel
        messageRel
        handlerRel
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    DetailedStateCorresponds
      stableRel
      messageRel
      handlerRel
      messageServers
      messageReactions
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
        lfDispatch) := by

  exact
    DetailedStateCorresponds.futureAfterTime
      hDtrFuture
      hLfFuture
      hWitness

/--
Construct correspondence after the generated-LF internal microstep phase of a
future dispatch.
-/
theorem future_ready
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
        messageReactions
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
      DetailedDispatchWitnessCorresponds
        stableRel
        messageRel
        handlerRel
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    DetailedStateCorresponds
      stableRel
      messageRel
      handlerRel
      messageServers
      messageReactions
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
    DetailedStateCorresponds.futureReady
      hDtrFuture
      hLfFuture
      hPositiveMicrostep
      hWitness

/--
Construct the stuttering correspondence used when LF internally advances to a
later microstep before matching a same-time DTR consumption transition.
-/
theorem sameTime_microstepAhead
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
        messageReactions
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
      DetailedDispatchWitnessCorresponds
        stableRel
        messageRel
        handlerRel
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    DetailedStateCorresponds
      stableRel
      messageRel
      handlerRel
      messageServers
      messageReactions
      (.stable dtrBefore)
      (.dispatchReady
        lfBefore
        selectedAction
        selectedReaction
        lfAfter
        lfDispatch) := by

  exact
    DetailedStateCorresponds.sameTimeMicrostepAhead
      dtrDispatch
      hDtrSameTime
      hLfSameTime
      hLfLaterMicrostep
      hWitness

end DetailedStateCorresponds

end Correctness
end Relico
