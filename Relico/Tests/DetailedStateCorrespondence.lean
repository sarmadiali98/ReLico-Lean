import Relico.Correctness.DetailedStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedStateCorrespondence

theorem stable_constructor
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
    {dtrState : DTR.StoreState}
    {lfState : LF.StoreState}
    (hStable :
      stableRel
        dtrState
        lfState) :
    Correctness.DetailedStateCorresponds
      stableRel
      messageRel
      handlerRel
      messageServers
      messageReactions
      (.stable dtrState)
      (.stable lfState) := by

  exact
    Correctness.DetailedStateCorresponds.stable
      hStable

theorem stable_inversion
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
    {dtrState : DTR.StoreState}
    {lfState : LF.StoreState}
    (hCorresponds :
      Correctness.DetailedStateCorresponds
        stableRel
        messageRel
        handlerRel
        messageServers
        messageReactions
        (.stable dtrState)
        (.stable lfState)) :
    stableRel
      dtrState
      lfState := by

  exact
    Correctness.DetailedStateCorresponds.stable_iff.mp
      hCorresponds

theorem future_afterTime_constructor
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
      Correctness.DetailedDispatchWitnessCorresponds
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
    Correctness.DetailedStateCorresponds
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
    Correctness.DetailedStateCorresponds.future_afterTime
      hDtrFuture
      hLfFuture
      hWitness

theorem future_ready_constructor
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
      Correctness.DetailedDispatchWitnessCorresponds
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
    Correctness.DetailedStateCorresponds
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
    Correctness.DetailedStateCorresponds.future_ready
      hDtrFuture
      hLfFuture
      hPositiveMicrostep
      hWitness

theorem sameTime_microstepAhead_constructor
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
      Correctness.DetailedDispatchWitnessCorresponds
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
    Correctness.DetailedStateCorresponds
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
    Correctness.DetailedStateCorresponds.sameTime_microstepAhead
      dtrDispatch
      hDtrSameTime
      hLfSameTime
      hLfLaterMicrostep
      hWitness

end DetailedStateCorrespondence
end Tests
end Relico
