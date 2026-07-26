import Relico.Correctness.DetailedMultiStoreRefinement
import Relico.DTR.DetailedWeakSemantics
import Relico.LF.DetailedWeakSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

theorem dtrDetailed_dispatch_future_observable
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {before after : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    (hDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after)
    (hFuture :
      before.currentTime < after.currentTime) :
    ∃ labels,
      DTR.DetailedMultiStoreSteps
          declaredVariables
          messageServers
          (.stable before)
          labels
          (.stable after) ∧
        DTR.detailedObservableTrace labels =
          [
            DTR.DetailedMultiStoreObservable.timeAdvance
              before.currentTime
              after.currentTime,
            DTR.DetailedMultiStoreObservable.consume
              selectedMessage.name
              selectedMessage.arrivalTime
          ] := by
  refine
    ⟨[
        DTR.DetailedMultiStoreLabel.timeAdvance
          before.currentTime
          after.currentTime,
        DTR.DetailedMultiStoreLabel.consume
          selectedMessage
          selectedServer
      ],
     ?_,
     rfl⟩
  exact
    Correctness.dtrDetailed_dispatch_future
      hDispatch
      hFuture

theorem dtrDetailed_dispatch_sameTime_observable
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {before after : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    (hDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after)
    (hSameTime :
      before.currentTime = after.currentTime) :
    ∃ labels,
      DTR.DetailedMultiStoreSteps
          declaredVariables
          messageServers
          (.stable before)
          labels
          (.stable after) ∧
        DTR.detailedObservableTrace labels =
          [
            DTR.DetailedMultiStoreObservable.consume
              selectedMessage.name
              selectedMessage.arrivalTime
          ] := by
  refine
    ⟨[
        DTR.DetailedMultiStoreLabel.consume
          selectedMessage
          selectedServer
      ],
     ?_,
     rfl⟩
  exact
    Correctness.dtrDetailed_dispatch_sameTime
      hDispatch
      hSameTime

theorem lfDetailed_dispatch_future_zero_observable
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (hFuture :
      before.currentTag.time < after.currentTag.time)
    (hZeroMicrostep :
      after.currentTag.microstep = 0) :
    ∃ labels,
      LF.DetailedMultiStoreSteps
          declaredVariables
          logicalActions
          messageReactions
          (.stable before)
          labels
          (.stable after) ∧
        LF.detailedObservableTrace labels =
          [
            LF.DetailedMultiStoreObservable.timeAdvance
              before.currentTag.time
              after.currentTag.time,
            LF.DetailedMultiStoreObservable.consume
              selectedAction.name
              selectedAction.tag.time
          ] := by
  refine
    ⟨[
        LF.DetailedMultiStoreLabel.timeAdvance
          before.currentTag.time
          after.currentTag.time,
        LF.DetailedMultiStoreLabel.consume
          selectedAction
          selectedReaction
      ],
     ?_,
     rfl⟩
  exact
    Correctness.lfDetailed_dispatch_future_zero
      hDispatch
      hFuture
      hZeroMicrostep

theorem lfDetailed_dispatch_future_positive_observable
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (hFuture :
      before.currentTag.time < after.currentTag.time)
    (hPositiveMicrostep :
      0 < after.currentTag.microstep) :
    ∃ labels,
      LF.DetailedMultiStoreSteps
          declaredVariables
          logicalActions
          messageReactions
          (.stable before)
          labels
          (.stable after) ∧
        LF.detailedObservableTrace labels =
          [
            LF.DetailedMultiStoreObservable.timeAdvance
              before.currentTag.time
              after.currentTag.time,
            LF.DetailedMultiStoreObservable.consume
              selectedAction.name
              selectedAction.tag.time
          ] := by
  refine
    ⟨[
        LF.DetailedMultiStoreLabel.timeAdvance
          before.currentTag.time
          after.currentTag.time,
        LF.DetailedMultiStoreLabel.microstepAdvance
          {
            time := after.currentTag.time
            microstep := 0
          }
          after.currentTag,
        LF.DetailedMultiStoreLabel.consume
          selectedAction
          selectedReaction
      ],
     ?_,
     rfl⟩
  exact
    Correctness.lfDetailed_dispatch_future_positiveMicrostep
      hDispatch
      hFuture
      hPositiveMicrostep

theorem lfDetailed_dispatch_laterMicrostep_observable
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (hSameTime :
      before.currentTag.time = after.currentTag.time)
    (hLaterMicrostep :
      before.currentTag.microstep <
        after.currentTag.microstep) :
    ∃ labels,
      LF.DetailedMultiStoreSteps
          declaredVariables
          logicalActions
          messageReactions
          (.stable before)
          labels
          (.stable after) ∧
        LF.detailedObservableTrace labels =
          [
            LF.DetailedMultiStoreObservable.consume
              selectedAction.name
              selectedAction.tag.time
          ] := by
  refine
    ⟨[
        LF.DetailedMultiStoreLabel.microstepAdvance
          before.currentTag
          after.currentTag,
        LF.DetailedMultiStoreLabel.consume
          selectedAction
          selectedReaction
      ],
     ?_,
     rfl⟩
  exact
    Correctness.lfDetailed_dispatch_laterMicrostep
      hDispatch
      hSameTime
      hLaterMicrostep

theorem lfDetailed_dispatch_sameTag_observable
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (hSameTime :
      before.currentTag.time = after.currentTag.time)
    (hSameMicrostep :
      before.currentTag.microstep =
        after.currentTag.microstep) :
    ∃ labels,
      LF.DetailedMultiStoreSteps
          declaredVariables
          logicalActions
          messageReactions
          (.stable before)
          labels
          (.stable after) ∧
        LF.detailedObservableTrace labels =
          [
            LF.DetailedMultiStoreObservable.consume
              selectedAction.name
              selectedAction.tag.time
          ] := by
  refine
    ⟨[
        LF.DetailedMultiStoreLabel.consume
          selectedAction
          selectedReaction
      ],
     ?_,
     rfl⟩
  exact
    Correctness.lfDetailed_dispatch_sameTag
      hDispatch
      hSameTime
      hSameMicrostep

end Correctness
end Relico
