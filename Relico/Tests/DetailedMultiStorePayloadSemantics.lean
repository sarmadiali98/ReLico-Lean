import Relico.DTR.DetailedMultiStorePayloadSemantics
import Relico.LF.DetailedMultiStorePayloadSemantics

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedMultiStorePayloadSemantics

theorem dtr_statement_is_internal
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    (statementStep :
      DTR.MultiStorePayloadStep
        before
        after) :
    DTR.DetailedMultiStorePayloadStep
      messageServers
      (.stable before)
      .tau
      (.stable after) :=

  DTR.DetailedMultiStorePayloadStep.statement
    statementStep

theorem dtr_future_dispatch_exposes_time
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (dispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after)
    (future :
      before.currentTime <
        after.currentTime) :
    DTR.DetailedMultiStorePayloadStep
      messageServers
      (.stable before)
      (.timeAdvance
        before.currentTime
        after.currentTime)
      (.dispatchReady
        before
        selectedMessage
        selectedServer
        after
        dispatch) :=

  DTR.DetailedMultiStorePayloadStep.timeAdvance
    dispatch
    future

theorem dtr_ready_dispatch_consumes
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (dispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    DTR.DetailedMultiStorePayloadStep
      messageServers
      (.dispatchReady
        before
        selectedMessage
        selectedServer
        after
        dispatch)
      (.consume
        selectedMessage
        selectedServer)
      (.stable after) :=

  DTR.DetailedMultiStorePayloadStep.consumeReady
    dispatch

theorem dtr_same_time_dispatch_consumes_now
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (dispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after)
    (sameTime :
      before.currentTime =
        after.currentTime) :
    DTR.DetailedMultiStorePayloadStep
      messageServers
      (.stable before)
      (.consume
        selectedMessage
        selectedServer)
      (.stable after) :=

  DTR.DetailedMultiStorePayloadStep.consumeNow
    dispatch
    sameTime

theorem lf_statement_is_internal
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    (statementStep :
      LF.MultiStorePayloadStep
        before
        after) :
    LF.DetailedMultiStorePayloadStep
      messageReactions
      (.stable before)
      .tau
      (.stable after) :=

  LF.DetailedMultiStorePayloadStep.statement
    statementStep

theorem lf_future_dispatch_exposes_time
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (dispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (future :
      before.currentTag.time <
        after.currentTag.time) :
    LF.DetailedMultiStorePayloadStep
      messageReactions
      (.stable before)
      (.timeAdvance
        before.currentTag.time
        after.currentTag.time)
      (.afterTime
        before
        selectedAction
        selectedReaction
        after
        dispatch) :=

  LF.DetailedMultiStorePayloadStep.timeAdvance
    dispatch
    future

theorem lf_future_microstep_is_explicit
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (dispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (positiveMicrostep :
      0 <
        after.currentTag.microstep) :
    LF.DetailedMultiStorePayloadStep
      messageReactions
      (.afterTime
        before
        selectedAction
        selectedReaction
        after
        dispatch)
      (.microstepAdvance
        {
          time :=
            after.currentTag.time

          microstep :=
            0
        }
        after.currentTag)
      (.dispatchReady
        before
        selectedAction
        selectedReaction
        after
        dispatch) :=

  LF.DetailedMultiStorePayloadStep.microstepAfterTime
    dispatch
    positiveMicrostep

theorem lf_after_time_zero_consumes
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (dispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (zeroMicrostep :
      after.currentTag.microstep =
        0) :
    LF.DetailedMultiStorePayloadStep
      messageReactions
      (.afterTime
        before
        selectedAction
        selectedReaction
        after
        dispatch)
      (.consume
        selectedAction
        selectedReaction)
      (.stable after) :=

  LF.DetailedMultiStorePayloadStep.consumeAfterTimeZero
    dispatch
    zeroMicrostep

theorem lf_same_time_microstep_is_target_only
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (dispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (sameTime :
      before.currentTag.time =
        after.currentTag.time)
    (laterMicrostep :
      before.currentTag.microstep <
        after.currentTag.microstep) :
    LF.DetailedMultiStorePayloadStep
      messageReactions
      (.stable before)
      (.microstepAdvance
        before.currentTag
        after.currentTag)
      (.dispatchReady
        before
        selectedAction
        selectedReaction
        after
        dispatch) :=

  LF.DetailedMultiStorePayloadStep.microstepSameTime
    dispatch
    sameTime
    laterMicrostep

theorem lf_ready_dispatch_consumes
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (dispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    LF.DetailedMultiStorePayloadStep
      messageReactions
      (.dispatchReady
        before
        selectedAction
        selectedReaction
        after
        dispatch)
      (.consume
        selectedAction
        selectedReaction)
      (.stable after) :=

  LF.DetailedMultiStorePayloadStep.consumeReady
    dispatch

theorem lf_same_complete_tag_consumes_now
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (dispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (sameTime :
      before.currentTag.time =
        after.currentTag.time)
    (sameMicrostep :
      before.currentTag.microstep =
        after.currentTag.microstep) :
    LF.DetailedMultiStorePayloadStep
      messageReactions
      (.stable before)
      (.consume
        selectedAction
        selectedReaction)
      (.stable after) :=

  LF.DetailedMultiStorePayloadStep.consumeNow
    dispatch
    sameTime
    sameMicrostep

end DetailedMultiStorePayloadSemantics
end Tests
end Relico
