import Relico.DTR.DetailedMultiStorePayloadWeakSemantics
import Relico.LF.DetailedMultiStorePayloadWeakSemantics

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedMultiStorePayloadWeakSemantics

theorem dtr_weak_tau_is_reflexive
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (state :
      DTR.DetailedMultiStorePayloadState
        messageServers) :
    DTR.DetailedMultiStorePayloadWeakStep
      messageServers
      state
      .tau
      state :=

  DTR.detailedMultiStorePayloadWeakTau_refl
    state

theorem dtr_statement_is_weak_tau
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    (statementStep :
      DTR.MultiStorePayloadStep
        before
        after) :
    DTR.DetailedMultiStorePayloadWeakStep
      messageServers
      (.stable before)
      .tau
      (.stable after) :=

  DTR.detailedMultiStorePayloadStatement_is_weak
    statementStep

theorem dtr_time_advance_is_weak
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
    DTR.DetailedMultiStorePayloadWeakStep
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

  DTR.detailedMultiStorePayloadTimeAdvance_is_weak
    (DTR.DetailedMultiStorePayloadStep.timeAdvance
      dispatch
      future)

theorem dtr_ready_consumption_is_weak
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
    DTR.DetailedMultiStorePayloadWeakStep
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

  DTR.detailedMultiStorePayloadConsume_is_weak
    (DTR.DetailedMultiStorePayloadStep.consumeReady
      dispatch)

theorem lf_weak_tau_is_reflexive
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    (state :
      LF.DetailedMultiStorePayloadState
        messageReactions) :
    LF.DetailedMultiStorePayloadWeakStep
      messageReactions
      state
      .tau
      state :=

  LF.detailedMultiStorePayloadWeakTau_refl
    state

theorem lf_statement_is_weak_tau
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    (statementStep :
      LF.MultiStorePayloadStep
        before
        after) :
    LF.DetailedMultiStorePayloadWeakStep
      messageReactions
      (.stable before)
      .tau
      (.stable after) :=

  LF.detailedMultiStorePayloadStatement_is_weak
    statementStep

theorem lf_same_time_microstep_is_internal
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
    LF.DetailedMultiStorePayloadTauSteps
      messageReactions
      (.stable before)
      (.dispatchReady
        before
        selectedAction
        selectedReaction
        after
        dispatch) :=

  LF.detailedMultiStorePayloadMicrostep_to_tauSteps
    (LF.DetailedMultiStorePayloadStep.microstepSameTime
      dispatch
      sameTime
      laterMicrostep)

theorem lf_after_time_microstep_is_internal
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
    LF.DetailedMultiStorePayloadTauSteps
      messageReactions
      (.afterTime
        before
        selectedAction
        selectedReaction
        after
        dispatch)
      (.dispatchReady
        before
        selectedAction
        selectedReaction
        after
        dispatch) :=

  LF.detailedMultiStorePayloadMicrostep_to_tauSteps
    (LF.DetailedMultiStorePayloadStep.microstepAfterTime
      dispatch
      positiveMicrostep)

theorem lf_time_advance_is_weak
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
    LF.DetailedMultiStorePayloadWeakStep
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

  LF.detailedMultiStorePayloadTimeAdvance_is_weak
    (LF.DetailedMultiStorePayloadStep.timeAdvance
      dispatch
      future)

theorem lf_positive_microstep_consumption_is_weak
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
    LF.DetailedMultiStorePayloadWeakStep
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

  LF.detailedMultiStorePayloadConsumeAfterTimePositive_is_weak
    dispatch
    positiveMicrostep

theorem lf_same_time_microstep_then_consumption_is_weak
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
    LF.DetailedMultiStorePayloadWeakStep
      messageReactions
      (.stable before)
      (.consume
        selectedAction
        selectedReaction)
      (.stable after) :=

  LF.detailedMultiStorePayloadSameTimeMicrostepThenConsume_is_weak
    dispatch
    sameTime
    laterMicrostep

theorem lf_direct_consumption_is_weak
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
    LF.DetailedMultiStorePayloadWeakStep
      messageReactions
      (.stable before)
      (.consume
        selectedAction
        selectedReaction)
      (.stable after) :=

  LF.detailedMultiStorePayloadConsume_is_weak
    (LF.DetailedMultiStorePayloadStep.consumeNow
      dispatch
      sameTime
      sameMicrostep)

end DetailedMultiStorePayloadWeakSemantics
end Tests
end Relico
