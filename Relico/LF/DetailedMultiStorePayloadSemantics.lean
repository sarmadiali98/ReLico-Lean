import Relico.LF.DetailedMultiStorePayloadRuntime
import Relico.LF.MultiStorePayloadSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
Detailed one-step decomposition of the generated payload-aware LF runtime.

Metric-time and microstep progression are separate target transitions.
Microstep transitions remain target-only. Message-reaction firing is exposed
as visible consumption.
-/
inductive DetailedMultiStorePayloadStep
    (messageReactions :
      List MultiStorePayloadReaction) :
    DetailedMultiStorePayloadState
        messageReactions →
      DetailedMultiStorePayloadLabel →
        DetailedMultiStorePayloadState
            messageReactions →
          Prop where

  | statement
      {before after :
        MultiStorePayloadState}
      (statementStep :
        MultiStorePayloadStep
          before
          after) :
      DetailedMultiStorePayloadStep
        messageReactions
        (.stable before)
        .tau
        (.stable after)

  | timeAdvance
      {before after :
        MultiStorePayloadState}
      {selectedAction :
        PendingAction}
      {selectedReaction :
        MultiStorePayloadReaction}
      (dispatch :
        MultiStorePayloadDispatchStep
          messageReactions
          before
          selectedAction
          selectedReaction
          after)
      (future :
        before.currentTag.time <
          after.currentTag.time) :
      DetailedMultiStorePayloadStep
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
          dispatch)

  | microstepAfterTime
      {before after :
        MultiStorePayloadState}
      {selectedAction :
        PendingAction}
      {selectedReaction :
        MultiStorePayloadReaction}
      (dispatch :
        MultiStorePayloadDispatchStep
          messageReactions
          before
          selectedAction
          selectedReaction
          after)
      (positiveMicrostep :
        0 <
          after.currentTag.microstep) :
      DetailedMultiStorePayloadStep
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
          dispatch)

  | consumeAfterTimeZero
      {before after :
        MultiStorePayloadState}
      {selectedAction :
        PendingAction}
      {selectedReaction :
        MultiStorePayloadReaction}
      (dispatch :
        MultiStorePayloadDispatchStep
          messageReactions
          before
          selectedAction
          selectedReaction
          after)
      (zeroMicrostep :
        after.currentTag.microstep =
          0) :
      DetailedMultiStorePayloadStep
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
        (.stable after)

  | microstepSameTime
      {before after :
        MultiStorePayloadState}
      {selectedAction :
        PendingAction}
      {selectedReaction :
        MultiStorePayloadReaction}
      (dispatch :
        MultiStorePayloadDispatchStep
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
      DetailedMultiStorePayloadStep
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
          dispatch)

  | consumeReady
      {before after :
        MultiStorePayloadState}
      {selectedAction :
        PendingAction}
      {selectedReaction :
        MultiStorePayloadReaction}
      (dispatch :
        MultiStorePayloadDispatchStep
          messageReactions
          before
          selectedAction
          selectedReaction
          after) :
      DetailedMultiStorePayloadStep
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
        (.stable after)

  | consumeNow
      {before after :
        MultiStorePayloadState}
      {selectedAction :
        PendingAction}
      {selectedReaction :
        MultiStorePayloadReaction}
      (dispatch :
        MultiStorePayloadDispatchStep
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
      DetailedMultiStorePayloadStep
        messageReactions
        (.stable before)
        (.consume
          selectedAction
          selectedReaction)
        (.stable after)

end LF
end Relico
