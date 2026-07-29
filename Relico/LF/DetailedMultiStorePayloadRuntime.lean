import Relico.LF.MultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace LF

/--
Proof-indexed phases for generated payload-aware LF dispatch.

Future dispatch may pass through `afterTime` and `dispatchReady`. Same-time
dispatch may enter `dispatchReady` through a target-only microstep.
-/
inductive DetailedMultiStorePayloadState
    (messageReactions :
      List MultiStorePayloadReaction) where

  | stable
      (state :
        MultiStorePayloadState) :
      DetailedMultiStorePayloadState
        messageReactions

  | afterTime
      (before :
        MultiStorePayloadState)
      (selectedAction :
        PendingAction)
      (selectedReaction :
        MultiStorePayloadReaction)
      (after :
        MultiStorePayloadState)
      (dispatch :
        MultiStorePayloadDispatchStep
          messageReactions
          before
          selectedAction
          selectedReaction
          after) :
      DetailedMultiStorePayloadState
        messageReactions

  | dispatchReady
      (before :
        MultiStorePayloadState)
      (selectedAction :
        PendingAction)
      (selectedReaction :
        MultiStorePayloadReaction)
      (after :
        MultiStorePayloadState)
      (dispatch :
        MultiStorePayloadDispatchStep
          messageReactions
          before
          selectedAction
          selectedReaction
          after) :
      DetailedMultiStorePayloadState
        messageReactions

/--
Detailed labels for generated payload-aware LF dispatch.

Pure microstep progression is explicit on the target and will correspond to
source `tau`.
-/
inductive DetailedMultiStorePayloadLabel where

  | tau :
      DetailedMultiStorePayloadLabel

  | timeAdvance
      (before after :
        LogicalTime) :
      DetailedMultiStorePayloadLabel

  | microstepAdvance
      (before after :
        Tag) :
      DetailedMultiStorePayloadLabel

  | consume
      (selectedAction :
        PendingAction)
      (selectedReaction :
        MultiStorePayloadReaction) :
      DetailedMultiStorePayloadLabel

end LF
end Relico
