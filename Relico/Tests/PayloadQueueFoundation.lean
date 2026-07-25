import Relico.Correctness.PayloadCorrespondence
import Relico.Tests.MultiStoreModelTranslation

set_option autoImplicit false

namespace Relico
namespace Tests

def payloadQueueInitialTag :
    LF.Tag where

  time :=
    0

  microstep :=
    0

def payloadQueueFirstMessage :
    DTR.PendingMessage :=
  DTR.PendingMessage.scheduleWithPayload
    0
    twoStateMessageName
    [
      7,
      11
    ]
    { value := 1 }

def payloadQueueFirstAction :
    LF.PendingAction :=
  LF.PendingAction.scheduleWithPayload
    payloadQueueInitialTag
    (Translation.actionNameFor
      twoStateMessageName)
    [
      7,
      11
    ]
    { value := 1 }

def payloadQueueSecondMessage :
    DTR.PendingMessage :=
  DTR.PendingMessage.scheduleWithPayload
    0
    resetMessageName
    [
      13,
      17
    ]
    { value := 2 }

def payloadQueueSecondAction :
    LF.PendingAction :=
  LF.PendingAction.scheduleWithPayload
    payloadQueueInitialTag
    (Translation.actionNameFor
      resetMessageName)
    [
      13,
      17
    ]
    { value := 2 }

theorem payload_queue_first_occurrence_corresponds :
    Correctness.PayloadQueueCorresponds
      [
        payloadQueueFirstMessage
      ]
      [
        payloadQueueFirstAction
      ] := by

  apply
    Correctness.payloadQueueCorresponds_singleton

  simpa [
    payloadQueueFirstMessage,
    payloadQueueFirstAction
  ] using
    Correctness.pendingPayloadCorresponds_scheduleWithPayload
      0
      payloadQueueInitialTag
      twoStateMessageName
      [
        7,
        11
      ]
      { value := 1 }
      rfl

theorem payload_queue_append_preserves_correspondence :
    Correctness.PayloadQueueCorresponds
      [
        payloadQueueFirstMessage,
        payloadQueueSecondMessage
      ]
      [
        payloadQueueFirstAction,
        payloadQueueSecondAction
      ] := by

  simpa [
    payloadQueueSecondMessage,
    payloadQueueSecondAction
  ] using
    Correctness.payloadQueueCorresponds_append_scheduleWithPayload
      payload_queue_first_occurrence_corresponds
      0
      payloadQueueInitialTag
      resetMessageName
      [
        13,
        17
      ]
      { value := 2 }
      rfl

theorem payload_queue_preserves_first_payload :
    payloadQueueFirstAction.payload =
      payloadQueueFirstMessage.payload := by
  rfl

theorem payload_queue_preserves_second_payload :
    payloadQueueSecondAction.payload =
      payloadQueueSecondMessage.payload := by
  rfl

theorem payload_queue_preserves_order :
    List.map
        DTR.PendingMessage.payload
        [
          payloadQueueFirstMessage,
          payloadQueueSecondMessage
        ] =
      [
        [
          7,
          11
        ],
        [
          13,
          17
        ]
      ] := by
  rfl

end Tests
end Relico
