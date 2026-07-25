import Relico.Correctness.PayloadCorrespondence
import Relico.Tests.MultiStoreModelTranslation

set_option autoImplicit false

namespace Relico
namespace Tests

def payloadFoundationValues :
    Payload := [
  7,
  11
]

def payloadFoundationMessage :
    DTR.PendingMessage where

  name :=
    twoStateMessageName

  arrivalTime :=
    5

  payload :=
    payloadFoundationValues

def payloadFoundationAction :
    LF.PendingAction where

  name :=
    Translation.actionNameFor
      twoStateMessageName

  tag := {
    time :=
      5

    microstep :=
      0
  }

  payload :=
    payloadFoundationValues

theorem payload_foundation_source_values :
    payloadFoundationMessage.payload = [
      7,
      11
    ] := by
  rfl

theorem payload_foundation_target_values :
    payloadFoundationAction.payload = [
      7,
      11
    ] := by
  rfl

theorem payload_foundation_correspondence :
    Correctness.PendingPayloadCorresponds
      payloadFoundationMessage
      payloadFoundationAction := by

  refine {
    occurrence := ?_
    payload := rfl
  }

  exact {
    actionName := rfl
    logicalTime := rfl
  }

theorem legacy_pending_message_payload_is_empty :
    ({
      name :=
        twoStateMessageName

      arrivalTime :=
        5
    } : DTR.PendingMessage).payload =
      [] := by
  rfl

theorem legacy_pending_action_payload_is_empty :
    ({
      name :=
        Translation.actionNameFor
          twoStateMessageName

      tag := {
        time :=
          5

        microstep :=
          0
      }
    } : LF.PendingAction).payload =
      [] := by
  rfl

end Tests
end Relico
