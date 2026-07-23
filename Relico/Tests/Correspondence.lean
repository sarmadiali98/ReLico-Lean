import Relico.Correctness.Correspondence
import Relico.Tests.Translation

set_option autoImplicit false

namespace Relico
namespace Tests

def correspondenceSourceState : DTR.State where
  currentTime := 2
  stateValue := 5
  pendingMessages := [
    {
      name := tickMessageName
      arrivalTime := 5
    }
  ]
  activeBody := [
    .selfSend tickMessageName ⟨3⟩
  ]

def correspondenceTargetState : LF.State where
  currentTag := {
    time := 2
    microstep := 4
  }
  stateValue := 5
  pendingActions := [
    {
      name :=
        Translation.actionNameFor tickMessageName
      tag := {
        time := 5
        microstep := 0
      }
    }
  ]
  activeBody :=
    Translation.compileBody
      correspondenceSourceState.activeBody

theorem exampleStateCorresponds :
    Correctness.StateCorresponds
      correspondenceSourceState
      correspondenceTargetState := by
  refine {
    currentTime := rfl
    stateValue := rfl
    pendingEvents := ?_
    activeBody := rfl
  }

  exact
    Correctness.QueueCorresponds.cons
      {
        actionName := rfl
        logicalTime := rfl
      }
      Correctness.QueueCorresponds.nil

def zeroDelaySourceMessage :
    DTR.PendingMessage where
  name := tickMessageName
  arrivalTime := 2

def zeroDelayTargetAction :
    LF.PendingAction where
  name :=
    Translation.actionNameFor tickMessageName
  tag :=
    LF.Tag.schedule
      {
        time := 2
        microstep := 4
      }
      ⟨0⟩

theorem zeroDelayOccurrenceCorresponds :
    Correctness.PendingCorresponds
      zeroDelaySourceMessage
      zeroDelayTargetAction := by
  exact
    Correctness.pendingCorresponds_scheduled
      2
      {
        time := 2
        microstep := 4
      }
      tickMessageName
      ⟨0⟩
      rfl

end Tests
end Relico
