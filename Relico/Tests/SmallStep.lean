import Relico.DTR.Semantics
import Relico.LF.Semantics
import Relico.Tests.Translation

set_option autoImplicit false

namespace Relico
namespace Tests

def dtrAssignmentSource : DTR.State where
  currentTime := 2
  stateValue := 5
  pendingMessages := []
  activeBody := [
    .assign
      stateVariableName
      (.intLiteral 7)
  ]

def dtrAssignmentTarget : DTR.State where
  currentTime := 2
  stateValue := 7
  pendingMessages := []
  activeBody := []

example :
    DTR.Step
      validModel
      dtrAssignmentSource
      .internal
      dtrAssignmentTarget := by
  simpa [
    dtrAssignmentSource,
    dtrAssignmentTarget
  ] using
    (DTR.Step.assign
      (model := validModel)
      (currentTime := 2)
      (stateValue := 5)
      (pendingMessages := [])
      (target := stateVariableName)
      (expression := .intLiteral 7)
      (remaining := [])
      (hTarget := rfl))

def dtrSendSource : DTR.State where
  currentTime := 2
  stateValue := 5
  pendingMessages := []
  activeBody := [
    .selfSend
      tickMessageName
      ⟨3⟩
  ]

def dtrSendTarget : DTR.State where
  currentTime := 2
  stateValue := 5
  pendingMessages := [
    {
      name := tickMessageName
      arrivalTime :=
        LogicalTime.after 2 ⟨3⟩
    }
  ]
  activeBody := []

example :
    DTR.Step
      validModel
      dtrSendSource
      (.send
        tickMessageName
        (LogicalTime.after 2 ⟨3⟩))
      dtrSendTarget := by
  simpa [
    dtrSendSource,
    dtrSendTarget
  ] using
    (DTR.Step.selfSend
      (model := validModel)
      (currentTime := 2)
      (stateValue := 5)
      (pendingMessages := [])
      (targetMessage := tickMessageName)
      (delay := ⟨3⟩)
      (remaining := [])
      (hTarget := rfl))

def initialLFTag : LF.Tag where
  time := 2
  microstep := 0

def lfAssignmentSource : LF.State where
  currentTag := initialLFTag
  stateValue := 5
  pendingActions := []
  activeBody := [
    .assign
      stateVariableName
      (.intLiteral 7)
  ]

def lfAssignmentTarget : LF.State where
  currentTag := initialLFTag
  stateValue := 7
  pendingActions := []
  activeBody := []

example :
    LF.Step
      expectedProgram
      lfAssignmentSource
      .internal
      lfAssignmentTarget := by
  simpa [
    lfAssignmentSource,
    lfAssignmentTarget
  ] using
    (LF.Step.assign
      (program := expectedProgram)
      (currentTag := initialLFTag)
      (stateValue := 5)
      (pendingActions := [])
      (target := stateVariableName)
      (expression := .intLiteral 7)
      (remaining := [])
      (hTarget := rfl))

def lfScheduleSource : LF.State where
  currentTag := initialLFTag
  stateValue := 5
  pendingActions := []
  activeBody := [
    .schedule
      expectedActionName
      ⟨3⟩
  ]

def lfScheduleTarget : LF.State where
  currentTag := initialLFTag
  stateValue := 5
  pendingActions := [
    {
      name := expectedActionName
      tag :=
        LF.Tag.schedule
          initialLFTag
          ⟨3⟩
    }
  ]
  activeBody := []

example :
    LF.Step
      expectedProgram
      lfScheduleSource
      (.schedule
        expectedActionName
        (LF.Tag.schedule
          initialLFTag
          ⟨3⟩))
      lfScheduleTarget := by
  simpa [
    lfScheduleSource,
    lfScheduleTarget
  ] using
    (LF.Step.schedule
      (program := expectedProgram)
      (currentTag := initialLFTag)
      (stateValue := 5)
      (pendingActions := [])
      (targetAction := expectedActionName)
      (delay := ⟨3⟩)
      (remaining := [])
      (hTarget := rfl))

end Tests
end Relico
