import Relico.DTR.DispatchSemantics
import Relico.LF.DispatchSemantics
import Relico.Tests.Translation

set_option autoImplicit false

namespace Relico
namespace Tests

def dtrDispatchMessage :
    DTR.PendingMessage where
  name := tickMessageName
  arrivalTime := 5

def dtrDispatchSource :
    DTR.State where
  currentTime := 2
  stateValue := 11
  pendingMessages := [
    dtrDispatchMessage
  ]
  activeBody := []

def dtrDispatchTarget :
    DTR.State where
  currentTime := 5
  stateValue := 11
  pendingMessages := []
  activeBody :=
    validMessageServer.body

theorem dtrMessageDispatch :
    DTR.DispatchStep
      validModel
      dtrDispatchSource
      dtrDispatchMessage
      dtrDispatchTarget := by

  simpa [
    dtrDispatchSource,
    dtrDispatchTarget,
    dtrDispatchMessage,
    validModel,
    validReactiveClass
  ] using
    (DTR.DispatchStep.fire
      (model := validModel)
      (currentTime := 2)
      (stateValue := 11)
      (pendingMessages := [
        dtrDispatchMessage
      ])
      (remainingMessages := [])
      (selectedMessage :=
        dtrDispatchMessage)
      (hRemoved :=
        Occurrence.RemovesOne.head [])
      (hEarliest := by
        intro candidate hCandidate

        simp only [
          List.mem_singleton
        ] at hCandidate

        subst candidate
        exact Nat.le_refl 5)
      (hNotPast := by decide)
      (hTarget := by
        simp [
          dtrDispatchMessage,
          validModel,
          validReactiveClass,
          validMessageServer
        ]))

def lfDispatchTag :
    LF.Tag where
  time := 5
  microstep := 0

def lfCurrentDispatchTag :
    LF.Tag where
  time := 2
  microstep := 0

def lfDispatchAction :
    LF.PendingAction where
  name := expectedActionName
  tag := lfDispatchTag

def lfDispatchSource :
    LF.State where
  currentTag := lfCurrentDispatchTag
  stateValue := 11
  pendingActions := [
    lfDispatchAction
  ]
  activeBody := []

def lfDispatchTarget :
    LF.State where
  currentTag := lfDispatchTag
  stateValue := 11
  pendingActions := []
  activeBody :=
    expectedMessageReaction.body

theorem lfActionDispatch :
    LF.DispatchStep
      expectedProgram
      lfDispatchSource
      lfDispatchAction
      lfDispatchTarget := by

  simpa [
    lfDispatchSource,
    lfDispatchTarget,
    lfDispatchAction,
    lfDispatchTag,
    lfCurrentDispatchTag,
    expectedProgram,
    expectedReactor
  ] using
    (LF.DispatchStep.fire
      (program := expectedProgram)
      (currentTag :=
        lfCurrentDispatchTag)
      (stateValue := 11)
      (pendingActions := [
        lfDispatchAction
      ])
      (remainingActions := [])
      (selectedAction :=
        lfDispatchAction)
      (hRemoved :=
        Occurrence.RemovesOne.head [])
      (hEarliest := by
        intro candidate hCandidate

        simp only [
          List.mem_singleton
        ] at hCandidate

        subst candidate

        exact
          LF.Tag.precedesOrEqual_refl
            lfDispatchAction.tag)
      (hNotPast := by
        exact Or.inl (by decide))
      (hTarget := by
        simp [
          lfDispatchAction,
          expectedProgram,
          expectedReactor
        ]))

end Tests
end Relico
