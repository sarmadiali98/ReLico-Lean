import Relico.DTR.Scheduling
import Relico.LF.Scheduling

set_option autoImplicit false

namespace Relico
namespace Tests

def schedulerMessageA :
    DTR.PendingMessage where
  name := ⟨"a"⟩
  arrivalTime := 5

def schedulerMessageB :
    DTR.PendingMessage where
  name := ⟨"b"⟩
  arrivalTime := 5

/--
The second occurrence can be selected even though the first occurrence
has the same logical time.
-/
def dtrEqualTimeSelection :
    DTR.DispatchSelection
      [schedulerMessageA, schedulerMessageB]
      [schedulerMessageA] where

  selected :=
    schedulerMessageB

  removed :=
    Occurrence.RemovesOne.tail
      schedulerMessageA
      (Occurrence.RemovesOne.head [])

  earliest := by
    intro candidate hCandidate

    simp only [
      List.mem_cons,
      List.not_mem_nil,
      or_false
    ] at hCandidate

    rcases hCandidate with
      hFirst | hSecond

    · rw [hFirst]

      simp [
        schedulerMessageA,
        schedulerMessageB
      ]

    · rw [hSecond]

      simp [schedulerMessageB]

theorem dtrSelectionKeepsOccurrenceMembership :
    dtrEqualTimeSelection.selected ∈
      [schedulerMessageA, schedulerMessageB] := by
  exact
    DTR.DispatchSelection.selected_mem
      dtrEqualTimeSelection

def schedulerEarlyAction :
    LF.PendingAction where
  name := ⟨"tick_action"⟩
  tag := {
    time := 5
    microstep := 0
  }

def schedulerLaterAction :
    LF.PendingAction where
  name := ⟨"tick_action"⟩
  tag := {
    time := 5
    microstep := 1
  }

/--
At equal logical time, the lower microstep is the earliest LF action.
-/
def lfMicrostepSelection :
    LF.DispatchSelection
      [schedulerEarlyAction, schedulerLaterAction]
      [schedulerLaterAction] where

  selected :=
    schedulerEarlyAction

  removed :=
    Occurrence.RemovesOne.head
      [schedulerLaterAction]

  earliest := by
    intro candidate hCandidate

    simp only [
      List.mem_cons,
      List.not_mem_nil,
      or_false
    ] at hCandidate

    rcases hCandidate with
      hEarly | hLater

    · rw [hEarly]

      exact
        LF.Tag.precedesOrEqual_refl
          schedulerEarlyAction.tag

    · rw [hLater]

      apply
        LF.Tag.precedesOrEqual_same_time

      · rfl

      · exact Nat.zero_le 1

theorem lfSelectionKeepsOccurrenceMembership :
    lfMicrostepSelection.selected ∈
      [schedulerEarlyAction, schedulerLaterAction] := by
  exact
    LF.DispatchSelection.selected_mem
      lfMicrostepSelection

end Tests
end Relico
