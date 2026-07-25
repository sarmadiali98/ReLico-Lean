import Relico.DTR.MultiStorePriorityScheduling
import Relico.LF.MultiStoreReactionScheduling
import Relico.Translation.MultiStoreBasic
import Std.Tactic

set_option autoImplicit false

namespace Relico
namespace Tests

def dispatchPriorityLowName :
    MsgName :=
  ⟨"dispatchPriorityLow"⟩

def dispatchPriorityHighName :
    MsgName :=
  ⟨"dispatchPriorityHigh"⟩

def dispatchPriorityLowServer :
    DTR.MessageServer where

  name :=
    dispatchPriorityLowName

  body :=
    []

  priority :=
    some 4

def dispatchPriorityHighServer :
    DTR.MessageServer where

  name :=
    dispatchPriorityHighName

  body :=
    []

  priority :=
    some 1

/--
Source declaration order deliberately places the lower-priority server
first.
-/
def dispatchPriorityServers :
    List DTR.MessageServer := [
  dispatchPriorityLowServer,
  dispatchPriorityHighServer
]

def dispatchLowMessage :
    DTR.PendingMessage where

  name :=
    dispatchPriorityLowName

  arrivalTime :=
    5

def dispatchHighMessage :
    DTR.PendingMessage where

  name :=
    dispatchPriorityHighName

  arrivalTime :=
    5

def dispatchSourcePriorityQueue :
    DTR.MessageBag := [
  dispatchLowMessage,
  dispatchHighMessage
]

/--
Stable normalization places the higher-priority server first even
though the source declaration list places it second.
-/
theorem dispatch_source_high_precedes_low :
    DTR.PriorityServerNamePrecedesOrEqual
      dispatchPriorityHighName
      dispatchPriorityLowName
      dispatchPriorityServers := by
  native_decide

theorem dispatch_source_high_precedes_itself :
    DTR.PriorityServerNamePrecedesOrEqual
      dispatchPriorityHighName
      dispatchPriorityHighName
      dispatchPriorityServers := by
  native_decide

theorem dispatch_source_low_does_not_precede_high :
    ¬ DTR.PriorityServerNamePrecedesOrEqual
        dispatchPriorityLowName
        dispatchPriorityHighName
        dispatchPriorityServers := by
  native_decide

/--
Among equal-time source messages, the higher-priority server is
eligible even when its message occurrence appears later in the queue.
-/
theorem dispatch_source_high_is_priority_eligible :
    DTR.IsPriorityEligible
      dispatchPriorityServers
      dispatchHighMessage
      dispatchSourcePriorityQueue := by

  refine
    ⟨?_,
     ?_⟩

  · intro candidate hCandidate

    simp [
      dispatchSourcePriorityQueue
    ] at hCandidate

    rcases hCandidate with
      hLow | hHigh

    · subst candidate

      simp [
        dispatchLowMessage,
        dispatchHighMessage
      ]

    · subst candidate

      simp [
        dispatchHighMessage
      ]

  · intro candidate hCandidate hSameTime

    simp [
      dispatchSourcePriorityQueue
    ] at hCandidate

    rcases hCandidate with
      hLow | hHigh

    · subst candidate

      exact
        dispatch_source_high_precedes_low

    · subst candidate

      exact
        dispatch_source_high_precedes_itself

/--
The lower-priority equal-time message is not eligible while the
higher-priority message remains pending.
-/
theorem dispatch_source_low_is_not_priority_eligible :
    ¬ DTR.IsPriorityEligible
        dispatchPriorityServers
        dispatchLowMessage
        dispatchSourcePriorityQueue := by

  intro hEligible

  have hOrder :
      DTR.PriorityServerNamePrecedesOrEqual
        dispatchPriorityLowName
        dispatchPriorityHighName
        dispatchPriorityServers :=

    hEligible.precedes_same_time
      (candidate :=
        dispatchHighMessage)
      (by
        simp [
          dispatchSourcePriorityQueue
        ])
      (by
        rfl)

  exact
    dispatch_source_low_does_not_precede_high
      hOrder

def dispatchPriorityTag :
    LF.Tag where

  time :=
    5

  microstep :=
    0

def dispatchLowAction :
    LF.PendingAction where

  name :=
    Translation.actionNameFor
      dispatchPriorityLowName

  tag :=
    dispatchPriorityTag

def dispatchHighAction :
    LF.PendingAction where

  name :=
    Translation.actionNameFor
      dispatchPriorityHighName

  tag :=
    dispatchPriorityTag

def dispatchTargetPriorityQueue :
    LF.ActionQueue := [
  dispatchLowAction,
  dispatchHighAction
]

def dispatchPriorityReactions :
    List LF.Reaction :=
  Translation.compileMessageReactions
    dispatchPriorityServers

/--
The generated reaction list carries the same high-before-low order as
the source priority normalization.
-/
theorem dispatch_target_high_reaction_precedes_low :
    LF.ReactionActionPrecedesOrEqual
      (Translation.actionNameFor
        dispatchPriorityHighName)
      (Translation.actionNameFor
        dispatchPriorityLowName)
      dispatchPriorityReactions := by
  native_decide

theorem dispatch_target_high_reaction_precedes_itself :
    LF.ReactionActionPrecedesOrEqual
      (Translation.actionNameFor
        dispatchPriorityHighName)
      (Translation.actionNameFor
        dispatchPriorityHighName)
      dispatchPriorityReactions := by
  native_decide

theorem dispatch_target_low_reaction_does_not_precede_high :
    ¬ LF.ReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          dispatchPriorityLowName)
        (Translation.actionNameFor
          dispatchPriorityHighName)
        dispatchPriorityReactions := by
  native_decide

/--
At one complete LF tag, reaction declaration order makes the generated
high-priority action eligible.
-/
theorem dispatch_target_high_is_reaction_priority_eligible :
    LF.IsReactionPriorityEligible
      dispatchPriorityReactions
      dispatchHighAction
      dispatchTargetPriorityQueue := by

  refine
    ⟨?_,
     ?_⟩

  · intro candidate hCandidate

    simp [
      dispatchTargetPriorityQueue
    ] at hCandidate

    rcases hCandidate with
      hLow | hHigh

    · subst candidate

      simpa [
        dispatchLowAction,
        dispatchHighAction
      ] using
        LF.Tag.precedesOrEqual_refl
          dispatchPriorityTag

    · subst candidate

      simpa [
        dispatchHighAction
      ] using
        LF.Tag.precedesOrEqual_refl
          dispatchPriorityTag

  · intro candidate hCandidate hSameTag

    simp [
      dispatchTargetPriorityQueue
    ] at hCandidate

    rcases hCandidate with
      hLow | hHigh

    · subst candidate

      exact
        dispatch_target_high_reaction_precedes_low

    · subst candidate

      exact
        dispatch_target_high_reaction_precedes_itself

/--
The low-priority action cannot dispatch first while the high-priority
action is pending at the same complete LF tag.
-/
theorem dispatch_target_low_is_not_reaction_priority_eligible :
    ¬ LF.IsReactionPriorityEligible
        dispatchPriorityReactions
        dispatchLowAction
        dispatchTargetPriorityQueue := by

  intro hEligible

  have hOrder :
      LF.ReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          dispatchPriorityLowName)
        (Translation.actionNameFor
          dispatchPriorityHighName)
        dispatchPriorityReactions :=

    hEligible.precedes_same_tag
      (candidate :=
        dispatchHighAction)
      (by
        simp [
          dispatchTargetPriorityQueue
        ])
      (by
        rfl)

  exact
    dispatch_target_low_reaction_does_not_precede_high
      hOrder

end Tests
end Relico
