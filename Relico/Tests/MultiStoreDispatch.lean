import Relico.Correctness.MultiStoreDispatch
import Relico.Tests.MultiStoreModelTranslation

set_option autoImplicit false

namespace Relico
namespace Tests

def multiDispatchStore :
    StateStore := [
  (twoStateX, 1),
  (twoStateY, 2)
]

def multiDispatchMessage :
    DTR.PendingMessage where

  name :=
    resetMessageName

  arrivalTime :=
    5

def multiDispatchTag :
    LF.Tag where

  time :=
    5

  microstep :=
    0

def multiDispatchCurrentTag :
    LF.Tag where

  time :=
    2

  microstep :=
    0

def multiDispatchAction :
    LF.PendingAction where

  name :=
    Translation.actionNameFor
      resetMessageName

  tag :=
    multiDispatchTag

def multiDtrDispatchBefore :
    DTR.StoreState where

  currentTime :=
    2

  stateStore :=
    multiDispatchStore

  pendingMessages := [
    multiDispatchMessage
  ]

  activeBody :=
    []

def multiDtrDispatchAfter :
    DTR.StoreState where

  currentTime :=
    5

  stateStore :=
    multiDispatchStore

  pendingMessages :=
    []

  activeBody :=
    resetMessageServer.body

def multiLfDispatchBefore :
    LF.StoreState where

  currentTag :=
    multiDispatchCurrentTag

  stateStore :=
    multiDispatchStore

  pendingActions := [
    multiDispatchAction
  ]

  activeBody :=
    []

def multiLfDispatchAfter :
    LF.StoreState where

  currentTag :=
    multiDispatchTag

  stateStore :=
    multiDispatchStore

  pendingActions :=
    []

  activeBody :=
    (Translation.compileMessageReaction
      resetMessageServer).body

theorem multi_dispatch_message_is_priority_eligible :
    DTR.IsPriorityEligible
      twoMessageServers
      multiDispatchMessage
      [multiDispatchMessage] := by

  refine
    ⟨?_,
     ?_⟩

  · intro candidate hCandidate

    simp only [
      List.mem_singleton
    ] at hCandidate

    subst candidate
    native_decide

  · intro candidate hCandidate hSameTime

    simp only [
      List.mem_singleton
    ] at hCandidate

    subst candidate
    native_decide

theorem multi_dispatch_action_is_reaction_priority_eligible :
    LF.IsReactionPriorityEligible
      (Translation.compileMessageReactions
        twoMessageServers)
      multiDispatchAction
      [multiDispatchAction] := by

  refine
    ⟨?_,
     ?_⟩

  · intro candidate hCandidate

    simp only [
      List.mem_singleton
    ] at hCandidate

    subst candidate

    exact
      LF.Tag.precedesOrEqual_refl
        multiDispatchAction.tag

  · intro candidate hCandidate hSameTag

    simp only [
      List.mem_singleton
    ] at hCandidate

    subst candidate
    native_decide

theorem multi_dtr_dispatch_selects_reset :
    DTR.MultiStoreDispatchStep
      twoMessageServers
      multiDtrDispatchBefore
      multiDispatchMessage
      resetMessageServer
      multiDtrDispatchAfter := by

  exact
    DTR.MultiStoreDispatchStep.fire
      (messageServers :=
        twoMessageServers)
      (currentTime :=
        2)
      (stateStore :=
        multiDispatchStore)
      (pendingMessages := [
        multiDispatchMessage
      ])
      (remainingMessages :=
        [])
      (selectedMessage :=
        multiDispatchMessage)
      (selectedServer :=
        resetMessageServer)
      (by
        simp [
          twoMessageServers
        ])
      (Occurrence.RemovesOne.head [])
      multi_dispatch_message_is_priority_eligible
      (by decide)
      rfl

theorem multi_lf_dispatch_selects_reset_reaction :
    LF.MultiStoreDispatchStep
      (Translation.compileMessageReactions
        twoMessageServers)
      multiLfDispatchBefore
      multiDispatchAction
      (Translation.compileMessageReaction
        resetMessageServer)
      multiLfDispatchAfter := by

  exact
    LF.MultiStoreDispatchStep.fire
      (messageReactions :=
        Translation.compileMessageReactions
          twoMessageServers)
      (currentTag :=
        multiDispatchCurrentTag)
      (stateStore :=
        multiDispatchStore)
      (pendingActions := [
        multiDispatchAction
      ])
      (remainingActions :=
        [])
      (selectedAction :=
        multiDispatchAction)
      (selectedReaction :=
        Translation.compileMessageReaction
          resetMessageServer)
      (by
        exact
          List.mem_map_of_mem
            (by
              simp [
                twoMessageServers
              ]))
      (Occurrence.RemovesOne.head [])
      multi_dispatch_action_is_reaction_priority_eligible
      (by
        exact Or.inl (by decide))
      (by
        rfl)

theorem multiDispatchStatesCorrespond :
    Correctness.StoreStateCorresponds
      multiDtrDispatchBefore
      multiLfDispatchBefore := by

  exact {
    currentTime :=
      rfl

    stateStore :=
      rfl

    pendingEvents :=
      Correctness.QueueCorresponds.cons
        {
          actionName :=
            rfl

          logicalTime :=
            rfl
        }
        Correctness.QueueCorresponds.nil

    activeBody :=
      rfl
  }

theorem multiDispatchForwardCompatible :
    Correctness.StoreForwardDispatchCompatible
      multiDispatchMessage
      []
      multiLfDispatchBefore := by

  refine
    ⟨multiDispatchAction,
     [],
     Occurrence.RemovesOne.head [],
     ?_,
     Correctness.QueueCorresponds.nil,
     ?_,
     ?_⟩

  · exact {
      actionName :=
        rfl

      logicalTime :=
        rfl
    }

  · intro candidate hCandidate

    simp only [
      multiLfDispatchBefore,
      List.mem_singleton
    ] at hCandidate

    subst candidate

    exact
      LF.Tag.precedesOrEqual_refl
        multiDispatchTag

  · exact Or.inl (by decide)

theorem multi_dispatch_forward_correspondence :
    ∃ selectedAction targetReaction targetStateAfter,
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            twoMessageServers)
          multiLfDispatchBefore
          selectedAction
          targetReaction
          targetStateAfter ∧
      targetReaction =
        Translation.compileMessageReaction
          resetMessageServer ∧
      Correctness.PendingCorresponds
        multiDispatchMessage
        selectedAction ∧
      Correctness.StoreStateCorresponds
        multiDtrDispatchAfter
        targetStateAfter := by

  exact
    Correctness.multiStore_dispatch_forward_of_compatible
      multi_dtr_dispatch_selects_reset
      multiDispatchStatesCorrespond
      multiDispatchForwardCompatible

theorem multi_lf_dispatch_before_pending_microsteps_zero :
    LF.StoreState.PendingMicrostepsZero
      multiLfDispatchBefore := by

  intro action hAction

  simp [
    multiLfDispatchBefore
  ] at hAction

  subst action
  rfl

theorem multi_dispatch_backward_correspondence :
    ∃ selectedMessage sourceServer sourceStateAfter,
      DTR.MultiStoreDispatchStep
          twoMessageServers
          multiDtrDispatchBefore
          selectedMessage
          sourceServer
          sourceStateAfter ∧
      Translation.compileMessageReaction
          resetMessageServer =
        Translation.compileMessageReaction
          sourceServer ∧
      Correctness.PendingCorresponds
        selectedMessage
        multiDispatchAction ∧
      Correctness.StoreStateCorresponds
        sourceStateAfter
        multiLfDispatchAfter := by

  exact
    Correctness.multiStore_dispatch_backward
      multi_lf_dispatch_selects_reset_reaction
      multiDispatchStatesCorrespond
      multi_lf_dispatch_before_pending_microsteps_zero

end Tests
end Relico
