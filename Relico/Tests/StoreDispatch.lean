import Relico.Correctness.StoreDispatch
import Relico.Tests.StoreSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

def storeDispatchMessage :
    DTR.PendingMessage where
  name :=
    storeRuntimeMessageName

  arrivalTime :=
    5

def storeDispatchTag :
    LF.Tag where
  time :=
    5

  microstep :=
    0

def storeDispatchCurrentTag :
    LF.Tag where
  time :=
    2

  microstep :=
    0

def storeDispatchAction :
    LF.PendingAction where
  name :=
    Translation.actionNameFor
      storeRuntimeMessageName

  tag :=
    storeDispatchTag

def storeDispatchBody :
    DTR.Body := [
  DTR.Stmt.assign
    secondStateVariableName
    (.stateVar
      stateVariableName)
]

def dtrStoreDispatchSource :
    DTR.StoreState where
  currentTime :=
    2

  stateStore :=
    twoVariableStore

  pendingMessages := [
    storeDispatchMessage
  ]

  activeBody :=
    []

def dtrStoreDispatchTarget :
    DTR.StoreState where
  currentTime :=
    5

  stateStore :=
    twoVariableStore

  pendingMessages :=
    []

  activeBody :=
    storeDispatchBody

def lfStoreDispatchSource :
    LF.StoreState where
  currentTag :=
    storeDispatchCurrentTag

  stateStore :=
    twoVariableStore

  pendingActions := [
    storeDispatchAction
  ]

  activeBody :=
    []

def lfStoreDispatchTarget :
    LF.StoreState where
  currentTag :=
    storeDispatchTag

  stateStore :=
    twoVariableStore

  pendingActions :=
    []

  activeBody :=
    Translation.compileBody
      storeDispatchBody

theorem dtr_store_dispatch :
    DTR.StoreDispatchStep
      storeRuntimeMessageName
      storeDispatchBody
      dtrStoreDispatchSource
      storeDispatchMessage
      dtrStoreDispatchTarget := by

  exact
    DTR.StoreDispatchStep.fire
      (messageServer :=
        storeRuntimeMessageName)
      (messageBody :=
        storeDispatchBody)
      (currentTime :=
        2)
      (stateStore :=
        twoVariableStore)
      (pendingMessages := [
        storeDispatchMessage
      ])
      (remainingMessages :=
        [])
      (selectedMessage :=
        storeDispatchMessage)
      (Occurrence.RemovesOne.head [])
      (by
        intro candidate hCandidate

        simp only [
          List.mem_singleton
        ] at hCandidate

        subst candidate

        exact Nat.le_refl 5)
      (by decide)
      rfl

theorem lf_store_dispatch :
    LF.StoreDispatchStep
      (Translation.actionNameFor
        storeRuntimeMessageName)
      (Translation.compileBody
        storeDispatchBody)
      lfStoreDispatchSource
      storeDispatchAction
      lfStoreDispatchTarget := by

  exact
    LF.StoreDispatchStep.fire
      (logicalAction :=
        Translation.actionNameFor
          storeRuntimeMessageName)
      (messageReactionBody :=
        Translation.compileBody
          storeDispatchBody)
      (currentTag :=
        storeDispatchCurrentTag)
      (stateStore :=
        twoVariableStore)
      (pendingActions := [
        storeDispatchAction
      ])
      (remainingActions :=
        [])
      (selectedAction :=
        storeDispatchAction)
      (Occurrence.RemovesOne.head [])
      (by
        intro candidate hCandidate

        simp only [
          List.mem_singleton
        ] at hCandidate

        subst candidate

        exact
          LF.Tag.precedesOrEqual_refl
            storeDispatchAction.tag)
      (by
        exact Or.inl (by decide))
      rfl

theorem storeDispatchSourceStatesCorrespond :
    Correctness.StoreStateCorresponds
      dtrStoreDispatchSource
      lfStoreDispatchSource := by

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

theorem storeDispatchForwardCompatible :
    Correctness.StoreForwardDispatchCompatible
      storeDispatchMessage
      []
      lfStoreDispatchSource := by

  refine
    ⟨storeDispatchAction,
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
      lfStoreDispatchSource,
      List.mem_singleton
    ] at hCandidate

    subst candidate

    exact
      LF.Tag.precedesOrEqual_refl
        storeDispatchAction.tag

  · exact Or.inl (by decide)

theorem dtr_store_dispatch_has_lf_dispatch :
    ∃ selectedAction targetStateAfter,
      LF.StoreDispatchStep
          (Translation.actionNameFor
            storeRuntimeMessageName)
          (Translation.compileBody
            storeDispatchBody)
          lfStoreDispatchSource
          selectedAction
          targetStateAfter ∧
      Correctness.PendingCorresponds
        storeDispatchMessage
        selectedAction ∧
      Correctness.StoreStateCorresponds
        dtrStoreDispatchTarget
        targetStateAfter := by

  exact
    Correctness.store_dispatch_forward_of_compatible
      dtr_store_dispatch
      storeDispatchSourceStatesCorrespond
      storeDispatchForwardCompatible

theorem storeDispatchPendingTargets :
    ∀ pendingMessage,
      pendingMessage ∈
        dtrStoreDispatchSource.pendingMessages →
      pendingMessage.name =
        storeRuntimeMessageName := by

  intro pendingMessage hMember

  simp only [
    dtrStoreDispatchSource,
    List.mem_singleton
  ] at hMember

  subst pendingMessage

  rfl

theorem lf_store_dispatch_has_dtr_dispatch :
    ∃ selectedMessage sourceStateAfter,
      DTR.StoreDispatchStep
          storeRuntimeMessageName
          storeDispatchBody
          dtrStoreDispatchSource
          selectedMessage
          sourceStateAfter ∧
      Correctness.PendingCorresponds
        selectedMessage
        storeDispatchAction ∧
      Correctness.StoreStateCorresponds
        sourceStateAfter
        lfStoreDispatchTarget := by

  exact
    Correctness.store_dispatch_backward
      lf_store_dispatch
      storeDispatchSourceStatesCorrespond
      storeDispatchPendingTargets

example :
    dtrStoreDispatchTarget.stateStore =
      twoVariableStore := by
  rfl

example :
    lfStoreDispatchTarget.stateStore =
      twoVariableStore := by
  rfl

end Tests
end Relico
