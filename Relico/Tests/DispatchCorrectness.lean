import Relico.Correctness.Dispatch
import Relico.Tests.DispatchSemantics
import Relico.Tests.DTRWellFormed

set_option autoImplicit false

namespace Relico
namespace Tests

def generatedLFDispatchTarget :
    LF.State where
  currentTag := lfDispatchTag
  stateValue := 11
  pendingActions := []
  activeBody := (Translation.translateCore validModel).reactor.messageReaction.body

theorem generatedLFDispatchStep :
    LF.DispatchStep
      (Translation.translateCore validModel)
      lfDispatchSource
      lfDispatchAction
      generatedLFDispatchTarget := by

  simpa [
    lfDispatchSource,
    generatedLFDispatchTarget,
    lfDispatchAction
  ] using
    (LF.DispatchStep.fire
      (program :=
        Translation.translateCore validModel)
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
          expectedActionName,
          tickMessageName,
          Translation.actionNameFor,
          Translation.translateCore,
          Translation.compileReactor,
          validModel,
          validReactiveClass,
          validMessageServer
        ]))

theorem dispatchSourceStatesCorrespond :
    Correctness.StateCorresponds
      dtrDispatchSource
      lfDispatchSource := by

  refine {
    currentTime := ?_
    stateValue := ?_
    pendingEvents := ?_
    activeBody := ?_
  }

  · simp [
      dtrDispatchSource,
      lfDispatchSource,
      lfCurrentDispatchTag
    ]

  · simp [
      dtrDispatchSource,
      lfDispatchSource
    ]

  · apply
      Correctness.QueueCorresponds.cons

    · refine {
        actionName := ?_
        logicalTime := ?_
      }

      · simp [
          dtrDispatchMessage,
          lfDispatchAction,
          expectedActionName,
          tickMessageName,
          Translation.actionNameFor
        ]

      · simp [
          dtrDispatchMessage,
          lfDispatchAction,
          lfDispatchTag
        ]

    · exact
        Correctness.QueueCorresponds.nil

  · simp [
      dtrDispatchSource,
      lfDispatchSource,
      Translation.compileBody
    ]

theorem dtrDispatchSource_runtimeWellFormed :
    DTR.State.WellFormed
      validModel
      dtrDispatchSource := by

  refine {
    activeBodyWellFormed := ?_
    pendingMessagesWellFormed := ?_
  }

  · simp [
      dtrDispatchSource,
      DTR.Body.WellFormed
    ]

  · intro pendingMessage hMembership

    simp only [
      dtrDispatchSource,
      List.mem_singleton
    ] at hMembership

    subst pendingMessage

    simp [
      dtrDispatchMessage,
      validModel,
      validReactiveClass,
      validMessageServer
    ]

theorem lf_dispatch_has_matching_dtr_dispatch :
    ∃ selectedMessage sourceStateAfter,
      DTR.DispatchStep
          validModel
          dtrDispatchSource
          selectedMessage
          sourceStateAfter ∧
      Correctness.PendingCorresponds
          selectedMessage
          lfDispatchAction ∧
      Correctness.StateCorresponds
          sourceStateAfter
          generatedLFDispatchTarget := by

  exact
    Correctness.dispatch_backward
      generatedLFDispatchStep
      dispatchSourceStatesCorrespond
      dtrDispatchSource_runtimeWellFormed

end Tests
end Relico
