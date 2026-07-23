import Relico.Correctness.DispatchForward
import Relico.Tests.DispatchCorrectness

set_option autoImplicit false

namespace Relico
namespace Tests

theorem singleDispatchForwardCompatible :
    Correctness.ForwardDispatchCompatible
      dtrDispatchMessage
      []
      lfDispatchSource := by

  unfold Correctness.ForwardDispatchCompatible

  refine
    ⟨lfDispatchAction,
     [],
     ?_,
     ?_,
     Correctness.QueueCorresponds.nil,
     ?_,
     ?_⟩

  · exact
      Occurrence.RemovesOne.head []

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

  · intro candidate hCandidate

    simp only [
      lfDispatchSource,
      List.mem_singleton
    ] at hCandidate

    subst candidate

    exact
      LF.Tag.precedesOrEqual_refl
        lfDispatchAction.tag

  · simp [
      lfDispatchSource,
      lfCurrentDispatchTag,
      lfDispatchAction,
      lfDispatchTag,
      LF.Tag.PrecedesOrEqual
    ]

theorem dtr_dispatch_has_compatible_lf_dispatch :
    ∃ selectedAction targetStateAfter,
      LF.DispatchStep
          (Translation.translateCore validModel)
          lfDispatchSource
          selectedAction
          targetStateAfter ∧
      Correctness.PendingCorresponds
          dtrDispatchMessage
          selectedAction ∧
      Correctness.StateCorresponds
          dtrDispatchTarget
          targetStateAfter := by

  exact
    Correctness.dispatch_forward_of_compatible
      dtrMessageDispatch
      dispatchSourceStatesCorrespond
      singleDispatchForwardCompatible

end Tests
end Relico
