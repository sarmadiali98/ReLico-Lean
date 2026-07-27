import Relico.DTR.DetailedBoundPayloadSemantics
import Relico.LF.DetailedBoundPayloadSemantics

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadSemantics

theorem source_statement_lifts_to_detailed_tau
    {server : DTR.PayloadMessageServer}
    {before after : DTR.BoundPayloadState}
    {label : DTR.BoundPayloadLabel}
    (hStep :
      DTR.BoundPayloadStep
        server.name
        before
        label
        after) :
    DTR.DetailedBoundPayloadStep
      server
      (.stable before)
      .tau
      (.stable after) := by

  exact
    DTR.DetailedBoundPayloadStep.statement
      hStep

theorem target_statement_lifts_to_detailed_tau
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {label : LF.BoundPayloadLabel}
    (hStep :
      LF.BoundPayloadStep
        reaction.logicalAction
        before
        label
        after) :
    LF.DetailedBoundPayloadStep
      reaction
      (.stable before)
      .tau
      (.stable after) := by

  exact
    LF.DetailedBoundPayloadStep.statement
      hStep

theorem source_detailed_refl
    (server : DTR.PayloadMessageServer)
    (state : DTR.BoundPayloadState) :
    DTR.DetailedBoundPayloadSteps
      server
      (.stable state)
      []
      (.stable state) := by

  exact
    DTR.DetailedBoundPayloadSteps.refl
      (.stable state)

theorem target_detailed_refl
    (reaction : LF.PayloadReaction)
    (state : LF.BoundPayloadState) :
    LF.DetailedBoundPayloadSteps
      reaction
      (.stable state)
      []
      (.stable state) := by

  exact
    LF.DetailedBoundPayloadSteps.refl
      (.stable state)

theorem source_consumption_observable_retains_payload
    (selectedMessage : DTR.PendingMessage) :
    DTR.DetailedBoundPayloadLabel.toObservable
        (.consume selectedMessage) =
      some
        (.consume
          selectedMessage.name
          selectedMessage.arrivalTime
          selectedMessage.payload) := by

  rfl

theorem target_consumption_observable_retains_payload
    (selectedAction : LF.PendingAction) :
    LF.DetailedBoundPayloadLabel.toObservable
        (.consume selectedAction) =
      some
        (.consume
          selectedAction.name
          selectedAction.tag.time
          selectedAction.payload) := by

  rfl

theorem source_tau_is_erased
    (remaining :
      List DTR.DetailedBoundPayloadLabel) :
    DTR.detailedBoundPayloadObservableTrace
        (.tau :: remaining) =
      DTR.detailedBoundPayloadObservableTrace
        remaining := by

  simp

theorem target_microstep_is_erased
    (before after : LF.Tag)
    (remaining :
      List LF.DetailedBoundPayloadLabel) :
    LF.detailedBoundPayloadObservableTrace
        (.microstepAdvance before after ::
          remaining) =
      LF.detailedBoundPayloadObservableTrace
        remaining := by

  simp

end DetailedBoundPayloadSemantics
end Tests
end Relico
