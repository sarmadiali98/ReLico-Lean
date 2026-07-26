import Relico.Correctness.DetailedMultiStoreRefinement

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedMultiStoreSemantics

theorem dtr_tau_is_internal :
    DTR.DetailedMultiStoreLabel.isTau
      DTR.DetailedMultiStoreLabel.tau := by

  exact True.intro

theorem lf_tau_is_internal :
    LF.DetailedMultiStoreLabel.isTau
      LF.DetailedMultiStoreLabel.tau := by

  exact True.intro

theorem lf_microstep_is_internal
    (before after : LF.Tag) :
    LF.DetailedMultiStoreLabel.isTau
      (.microstepAdvance
        before
        after) := by

  exact True.intro

theorem dtr_internal_projection_empty :
    Common.observableProjection
        DTR.DetailedMultiStoreLabel.toObservable
        [
          DTR.DetailedMultiStoreLabel.tau
        ] =
      [] := by

  rfl

theorem lf_internal_projection_empty
    (before after : LF.Tag) :
    Common.observableProjection
        LF.DetailedMultiStoreLabel.toObservable
        [
          LF.DetailedMultiStoreLabel.tau,
          LF.DetailedMultiStoreLabel.microstepAdvance
            before
            after
        ] =
      [] := by

  rfl

theorem dtr_time_projection
    (before after : LogicalTime) :
    Common.observableProjection
        DTR.DetailedMultiStoreLabel.toObservable
        [
          DTR.DetailedMultiStoreLabel.timeAdvance
            before
            after
        ] =
      [
        DTR.DetailedMultiStoreObservable.timeAdvance
          before
          after
      ] := by

  rfl

theorem lf_time_projection
    (before after : LogicalTime) :
    Common.observableProjection
        LF.DetailedMultiStoreLabel.toObservable
        [
          LF.DetailedMultiStoreLabel.timeAdvance
            before
            after
        ] =
      [
        LF.DetailedMultiStoreObservable.timeAdvance
          before
          after
      ] := by

  rfl

theorem dtr_consume_projection
    (selectedMessage : DTR.PendingMessage)
    (selectedServer : DTR.MessageServer) :
    Common.observableProjection
        DTR.DetailedMultiStoreLabel.toObservable
        [
          DTR.DetailedMultiStoreLabel.consume
            selectedMessage
            selectedServer
        ] =
      [
        DTR.DetailedMultiStoreObservable.consume
          selectedMessage.name
          selectedMessage.arrivalTime
      ] := by

  rfl

theorem lf_consume_projection
    (selectedAction : LF.PendingAction)
    (selectedReaction : LF.Reaction) :
    Common.observableProjection
        LF.DetailedMultiStoreLabel.toObservable
        [
          LF.DetailedMultiStoreLabel.consume
            selectedAction
            selectedReaction
        ] =
      [
        LF.DetailedMultiStoreObservable.consume
          selectedAction.name
          selectedAction.tag.time
      ] := by

  rfl

theorem every_dtr_macro_dispatch_has_detailed_execution
    {declaredVariables : List VarName}
    {messageServers :
      List DTR.MessageServer}
    {before after : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    (hDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    ∃ labels,
      DTR.DetailedMultiStoreSteps
        declaredVariables
        messageServers
        (.stable before)
        labels
        (.stable after) := by

  exact
    Correctness.dtrDetailed_dispatch
      hDispatch

theorem every_lf_macro_dispatch_has_detailed_execution
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions :
      List LF.Reaction}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    ∃ labels,
      LF.DetailedMultiStoreSteps
        declaredVariables
        logicalActions
        messageReactions
        (.stable before)
        labels
        (.stable after) := by

  exact
    Correctness.lfDetailed_dispatch
      hDispatch

end DetailedMultiStoreSemantics
end Tests
end Relico
