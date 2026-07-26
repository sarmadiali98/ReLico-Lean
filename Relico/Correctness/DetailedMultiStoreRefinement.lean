import Relico.DTR.DetailedMultiStoreSemantics
import Relico.LF.DetailedMultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Every executable DTR statement step is one internal detailed transition.
-/
theorem dtrDetailed_statement
    {declaredVariables : List VarName}
    {messageServers :
      List DTR.MessageServer}
    {before after : DTR.StoreState}
    {label : DTR.Label}
    (hStatement :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        before
        label
        after) :
    DTR.DetailedMultiStoreStep
      declaredVariables
      messageServers
      (.stable before)
      .tau
      (.stable after) := by

  exact
    DTR.DetailedMultiStoreStep.statement
      hStatement

/--
A future DTR macro dispatch refines to observable time progression followed by
observable message consumption.
-/
theorem dtrDetailed_dispatch_future
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
        after)
    (hFuture :
      before.currentTime <
        after.currentTime) :
    DTR.DetailedMultiStoreSteps
      declaredVariables
      messageServers
      (.stable before)
      [
        .timeAdvance
          before.currentTime
          after.currentTime,

        .consume
          selectedMessage
          selectedServer
      ]
      (.stable after) := by

  exact
    DTR.DetailedMultiStoreSteps.cons
      (DTR.DetailedMultiStoreStep.timeAdvance
        hDispatch
        hFuture)
      (DTR.DetailedMultiStoreSteps.cons
        (DTR.DetailedMultiStoreStep.consumeReady
          hDispatch)
        (DTR.DetailedMultiStoreSteps.refl
          (.stable after)))

/--
A same-time DTR macro dispatch refines directly to observable message
consumption.
-/
theorem dtrDetailed_dispatch_sameTime
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
        after)
    (hSameTime :
      before.currentTime =
        after.currentTime) :
    DTR.DetailedMultiStoreSteps
      declaredVariables
      messageServers
      (.stable before)
      [
        .consume
          selectedMessage
          selectedServer
      ]
      (.stable after) := by

  exact
    DTR.DetailedMultiStoreSteps.cons
      (DTR.DetailedMultiStoreStep.consumeNow
        hDispatch
        hSameTime)
      (DTR.DetailedMultiStoreSteps.refl
        (.stable after))

/--
A DTR macro dispatch never moves logical time backwards.
-/
theorem dtrMultiStoreDispatch_time_le
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
    before.currentTime ≤
      after.currentTime := by

  cases hDispatch with

  | fire
      currentTime
      stateStore
      pendingMessages
      remainingMessages
      selectedMessage
      selectedServer
      hServerDeclared
      hRemoved
      hPriorityEligible
      hNotPast
      hTarget =>

      exact hNotPast

/--
Every DTR macro dispatch has a finite detailed execution.
-/
theorem dtrDetailed_dispatch
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

  have hTimeOrder :
      before.currentTime ≤
        after.currentTime :=
    dtrMultiStoreDispatch_time_le
      hDispatch

  rcases
      Nat.lt_or_eq_of_le
        hTimeOrder
    with
      hFuture | hSameTime

  · exact
      ⟨[
          .timeAdvance
            before.currentTime
            after.currentTime,

          .consume
            selectedMessage
            selectedServer
        ],
       dtrDetailed_dispatch_future
         hDispatch
         hFuture⟩

  · exact
      ⟨[
          .consume
            selectedMessage
            selectedServer
        ],
       dtrDetailed_dispatch_sameTime
         hDispatch
         hSameTime⟩

/--
Every executable generated-LF statement step is one internal detailed
transition.
-/
theorem lfDetailed_statement
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions :
      List LF.Reaction}
    {before after : LF.StoreState}
    {label : LF.Label}
    (hStatement :
      LF.MultiStoreStep
        declaredVariables
        logicalActions
        before
        label
        after) :
    LF.DetailedMultiStoreStep
      declaredVariables
      logicalActions
      messageReactions
      (.stable before)
      .tau
      (.stable after) := by

  exact
    LF.DetailedMultiStoreStep.statement
      hStatement

/--
A future generated-LF macro dispatch whose destination microstep is zero
refines to observable metric-time progression followed by reaction firing.
-/
theorem lfDetailed_dispatch_future_zero
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
        after)
    (hFuture :
      before.currentTag.time <
        after.currentTag.time)
    (hZeroMicrostep :
      after.currentTag.microstep =
        0) :
    LF.DetailedMultiStoreSteps
      declaredVariables
      logicalActions
      messageReactions
      (.stable before)
      [
        .timeAdvance
          before.currentTag.time
          after.currentTag.time,

        .consume
          selectedAction
          selectedReaction
      ]
      (.stable after) := by

  exact
    LF.DetailedMultiStoreSteps.cons
      (LF.DetailedMultiStoreStep.timeAdvance
        hDispatch
        hFuture)
      (LF.DetailedMultiStoreSteps.cons
        (LF.DetailedMultiStoreStep.consumeAfterTimeZero
          hDispatch
          hZeroMicrostep)
        (LF.DetailedMultiStoreSteps.refl
          (.stable after)))

/--
A future generated-LF macro dispatch with a positive destination microstep
refines to metric-time progression, internal microstep progression, and
reaction firing.
-/
theorem lfDetailed_dispatch_future_positiveMicrostep
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
        after)
    (hFuture :
      before.currentTag.time <
        after.currentTag.time)
    (hPositiveMicrostep :
      0 <
        after.currentTag.microstep) :
    LF.DetailedMultiStoreSteps
      declaredVariables
      logicalActions
      messageReactions
      (.stable before)
      [
        .timeAdvance
          before.currentTag.time
          after.currentTag.time,

        .microstepAdvance
          {
            time :=
              after.currentTag.time

            microstep :=
              0
          }
          after.currentTag,

        .consume
          selectedAction
          selectedReaction
      ]
      (.stable after) := by

  exact
    LF.DetailedMultiStoreSteps.cons
      (LF.DetailedMultiStoreStep.timeAdvance
        hDispatch
        hFuture)
      (LF.DetailedMultiStoreSteps.cons
        (LF.DetailedMultiStoreStep.microstepAfterTime
          hDispatch
          hPositiveMicrostep)
        (LF.DetailedMultiStoreSteps.cons
          (LF.DetailedMultiStoreStep.consumeReady
            hDispatch)
          (LF.DetailedMultiStoreSteps.refl
            (.stable after))))

/--
A same-metric-time generated-LF macro dispatch at a later microstep refines to
internal microstep progression followed by reaction firing.
-/
theorem lfDetailed_dispatch_laterMicrostep
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
        after)
    (hSameTime :
      before.currentTag.time =
        after.currentTag.time)
    (hLaterMicrostep :
      before.currentTag.microstep <
        after.currentTag.microstep) :
    LF.DetailedMultiStoreSteps
      declaredVariables
      logicalActions
      messageReactions
      (.stable before)
      [
        .microstepAdvance
          before.currentTag
          after.currentTag,

        .consume
          selectedAction
          selectedReaction
      ]
      (.stable after) := by

  exact
    LF.DetailedMultiStoreSteps.cons
      (LF.DetailedMultiStoreStep.microstepSameTime
        hDispatch
        hSameTime
        hLaterMicrostep)
      (LF.DetailedMultiStoreSteps.cons
        (LF.DetailedMultiStoreStep.consumeReady
          hDispatch)
        (LF.DetailedMultiStoreSteps.refl
          (.stable after)))

/--
A generated-LF macro dispatch at the current complete tag refines directly to
reaction firing.
-/
theorem lfDetailed_dispatch_sameTag
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
        after)
    (hSameTime :
      before.currentTag.time =
        after.currentTag.time)
    (hSameMicrostep :
      before.currentTag.microstep =
        after.currentTag.microstep) :
    LF.DetailedMultiStoreSteps
      declaredVariables
      logicalActions
      messageReactions
      (.stable before)
      [
        .consume
          selectedAction
          selectedReaction
      ]
      (.stable after) := by

  exact
    LF.DetailedMultiStoreSteps.cons
      (LF.DetailedMultiStoreStep.consumeNow
        hDispatch
        hSameTime
        hSameMicrostep)
      (LF.DetailedMultiStoreSteps.refl
        (.stable after))

/--
A generated-LF macro dispatch preserves complete-tag order.
-/
theorem lfMultiStoreDispatch_tagOrder
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
    LF.Tag.PrecedesOrEqual
      before.currentTag
      after.currentTag := by

  cases hDispatch with

  | fire
      currentTag
      stateStore
      pendingActions
      remainingActions
      selectedAction
      selectedReaction
      hReactionDeclared
      hRemoved
      hPriorityEligible
      hNotPast
      hTrigger =>

      exact hNotPast

/--
At equal metric time, a generated-LF macro dispatch cannot move to an earlier
microstep.
-/
theorem lfMultiStoreDispatch_microstep_le_of_sameTime
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
        after)
    (hSameTime :
      before.currentTag.time =
        after.currentTag.time) :
    before.currentTag.microstep ≤
      after.currentTag.microstep := by

  have hOrder :
      LF.Tag.PrecedesOrEqual
        before.currentTag
        after.currentTag :=
    lfMultiStoreDispatch_tagOrder
      hDispatch

  change
    before.currentTag.time <
          after.currentTag.time ∨
      (before.currentTag.time =
            after.currentTag.time ∧
        before.currentTag.microstep ≤
          after.currentTag.microstep)
    at hOrder

  rcases hOrder with
    hEarlier | hSame

  · exact
      False.elim
        ((Nat.ne_of_lt hEarlier)
          hSameTime)

  · exact hSame.2

/--
Every generated-LF macro dispatch has a finite detailed execution.
-/
theorem lfDetailed_dispatch
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

  have hTagOrder :
      LF.Tag.PrecedesOrEqual
        before.currentTag
        after.currentTag :=
    lfMultiStoreDispatch_tagOrder
      hDispatch

  have hMetricTimeOrder :
      before.currentTag.time ≤
        after.currentTag.time :=
    LF.Tag.time_le_of_precedesOrEqual
      hTagOrder

  rcases
      Nat.lt_or_eq_of_le
        hMetricTimeOrder
    with
      hFuture | hSameTime

  · by_cases hZeroMicrostep :
      after.currentTag.microstep =
        0

    · exact
        ⟨[
            .timeAdvance
              before.currentTag.time
              after.currentTag.time,

            .consume
              selectedAction
              selectedReaction
          ],
         lfDetailed_dispatch_future_zero
           hDispatch
           hFuture
           hZeroMicrostep⟩

    · have hPositiveMicrostep :
          0 <
            after.currentTag.microstep :=
        Nat.pos_of_ne_zero
          hZeroMicrostep

      exact
        ⟨[
            .timeAdvance
              before.currentTag.time
              after.currentTag.time,

            .microstepAdvance
              {
                time :=
                  after.currentTag.time

                microstep :=
                  0
              }
              after.currentTag,

            .consume
              selectedAction
              selectedReaction
          ],
         lfDetailed_dispatch_future_positiveMicrostep
           hDispatch
           hFuture
           hPositiveMicrostep⟩

  · have hMicrostepOrder :
        before.currentTag.microstep ≤
          after.currentTag.microstep :=
      lfMultiStoreDispatch_microstep_le_of_sameTime
        hDispatch
        hSameTime

    rcases
        Nat.lt_or_eq_of_le
          hMicrostepOrder
      with
        hLaterMicrostep | hSameMicrostep

    · exact
        ⟨[
            .microstepAdvance
              before.currentTag
              after.currentTag,

            .consume
              selectedAction
              selectedReaction
          ],
         lfDetailed_dispatch_laterMicrostep
           hDispatch
           hSameTime
           hLaterMicrostep⟩

    · exact
        ⟨[
            .consume
              selectedAction
              selectedReaction
          ],
         lfDetailed_dispatch_sameTag
           hDispatch
           hSameTime
           hSameMicrostep⟩

end Correctness
end Relico
