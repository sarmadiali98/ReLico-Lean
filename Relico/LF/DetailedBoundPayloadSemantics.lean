import Relico.Common.WeakTransition
import Relico.LF.BoundPayloadSemantics
import Relico.LF.BoundPayloadDispatch

set_option autoImplicit false

namespace Relico
namespace LF

/--
Paper-level observables for parameter-aware detailed generated-LF execution.
-/
inductive DetailedBoundPayloadObservable where

  | timeAdvance :
      LogicalTime →
      LogicalTime →
      DetailedBoundPayloadObservable

  | consume :
      ActionName →
      LogicalTime →
      Payload →
      DetailedBoundPayloadObservable

deriving Repr, DecidableEq, BEq, Inhabited

inductive DetailedBoundPayloadLabel where

  | tau :
      DetailedBoundPayloadLabel

  | timeAdvance :
      LogicalTime →
      LogicalTime →
      DetailedBoundPayloadLabel

  | microstepAdvance :
      LF.Tag →
      LF.Tag →
      DetailedBoundPayloadLabel

  | consume :
      LF.PendingAction →
      DetailedBoundPayloadLabel

deriving Repr, DecidableEq, BEq, Inhabited

namespace DetailedBoundPayloadLabel

def isTau :
    LF.DetailedBoundPayloadLabel →
    Prop

  | .tau =>
      True

  | .microstepAdvance _ _ =>
      True

  | .timeAdvance _ _ =>
      False

  | .consume _ =>
      False

def toObservable :
    LF.DetailedBoundPayloadLabel →
    Option LF.DetailedBoundPayloadObservable

  | .tau =>
      none

  | .microstepAdvance _ _ =>
      none

  | .timeAdvance before after =>
      some
        (.timeAdvance
          before
          after)

  | .consume selectedAction =>
      some
        (.consume
          selectedAction.name
          selectedAction.tag.time
          selectedAction.payload)

end DetailedBoundPayloadLabel

inductive DetailedBoundPayloadState
    (reaction : LF.PayloadReaction) where

  | stable :
      LF.BoundPayloadState →
      DetailedBoundPayloadState
        reaction

  | afterTime
      (before : LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (after : LF.BoundPayloadState)
      (hDispatch :
        LF.BoundPayloadDispatchStep
          reaction
          before
          selectedAction
          after) :
      DetailedBoundPayloadState
        reaction

  | dispatchReady
      (before : LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (after : LF.BoundPayloadState)
      (hDispatch :
        LF.BoundPayloadDispatchStep
          reaction
          before
          selectedAction
          after) :
      DetailedBoundPayloadState
        reaction

inductive DetailedBoundPayloadStep
    (reaction : LF.PayloadReaction) :
    LF.DetailedBoundPayloadState reaction →
    LF.DetailedBoundPayloadLabel →
    LF.DetailedBoundPayloadState reaction →
    Prop where

  | statement
      {before after : LF.BoundPayloadState}
      {label : LF.BoundPayloadLabel}
      (hStatement :
        LF.BoundPayloadStep
          reaction.logicalAction
          before
          label
          after) :
      DetailedBoundPayloadStep
        reaction
        (.stable before)
        .tau
        (.stable after)

  | timeAdvance
      {before after : LF.BoundPayloadState}
      {selectedAction : LF.PendingAction}
      (hDispatch :
        LF.BoundPayloadDispatchStep
          reaction
          before
          selectedAction
          after)
      (hFuture :
        before.currentTag.time <
          after.currentTag.time) :
      DetailedBoundPayloadStep
        reaction
        (.stable before)
        (.timeAdvance
          before.currentTag.time
          after.currentTag.time)
        (.afterTime
          before
          selectedAction
          after
          hDispatch)

  | microstepAfterTime
      {before after : LF.BoundPayloadState}
      {selectedAction : LF.PendingAction}
      (hDispatch :
        LF.BoundPayloadDispatchStep
          reaction
          before
          selectedAction
          after)
      (hPositiveMicrostep :
        0 <
          after.currentTag.microstep) :
      DetailedBoundPayloadStep
        reaction
        (.afterTime
          before
          selectedAction
          after
          hDispatch)
        (.microstepAdvance
          {
            time :=
              after.currentTag.time

            microstep :=
              0
          }
          after.currentTag)
        (.dispatchReady
          before
          selectedAction
          after
          hDispatch)

  | consumeAfterTimeZero
      {before after : LF.BoundPayloadState}
      {selectedAction : LF.PendingAction}
      (hDispatch :
        LF.BoundPayloadDispatchStep
          reaction
          before
          selectedAction
          after)
      (hZeroMicrostep :
        after.currentTag.microstep =
          0) :
      DetailedBoundPayloadStep
        reaction
        (.afterTime
          before
          selectedAction
          after
          hDispatch)
        (.consume selectedAction)
        (.stable after)

  | microstepSameTime
      {before after : LF.BoundPayloadState}
      {selectedAction : LF.PendingAction}
      (hDispatch :
        LF.BoundPayloadDispatchStep
          reaction
          before
          selectedAction
          after)
      (hSameTime :
        before.currentTag.time =
          after.currentTag.time)
      (hLaterMicrostep :
        before.currentTag.microstep <
          after.currentTag.microstep) :
      DetailedBoundPayloadStep
        reaction
        (.stable before)
        (.microstepAdvance
          before.currentTag
          after.currentTag)
        (.dispatchReady
          before
          selectedAction
          after
          hDispatch)

  | consumeReady
      {before after : LF.BoundPayloadState}
      {selectedAction : LF.PendingAction}
      (hDispatch :
        LF.BoundPayloadDispatchStep
          reaction
          before
          selectedAction
          after) :
      DetailedBoundPayloadStep
        reaction
        (.dispatchReady
          before
          selectedAction
          after
          hDispatch)
        (.consume selectedAction)
        (.stable after)

  | consumeNow
      {before after : LF.BoundPayloadState}
      {selectedAction : LF.PendingAction}
      (hDispatch :
        LF.BoundPayloadDispatchStep
          reaction
          before
          selectedAction
          after)
      (hSameTag :
        before.currentTag =
          after.currentTag) :
      DetailedBoundPayloadStep
        reaction
        (.stable before)
        (.consume selectedAction)
        (.stable after)

inductive DetailedBoundPayloadSteps
    (reaction : LF.PayloadReaction) :
    LF.DetailedBoundPayloadState reaction →
    List LF.DetailedBoundPayloadLabel →
    LF.DetailedBoundPayloadState reaction →
    Prop where

  | refl
      (state :
        LF.DetailedBoundPayloadState
          reaction) :
      DetailedBoundPayloadSteps
        reaction
        state
        []
        state

  | cons
      {before middle after :
        LF.DetailedBoundPayloadState
          reaction}
      {label :
        LF.DetailedBoundPayloadLabel}
      {remaining :
        List LF.DetailedBoundPayloadLabel}
      (head :
        LF.DetailedBoundPayloadStep
          reaction
          before
          label
          middle)
      (tail :
        LF.DetailedBoundPayloadSteps
          reaction
          middle
          remaining
          after) :
      DetailedBoundPayloadSteps
        reaction
        before
        (label :: remaining)
        after


/--
Project a finite detailed generated-LF bound-payload label trace onto the
paper-level observable alphabet.

Statement execution and pure microstep administration are erased. Metric-time
advancement and payload-bearing reaction consumption remain observable.
-/
def detailedBoundPayloadObservableTrace
    (labels :
      List LF.DetailedBoundPayloadLabel) :
    List LF.DetailedBoundPayloadObservable :=
  Common.observableProjection
    LF.DetailedBoundPayloadLabel.toObservable
    labels

@[simp]
theorem detailedBoundPayloadObservableTrace_nil :
    LF.detailedBoundPayloadObservableTrace [] =
      [] := by
  rfl

@[simp]
theorem detailedBoundPayloadObservableTrace_tau_cons
    (remaining :
      List LF.DetailedBoundPayloadLabel) :
    LF.detailedBoundPayloadObservableTrace
        (LF.DetailedBoundPayloadLabel.tau ::
          remaining) =
      LF.detailedBoundPayloadObservableTrace
        remaining := by
  rfl

@[simp]
theorem detailedBoundPayloadObservableTrace_microstep_cons
    (before after : LF.Tag)
    (remaining :
      List LF.DetailedBoundPayloadLabel) :
    LF.detailedBoundPayloadObservableTrace
        (LF.DetailedBoundPayloadLabel.microstepAdvance
            before
            after ::
          remaining) =
      LF.detailedBoundPayloadObservableTrace
        remaining := by
  rfl

@[simp]
theorem detailedBoundPayloadObservableTrace_timeAdvance_cons
    (before after : LogicalTime)
    (remaining :
      List LF.DetailedBoundPayloadLabel) :
    LF.detailedBoundPayloadObservableTrace
        (LF.DetailedBoundPayloadLabel.timeAdvance
            before
            after ::
          remaining) =
      LF.DetailedBoundPayloadObservable.timeAdvance
          before
          after ::
        LF.detailedBoundPayloadObservableTrace
          remaining := by
  rfl

@[simp]
theorem detailedBoundPayloadObservableTrace_consume_cons
    (selectedAction : LF.PendingAction)
    (remaining :
      List LF.DetailedBoundPayloadLabel) :
    LF.detailedBoundPayloadObservableTrace
        (LF.DetailedBoundPayloadLabel.consume
            selectedAction ::
          remaining) =
      LF.DetailedBoundPayloadObservable.consume
          selectedAction.name
          selectedAction.tag.time
          selectedAction.payload ::
        LF.detailedBoundPayloadObservableTrace
          remaining := by
  rfl

end LF
end Relico
