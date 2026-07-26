import Relico.Common.WeakTransition
import Relico.LF.MultiStoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
Paper-level observable events for the detailed generated-LF multi-store
semantics.

Metric-time progression and reaction firing are observable. Microstep
progression and reaction-body statement execution are internal.
-/
inductive DetailedMultiStoreObservable where

  | timeAdvance :
      LogicalTime →
      LogicalTime →
      DetailedMultiStoreObservable

  | consume :
      ActionName →
      LogicalTime →
      DetailedMultiStoreObservable

deriving Repr, DecidableEq, BEq, Inhabited

/--
Labels for the detailed generated-LF semantic layer.
-/
inductive DetailedMultiStoreLabel where

  | tau :
      DetailedMultiStoreLabel

  | timeAdvance :
      LogicalTime →
      LogicalTime →
      DetailedMultiStoreLabel

  | microstepAdvance :
      LF.Tag →
      LF.Tag →
      DetailedMultiStoreLabel

  | consume :
      LF.PendingAction →
      LF.Reaction →
      DetailedMultiStoreLabel

deriving Repr, DecidableEq, BEq, Inhabited

namespace DetailedMultiStoreLabel

/--
Statement execution and pure LF microstep progression are internal.
-/
def isTau :
    LF.DetailedMultiStoreLabel →
    Prop

  | .tau =>
      True

  | .microstepAdvance _ _ =>
      True

  | .timeAdvance _ _ =>
      False

  | .consume _ _ =>
      False

/--
Project a detailed generated-LF label onto the paper-level observable
alphabet.
-/
def toObservable :
    LF.DetailedMultiStoreLabel →
    Option LF.DetailedMultiStoreObservable

  | .tau =>
      none

  | .microstepAdvance _ _ =>
      none

  | .timeAdvance before after =>
      some
        (.timeAdvance
          before
          after)

  | .consume selectedAction _selectedReaction =>
      some
        (.consume
          selectedAction.name
          selectedAction.tag.time)

@[simp]
theorem isTau_tau :
    isTau
      LF.DetailedMultiStoreLabel.tau := by

  exact True.intro

@[simp]
theorem isTau_microstepAdvance
    (before after : LF.Tag) :
    isTau
      (.microstepAdvance
        before
        after) := by

  exact True.intro

@[simp]
theorem toObservable_tau :
    toObservable
        LF.DetailedMultiStoreLabel.tau =
      none := by

  rfl

@[simp]
theorem toObservable_microstepAdvance
    (before after : LF.Tag) :
    toObservable
        (.microstepAdvance
          before
          after) =
      none := by

  rfl

end DetailedMultiStoreLabel

/--
States of the detailed generated-LF semantic layer.

`afterTime` records that metric time has advanced to the selected action time
but an LF microstep transition may remain. `dispatchReady` records that the
complete selected tag has been reached and reaction firing remains.

Both phase constructors embed the originating macro-dispatch witness.
-/
inductive DetailedMultiStoreState
    (messageReactions :
      List LF.Reaction) where

  | stable :
      LF.StoreState →
      DetailedMultiStoreState
        messageReactions

  | afterTime
      (before : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (after : LF.StoreState)
      (hDispatch :
        LF.MultiStoreDispatchStep
          messageReactions
          before
          selectedAction
          selectedReaction
          after) :
      DetailedMultiStoreState
        messageReactions

  | dispatchReady
      (before : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (after : LF.StoreState)
      (hDispatch :
        LF.MultiStoreDispatchStep
          messageReactions
          before
          selectedAction
          selectedReaction
          after) :
      DetailedMultiStoreState
        messageReactions

/--
Detailed one-step generated-LF semantics.

Statement execution is internal.

A future-tag dispatch first performs observable metric-time progression.
When the destination tag has a nonzero microstep, an internal microstep phase
follows. Reaction firing is the final observable consumption transition.

A same-metric-time dispatch with a later microstep performs only the internal
microstep phase before reaction firing. A dispatch at the current complete tag
fires directly.
-/
inductive DetailedMultiStoreStep
    (declaredVariables : List VarName)
    (logicalActions : List ActionName)
    (messageReactions :
      List LF.Reaction) :
    LF.DetailedMultiStoreState messageReactions →
    LF.DetailedMultiStoreLabel →
    LF.DetailedMultiStoreState messageReactions →
    Prop where

  | statement
      {before after : LF.StoreState}
      {label : LF.Label}
      (hStatement :
        LF.MultiStoreStep
          declaredVariables
          logicalActions
          before
          label
          after) :
      DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        (.stable before)
        .tau
        (.stable after)

  | timeAdvance
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
          after.currentTag.time) :
      DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        (.stable before)
        (.timeAdvance
          before.currentTag.time
          after.currentTag.time)
        (.afterTime
          before
          selectedAction
          selectedReaction
          after
          hDispatch)

  | microstepAfterTime
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
      (hPositiveMicrostep :
        0 <
          after.currentTag.microstep) :
      DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        (.afterTime
          before
          selectedAction
          selectedReaction
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
          selectedReaction
          after
          hDispatch)

  | consumeAfterTimeZero
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
      (hZeroMicrostep :
        after.currentTag.microstep =
          0) :
      DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        (.afterTime
          before
          selectedAction
          selectedReaction
          after
          hDispatch)
        (.consume
          selectedAction
          selectedReaction)
        (.stable after)

  | microstepSameTime
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
      DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        (.stable before)
        (.microstepAdvance
          before.currentTag
          after.currentTag)
        (.dispatchReady
          before
          selectedAction
          selectedReaction
          after
          hDispatch)

  | consumeReady
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
      DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        (.dispatchReady
          before
          selectedAction
          selectedReaction
          after
          hDispatch)
        (.consume
          selectedAction
          selectedReaction)
        (.stable after)

  | consumeNow
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
      DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        (.stable before)
        (.consume
          selectedAction
          selectedReaction)
        (.stable after)

/--
Finite executions of the detailed generated-LF multi-store semantics.
-/
inductive DetailedMultiStoreSteps
    (declaredVariables : List VarName)
    (logicalActions : List ActionName)
    (messageReactions :
      List LF.Reaction) :
    LF.DetailedMultiStoreState messageReactions →
    List LF.DetailedMultiStoreLabel →
    LF.DetailedMultiStoreState messageReactions →
    Prop where

  | refl
      (state :
        LF.DetailedMultiStoreState
          messageReactions) :
      DetailedMultiStoreSteps
        declaredVariables
        logicalActions
        messageReactions
        state
        []
        state

  | cons
      {before middle after :
        LF.DetailedMultiStoreState
          messageReactions}
      {label :
        LF.DetailedMultiStoreLabel}
      {remainingLabels :
        List LF.DetailedMultiStoreLabel}
      (hStep :
        LF.DetailedMultiStoreStep
          declaredVariables
          logicalActions
          messageReactions
          before
          label
          middle)
      (hSteps :
        DetailedMultiStoreSteps
          declaredVariables
          logicalActions
          messageReactions
          middle
          remainingLabels
          after) :
      DetailedMultiStoreSteps
        declaredVariables
        logicalActions
        messageReactions
        before
        (label :: remainingLabels)
        after

end LF
end Relico
