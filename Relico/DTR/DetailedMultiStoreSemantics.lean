import Relico.Common.WeakTransition
import Relico.DTR.MultiStoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Paper-level observable events for the detailed DTR multi-store semantics.

Statement execution is internal. Logical-time progression and message
consumption are observable.
-/
inductive DetailedMultiStoreObservable where

  | timeAdvance :
      LogicalTime →
      LogicalTime →
      DetailedMultiStoreObservable

  | consume :
      MsgName →
      LogicalTime →
      DetailedMultiStoreObservable

deriving Repr, DecidableEq, BEq, Inhabited

/--
Labels for the detailed DTR multi-store semantic layer.
-/
inductive DetailedMultiStoreLabel where

  | tau :
      DetailedMultiStoreLabel

  | timeAdvance :
      LogicalTime →
      LogicalTime →
      DetailedMultiStoreLabel

  | consume :
      DTR.PendingMessage →
      DTR.MessageServer →
      DetailedMultiStoreLabel

deriving Repr, DecidableEq, BEq, Inhabited

namespace DetailedMultiStoreLabel

/--
Only statement execution is internal in the current detailed DTR layer.
-/
def isTau :
    DTR.DetailedMultiStoreLabel →
    Prop

  | .tau =>
      True

  | .timeAdvance _ _ =>
      False

  | .consume _ _ =>
      False

/--
Project a detailed DTR label onto the paper-level observable alphabet.
-/
def toObservable :
    DTR.DetailedMultiStoreLabel →
    Option DTR.DetailedMultiStoreObservable

  | .tau =>
      none

  | .timeAdvance before after =>
      some
        (.timeAdvance
          before
          after)

  | .consume selectedMessage _selectedServer =>
      some
        (.consume
          selectedMessage.name
          selectedMessage.arrivalTime)

@[simp]
theorem isTau_tau :
    isTau
      DTR.DetailedMultiStoreLabel.tau := by

  exact True.intro

@[simp]
theorem toObservable_tau :
    toObservable
        DTR.DetailedMultiStoreLabel.tau =
      none := by

  rfl

end DetailedMultiStoreLabel

/--
States of the detailed DTR semantic layer.

Stable states contain an ordinary executable runtime state. A dispatch-ready
state records that an observable time-progress phase has completed and that
the corresponding observable message-consumption phase remains.

The embedded macro-dispatch witness prevents construction of an invalid
dispatch-ready phase.
-/
inductive DetailedMultiStoreState
    (messageServers :
      List DTR.MessageServer) where

  | stable :
      DTR.StoreState →
      DetailedMultiStoreState
        messageServers

  | dispatchReady
      (before : DTR.StoreState)
      (selectedMessage : DTR.PendingMessage)
      (selectedServer : DTR.MessageServer)
      (after : DTR.StoreState)
      (hDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          before
          selectedMessage
          selectedServer
          after) :
      DetailedMultiStoreState
        messageServers

/--
Detailed one-step DTR semantics.

Every executable statement is represented by one internal transition.

A future dispatch is represented by an observable logical-time transition
followed by observable message consumption. A dispatch already at the current
logical time is represented directly by observable message consumption.
-/
inductive DetailedMultiStoreStep
    (declaredVariables : List VarName)
    (messageServers :
      List DTR.MessageServer) :
    DTR.DetailedMultiStoreState messageServers →
    DTR.DetailedMultiStoreLabel →
    DTR.DetailedMultiStoreState messageServers →
    Prop where

  | statement
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
      DetailedMultiStoreStep
        declaredVariables
        messageServers
        (.stable before)
        .tau
        (.stable after)

  | timeAdvance
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
      DetailedMultiStoreStep
        declaredVariables
        messageServers
        (.stable before)
        (.timeAdvance
          before.currentTime
          after.currentTime)
        (.dispatchReady
          before
          selectedMessage
          selectedServer
          after
          hDispatch)

  | consumeReady
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
      DetailedMultiStoreStep
        declaredVariables
        messageServers
        (.dispatchReady
          before
          selectedMessage
          selectedServer
          after
          hDispatch)
        (.consume
          selectedMessage
          selectedServer)
        (.stable after)

  | consumeNow
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
      DetailedMultiStoreStep
        declaredVariables
        messageServers
        (.stable before)
        (.consume
          selectedMessage
          selectedServer)
        (.stable after)

/--
Finite executions of the detailed DTR multi-store semantics.
-/
inductive DetailedMultiStoreSteps
    (declaredVariables : List VarName)
    (messageServers :
      List DTR.MessageServer) :
    DTR.DetailedMultiStoreState messageServers →
    List DTR.DetailedMultiStoreLabel →
    DTR.DetailedMultiStoreState messageServers →
    Prop where

  | refl
      (state :
        DTR.DetailedMultiStoreState
          messageServers) :
      DetailedMultiStoreSteps
        declaredVariables
        messageServers
        state
        []
        state

  | cons
      {before middle after :
        DTR.DetailedMultiStoreState
          messageServers}
      {label :
        DTR.DetailedMultiStoreLabel}
      {remainingLabels :
        List DTR.DetailedMultiStoreLabel}
      (hStep :
        DTR.DetailedMultiStoreStep
          declaredVariables
          messageServers
          before
          label
          middle)
      (hSteps :
        DetailedMultiStoreSteps
          declaredVariables
          messageServers
          middle
          remainingLabels
          after) :
      DetailedMultiStoreSteps
        declaredVariables
        messageServers
        before
        (label :: remainingLabels)
        after

end DTR
end Relico
