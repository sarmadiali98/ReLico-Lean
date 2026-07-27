import Relico.Common.WeakTransition
import Relico.DTR.BoundPayloadSemantics
import Relico.DTR.BoundPayloadDispatch

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Paper-level observables for parameter-aware detailed source execution.

Consumption retains the complete ordered payload so the detailed layer does not
erase the values subsequently bound to formal parameters.
-/
inductive DetailedBoundPayloadObservable where

  | timeAdvance :
      LogicalTime →
      LogicalTime →
      DetailedBoundPayloadObservable

  | consume :
      MsgName →
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

  | consume :
      DTR.PendingMessage →
      DetailedBoundPayloadLabel

deriving Repr, DecidableEq, BEq, Inhabited

namespace DetailedBoundPayloadLabel

def isTau :
    DTR.DetailedBoundPayloadLabel →
    Prop

  | .tau =>
      True

  | .timeAdvance _ _ =>
      False

  | .consume _ =>
      False

def toObservable :
    DTR.DetailedBoundPayloadLabel →
    Option DTR.DetailedBoundPayloadObservable

  | .tau =>
      none

  | .timeAdvance before after =>
      some
        (.timeAdvance
          before
          after)

  | .consume selectedMessage =>
      some
        (.consume
          selectedMessage.name
          selectedMessage.arrivalTime
          selectedMessage.payload)

end DetailedBoundPayloadLabel

inductive DetailedBoundPayloadState
    (server : DTR.PayloadMessageServer) where

  | stable :
      DTR.BoundPayloadState →
      DetailedBoundPayloadState
        server

  | dispatchReady
      (before : DTR.BoundPayloadState)
      (selectedMessage : DTR.PendingMessage)
      (after : DTR.BoundPayloadState)
      (hDispatch :
        DTR.BoundPayloadDispatchStep
          server
          before
          selectedMessage
          after) :
      DetailedBoundPayloadState
        server

inductive DetailedBoundPayloadStep
    (server : DTR.PayloadMessageServer) :
    DTR.DetailedBoundPayloadState server →
    DTR.DetailedBoundPayloadLabel →
    DTR.DetailedBoundPayloadState server →
    Prop where

  | statement
      {before after : DTR.BoundPayloadState}
      {label : DTR.BoundPayloadLabel}
      (hStatement :
        DTR.BoundPayloadStep
          server.name
          before
          label
          after) :
      DetailedBoundPayloadStep
        server
        (.stable before)
        .tau
        (.stable after)

  | timeAdvance
      {before after : DTR.BoundPayloadState}
      {selectedMessage : DTR.PendingMessage}
      (hDispatch :
        DTR.BoundPayloadDispatchStep
          server
          before
          selectedMessage
          after)
      (hFuture :
        before.currentTime <
          after.currentTime) :
      DetailedBoundPayloadStep
        server
        (.stable before)
        (.timeAdvance
          before.currentTime
          after.currentTime)
        (.dispatchReady
          before
          selectedMessage
          after
          hDispatch)

  | consumeReady
      {before after : DTR.BoundPayloadState}
      {selectedMessage : DTR.PendingMessage}
      (hDispatch :
        DTR.BoundPayloadDispatchStep
          server
          before
          selectedMessage
          after) :
      DetailedBoundPayloadStep
        server
        (.dispatchReady
          before
          selectedMessage
          after
          hDispatch)
        (.consume selectedMessage)
        (.stable after)

  | consumeNow
      {before after : DTR.BoundPayloadState}
      {selectedMessage : DTR.PendingMessage}
      (hDispatch :
        DTR.BoundPayloadDispatchStep
          server
          before
          selectedMessage
          after)
      (hSameTime :
        before.currentTime =
          after.currentTime) :
      DetailedBoundPayloadStep
        server
        (.stable before)
        (.consume selectedMessage)
        (.stable after)

inductive DetailedBoundPayloadSteps
    (server : DTR.PayloadMessageServer) :
    DTR.DetailedBoundPayloadState server →
    List DTR.DetailedBoundPayloadLabel →
    DTR.DetailedBoundPayloadState server →
    Prop where

  | refl
      (state :
        DTR.DetailedBoundPayloadState
          server) :
      DetailedBoundPayloadSteps
        server
        state
        []
        state

  | cons
      {before middle after :
        DTR.DetailedBoundPayloadState
          server}
      {label :
        DTR.DetailedBoundPayloadLabel}
      {remaining :
        List DTR.DetailedBoundPayloadLabel}
      (head :
        DTR.DetailedBoundPayloadStep
          server
          before
          label
          middle)
      (tail :
        DTR.DetailedBoundPayloadSteps
          server
          middle
          remaining
          after) :
      DetailedBoundPayloadSteps
        server
        before
        (label :: remaining)
        after


/--
Project a finite detailed bound-payload label trace onto the paper-level
observable alphabet.

Statement execution is erased. Time advancement and payload-bearing message
consumption remain observable.
-/
def detailedBoundPayloadObservableTrace
    (labels :
      List DTR.DetailedBoundPayloadLabel) :
    List DTR.DetailedBoundPayloadObservable :=
  Common.observableProjection
    DTR.DetailedBoundPayloadLabel.toObservable
    labels

@[simp]
theorem detailedBoundPayloadObservableTrace_nil :
    DTR.detailedBoundPayloadObservableTrace [] =
      [] := by
  rfl

@[simp]
theorem detailedBoundPayloadObservableTrace_tau_cons
    (remaining :
      List DTR.DetailedBoundPayloadLabel) :
    DTR.detailedBoundPayloadObservableTrace
        (DTR.DetailedBoundPayloadLabel.tau ::
          remaining) =
      DTR.detailedBoundPayloadObservableTrace
        remaining := by
  rfl

@[simp]
theorem detailedBoundPayloadObservableTrace_timeAdvance_cons
    (before after : LogicalTime)
    (remaining :
      List DTR.DetailedBoundPayloadLabel) :
    DTR.detailedBoundPayloadObservableTrace
        (DTR.DetailedBoundPayloadLabel.timeAdvance
            before
            after ::
          remaining) =
      DTR.DetailedBoundPayloadObservable.timeAdvance
          before
          after ::
        DTR.detailedBoundPayloadObservableTrace
          remaining := by
  rfl

@[simp]
theorem detailedBoundPayloadObservableTrace_consume_cons
    (selectedMessage : DTR.PendingMessage)
    (remaining :
      List DTR.DetailedBoundPayloadLabel) :
    DTR.detailedBoundPayloadObservableTrace
        (DTR.DetailedBoundPayloadLabel.consume
            selectedMessage ::
          remaining) =
      DTR.DetailedBoundPayloadObservable.consume
          selectedMessage.name
          selectedMessage.arrivalTime
          selectedMessage.payload ::
        DTR.detailedBoundPayloadObservableTrace
          remaining := by
  rfl

end DTR
end Relico
