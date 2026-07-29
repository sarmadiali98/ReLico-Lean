import Relico.DTR.MultiStorePayloadSyntax
import Relico.DTR.State

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Runtime state for the local payload-aware finite-store source fragment.

Persistent actor state and activation-local parameters remain distinct.
Pending-message multiplicity is represented by list occurrences.
-/
structure MultiStorePayloadState where
  currentTime :
    LogicalTime

  stateStore :
    StateStore

  parameters :
    ParameterStore

  pendingMessages :
    DTR.MessageBag

  activeBody :
    DTR.MultiStorePayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

namespace MultiStorePayloadState

/--
State produced by executing one successful source assignment.
-/
def assignmentResult
    (state :
      DTR.MultiStorePayloadState)
    (target :
      VarName)
    (value :
      Int)
    (remaining :
      DTR.MultiStorePayloadBody) :
    DTR.MultiStorePayloadState :=
  {
    state with

    stateStore :=
      StateStore.update
        state.stateStore
        target
        value

    activeBody :=
      remaining
  }

/--
State produced by executing one successful payload-bearing self-send.

The newly generated occurrence is appended. Equal values therefore
remain distinct list occurrences.
-/
def selfSendResult
    (state :
      DTR.MultiStorePayloadState)
    (messageName :
      MsgName)
    (payload :
      Payload)
    (delay :
      Delay)
    (remaining :
      DTR.MultiStorePayloadBody) :
    DTR.MultiStorePayloadState :=
  {
    state with

    pendingMessages :=
      state.pendingMessages ++
        [
          DTR.PendingMessage.scheduleWithPayload
            state.currentTime
            messageName
            payload
            delay
        ]

    activeBody :=
      remaining
  }

/--
Execute the next source statement when all required expression lookups
succeed.

A failed state-variable or parameter lookup blocks the statement and
returns `none`.
-/
def step?
    (state :
      DTR.MultiStorePayloadState) :
    Option DTR.MultiStorePayloadState :=
  match state.activeBody with

  | [] =>
      none

  | (.assign
        target
        expression) ::
      remaining =>

      match
        DTR.MultiStorePayloadExpr.evaluate
          state.stateStore
          state.parameters
          expression
      with
      | none =>
          none

      | some value =>
          some
            (assignmentResult
              state
              target
              value
              remaining)

  | (.selfSend
        messageName
        payloadExpressions
        delay) ::
      remaining =>

      match
        DTR.MultiStorePayloadExpr.evaluateAll
          state.stateStore
          state.parameters
          payloadExpressions
      with
      | none =>
          none

      | some payload =>
          some
            (selfSendResult
              state
              messageName
              payload
              delay
              remaining)

end MultiStorePayloadState

/--
One deterministic local source statement transition.
-/
def MultiStorePayloadStep
    (before after :
      DTR.MultiStorePayloadState) :
    Prop :=
  DTR.MultiStorePayloadState.step?
      before =
    some after

end DTR
end Relico
