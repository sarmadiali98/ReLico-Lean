import Relico.LF.MultiStorePayloadSyntax
import Relico.LF.State

set_option autoImplicit false

namespace Relico
namespace LF

/--
Runtime state for the generated local payload-aware LF fragment.

The LF scheduler state includes a complete superdense tag. Persistent
reactor state and reaction-local parameters remain distinct.
-/
structure MultiStorePayloadState where
  currentTag :
    LF.Tag

  stateStore :
    StateStore

  parameters :
    ParameterStore

  pendingActions :
    LF.ActionQueue

  activeBody :
    LF.MultiStorePayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

namespace MultiStorePayloadState

/--
State produced by executing one successful generated assignment.
-/
def assignmentResult
    (state :
      LF.MultiStorePayloadState)
    (target :
      VarName)
    (value :
      Int)
    (remaining :
      LF.MultiStorePayloadBody) :
    LF.MultiStorePayloadState :=
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
State produced by scheduling one payload-bearing logical-action
occurrence.

`LF.Tag.schedule` places zero-delay actions at the next microstep and
positive-delay actions at the later metric time with microstep zero.
Appending preserves multiplicity.
-/
def scheduleResult
    (state :
      LF.MultiStorePayloadState)
    (actionName :
      ActionName)
    (payload :
      Payload)
    (delay :
      Delay)
    (remaining :
      LF.MultiStorePayloadBody) :
    LF.MultiStorePayloadState :=
  {
    state with

    pendingActions :=
      state.pendingActions ++
        [
          LF.PendingAction.scheduleWithPayload
            state.currentTag
            actionName
            payload
            delay
        ]

    activeBody :=
      remaining
  }

/--
Execute the next generated reaction statement when all expression
lookups succeed.
-/
def step?
    (state :
      LF.MultiStorePayloadState) :
    Option LF.MultiStorePayloadState :=
  match state.activeBody with

  | [] =>
      none

  | (.assign
        target
        expression) ::
      remaining =>

      match
        LF.MultiStorePayloadExpr.evaluate
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

  | (.schedule
        actionName
        payloadExpressions
        delay) ::
      remaining =>

      match
        LF.MultiStorePayloadExpr.evaluateAll
          state.stateStore
          state.parameters
          payloadExpressions
      with
      | none =>
          none

      | some payload =>
          some
            (scheduleResult
              state
              actionName
              payload
              delay
              remaining)

end MultiStorePayloadState

/--
One deterministic local target statement transition.
-/
def MultiStorePayloadStep
    (before after :
      LF.MultiStorePayloadState) :
    Prop :=
  LF.MultiStorePayloadState.step?
      before =
    some after

end LF
end Relico
