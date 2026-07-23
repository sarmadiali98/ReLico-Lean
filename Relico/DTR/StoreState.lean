import Relico.Common.StateStoreCoverage
import Relico.DTR.State

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Store-backed DTR runtime state.

This representation exists alongside the legacy v0 state while the
operational semantics and correctness proofs are migrated
incrementally.
-/
structure StoreState where
  currentTime : LogicalTime
  stateStore : StateStore
  pendingMessages : MessageBag
  activeBody : Body
deriving Repr, DecidableEq, BEq, Inhabited

namespace State

/--
Embed a legacy single-value DTR state into a store-backed state.

The declared v0 state variable receives the legacy integer value.
-/
def toStoreState
    (declaredStateVar : VarName)
    (state : DTR.State) :
    DTR.StoreState where
  currentTime :=
    state.currentTime

  stateStore :=
    StateStore.singleton
      declaredStateVar
      state.stateValue

  pendingMessages :=
    state.pendingMessages

  activeBody :=
    state.activeBody

end State

namespace StoreState

/--
A store-backed DTR state covers a list of declarations when its state
store covers that list.
-/
def Covers
    (declaredVariables : List VarName)
    (state : DTR.StoreState) :
    Prop :=
  StateStore.Covers
    declaredVariables
    state.stateStore

/--
Attempt to project a store-backed state into the legacy v0 runtime
state.

Projection succeeds when the requested legacy state variable has a
binding.
-/
def toLegacyState
    (declaredStateVar : VarName)
    (state : DTR.StoreState) :
    Option DTR.State :=
  match
    StateStore.lookup
      state.stateStore
      declaredStateVar
  with
  | none =>
      none

  | some stateValue =>
      some {
        currentTime :=
          state.currentTime

        stateValue :=
          stateValue

        pendingMessages :=
          state.pendingMessages

        activeBody :=
          state.activeBody
      }

/--
Embedding a legacy DTR state and projecting it through the same
declared state variable returns the original state.
-/
@[simp]
theorem toLegacyState_toStoreState
    (declaredStateVar : VarName)
    (state : DTR.State) :
    toLegacyState
        declaredStateVar
        (DTR.State.toStoreState
          declaredStateVar
          state) =
      some state := by

  cases state

  simp [
    toLegacyState,
    DTR.State.toStoreState
  ]

/--
The store produced from a legacy v0 state covers its singleton
declaration list.
-/
theorem toStoreState_covers_singleton
    (declaredStateVar : VarName)
    (state : DTR.State) :
    Covers
      [declaredStateVar]
      (DTR.State.toStoreState
        declaredStateVar
        state) := by

  simpa [
    Covers,
    DTR.State.toStoreState
  ] using
    (StateStore.covers_singleton
      declaredStateVar
      state.stateValue)

end StoreState
end DTR
end Relico
