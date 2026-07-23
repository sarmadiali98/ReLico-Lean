import Relico.Common.StateStoreCoverage
import Relico.LF.State

set_option autoImplicit false

namespace Relico
namespace LF

/--
Store-backed runtime state for the generated LF subset.

This representation exists alongside the legacy v0 state during the
incremental semantic migration.
-/
structure StoreState where
  currentTag : Tag
  stateStore : StateStore
  pendingActions : ActionQueue
  activeBody : Body
deriving Repr, DecidableEq, BEq, Inhabited

namespace State

/--
Embed a legacy single-value LF state into a store-backed state.
-/
def toStoreState
    (declaredStateVar : VarName)
    (state : LF.State) :
    LF.StoreState where
  currentTag :=
    state.currentTag

  stateStore :=
    StateStore.singleton
      declaredStateVar
      state.stateValue

  pendingActions :=
    state.pendingActions

  activeBody :=
    state.activeBody

end State

namespace StoreState

/--
A store-backed LF state covers a list of reactor state declarations
when its state store covers that list.
-/
def Covers
    (declaredVariables : List VarName)
    (state : LF.StoreState) :
    Prop :=
  StateStore.Covers
    declaredVariables
    state.stateStore

/--
Attempt to project a store-backed LF state into the legacy v0 state.

Projection succeeds when the requested reactor state variable has a
binding.
-/
def toLegacyState
    (declaredStateVar : VarName)
    (state : LF.StoreState) :
    Option LF.State :=
  match
    StateStore.lookup
      state.stateStore
      declaredStateVar
  with
  | none =>
      none

  | some stateValue =>
      some {
        currentTag :=
          state.currentTag

        stateValue :=
          stateValue

        pendingActions :=
          state.pendingActions

        activeBody :=
          state.activeBody
      }

/--
Embedding a legacy LF state and projecting it through the same
declared state variable returns the original state.
-/
@[simp]
theorem toLegacyState_toStoreState
    (declaredStateVar : VarName)
    (state : LF.State) :
    toLegacyState
        declaredStateVar
        (LF.State.toStoreState
          declaredStateVar
          state) =
      some state := by

  cases state

  simp [
    toLegacyState,
    LF.State.toStoreState
  ]

/--
The store produced from a legacy v0 LF state covers its singleton
reactor-state declaration list.
-/
theorem toStoreState_covers_singleton
    (declaredStateVar : VarName)
    (state : LF.State) :
    Covers
      [declaredStateVar]
      (LF.State.toStoreState
        declaredStateVar
        state) := by

  simpa [
    Covers,
    LF.State.toStoreState
  ] using
    (StateStore.covers_singleton
      declaredStateVar
      state.stateValue)

end StoreState
end LF
end Relico
