import Relico.Common.StateStoreCoverage
import Relico.DTR.StoreModelWellFormed
import Relico.DTR.StoreRuntimeWellFormed
import Relico.DTR.StoreState
import Relico.DTR.StoreSyntax

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Construct the initial finite state store from source declarations.

Declaration order is retained exactly.
-/
def initialStore
    (declarations : List DTR.StateVariableDecl) :
    StateStore :=
  declarations.map
    (fun declaration =>
      (declaration.name,
       declaration.initialValue))

/--
The store built directly from declarations covers every declared state
variable.

This result does not require declaration-name uniqueness. The model
well-formedness predicate imposes uniqueness separately.
-/
theorem initialStore_covers
    (declarations : List DTR.StateVariableDecl) :
    StateStore.Covers
      (DTR.stateVariableNames
        declarations)
      (DTR.initialStore
        declarations) := by

  induction declarations with

  | nil =>
      simp [
        DTR.initialStore,
        DTR.stateVariableNames,
        StateStore.Covers
      ]

  | cons declaration remaining inductionHypothesis =>
      intro variableName hMember

      simp only [
        DTR.stateVariableNames,
        List.map_cons,
        List.mem_cons
      ] at hMember

      rcases hMember with
        hHead | hRemaining

      · subst variableName

        exact
          ⟨declaration.initialValue,
           by
             simp [
               DTR.initialStore,
               StateStore.lookup,
               Store.lookup
             ]⟩

      · rcases
            inductionHypothesis
              variableName
              hRemaining
          with
            ⟨value, hLookup⟩

        by_cases hSame :
            declaration.name =
              variableName

        · subst variableName

          exact
            ⟨declaration.initialValue,
             by
               simp [
                 DTR.initialStore,
                 StateStore.lookup,
                 Store.lookup
               ]⟩

        · exact
            ⟨value,
             by
               simpa [
                 DTR.initialStore,
                 StateStore.lookup,
                 Store.lookup,
                 hSame
               ] using
                 hLookup⟩

namespace StoreModel

/--
The finite-store DTR runtime state at constructor entry.

The actor starts at logical time zero with no pending messages. Its
active body is the constructor body.
-/
def initialState
    (model : DTR.StoreModel) :
    DTR.StoreState where

  currentTime :=
    0

  stateStore :=
    DTR.initialStore
      model.reactiveClass.stateVariables

  pendingMessages :=
    []

  activeBody :=
    model.reactiveClass.constructor.body

@[simp]
theorem initialState_currentTime
    (model : DTR.StoreModel) :
    (initialState model).currentTime =
      0 := by
  rfl

@[simp]
theorem initialState_stateStore
    (model : DTR.StoreModel) :
    (initialState model).stateStore =
      DTR.initialStore
        model.reactiveClass.stateVariables := by
  rfl

@[simp]
theorem initialState_pendingMessages
    (model : DTR.StoreModel) :
    (initialState model).pendingMessages =
      [] := by
  rfl

@[simp]
theorem initialState_activeBody
    (model : DTR.StoreModel) :
    (initialState model).activeBody =
      model.reactiveClass.constructor.body := by
  rfl

/--
A well-formed finite-store model produces a runtime-well-formed state
at constructor entry.
-/
theorem initialState_runtimeWellFormed
    (model : DTR.StoreModel)
    (hModel :
      DTR.StoreModel.WellFormed
        model) :
    DTR.StoreState.RuntimeWellFormed
      (DTR.stateVariableNames
        model.reactiveClass.stateVariables)
      model.reactiveClass.messageServer.name
      (initialState model) := by

  refine {
    coverage := ?_
    activeBody := ?_
    pendingTargets := ?_
  }

  · simpa [
      DTR.StoreState.Covers,
      initialState
    ] using
      DTR.initialStore_covers
        model.reactiveClass.stateVariables

  · simpa [
      initialState
    ] using
      hModel.constructorBodyWellFormed

  · intro pendingMessage hMember

    simp [
      initialState
    ] at hMember

end StoreModel
end DTR
end Relico
