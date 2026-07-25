import Relico.DTR.MultiStoreModelWellFormed
import Relico.DTR.MultiStoreRuntimeWellFormed
import Relico.DTR.StoreInitialization

set_option autoImplicit false

namespace Relico
namespace DTR
namespace MultiStoreModel

/--
The finite-store DTR runtime state at constructor entry for a model
with multiple message servers.

Execution begins at logical time zero with the declaration-derived
store, no pending messages, and the constructor body active.
-/
def initialState
    (model : DTR.MultiStoreModel) :
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
    (model : DTR.MultiStoreModel) :
    (initialState model).currentTime =
      0 := by
  rfl

@[simp]
theorem initialState_stateStore
    (model : DTR.MultiStoreModel) :
    (initialState model).stateStore =
      DTR.initialStore
        model.reactiveClass.stateVariables := by
  rfl

@[simp]
theorem initialState_pendingMessages
    (model : DTR.MultiStoreModel) :
    (initialState model).pendingMessages =
      [] := by
  rfl

@[simp]
theorem initialState_activeBody
    (model : DTR.MultiStoreModel) :
    (initialState model).activeBody =
      model.reactiveClass.constructor.body := by
  rfl

/--
A well-formed multi-server source model begins in a runtime-well-formed
state.
-/
theorem initialState_runtimeWellFormed
    (model : DTR.MultiStoreModel)
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model) :
    DTR.StoreState.MultiStoreRuntimeWellFormed
      (DTR.stateVariableNames
        model.reactiveClass.stateVariables)
      model.reactiveClass.messageServers
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

end MultiStoreModel
end DTR
end Relico
