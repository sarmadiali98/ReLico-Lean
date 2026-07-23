import Relico.DTR.StoreState
import Relico.LF.StoreState

set_option autoImplicit false

namespace Relico
namespace Tests

def runtimeStateVariable :
    VarName :=
  ⟨"x"⟩

def legacyDTRRuntimeState :
    DTR.State where
  currentTime :=
    default

  stateValue :=
    17

  pendingMessages :=
    []

  activeBody :=
    []

def legacyLFRuntimeState :
    LF.State where
  currentTag :=
    default

  stateValue :=
    23

  pendingActions :=
    []

  activeBody :=
    []

example :
    (DTR.State.toStoreState
      runtimeStateVariable
      legacyDTRRuntimeState).stateStore =
      StateStore.singleton
        runtimeStateVariable
        17 := by
  rfl

example :
    DTR.StoreState.toLegacyState
        runtimeStateVariable
        (DTR.State.toStoreState
          runtimeStateVariable
          legacyDTRRuntimeState) =
      some legacyDTRRuntimeState := by

  exact
    DTR.StoreState.toLegacyState_toStoreState
      runtimeStateVariable
      legacyDTRRuntimeState

example :
    DTR.StoreState.Covers
      [runtimeStateVariable]
      (DTR.State.toStoreState
        runtimeStateVariable
        legacyDTRRuntimeState) := by

  exact
    DTR.StoreState.toStoreState_covers_singleton
      runtimeStateVariable
      legacyDTRRuntimeState

example :
    (LF.State.toStoreState
      runtimeStateVariable
      legacyLFRuntimeState).stateStore =
      StateStore.singleton
        runtimeStateVariable
        23 := by
  rfl

example :
    LF.StoreState.toLegacyState
        runtimeStateVariable
        (LF.State.toStoreState
          runtimeStateVariable
          legacyLFRuntimeState) =
      some legacyLFRuntimeState := by

  exact
    LF.StoreState.toLegacyState_toStoreState
      runtimeStateVariable
      legacyLFRuntimeState

example :
    LF.StoreState.Covers
      [runtimeStateVariable]
      (LF.State.toStoreState
        runtimeStateVariable
        legacyLFRuntimeState) := by

  exact
    LF.StoreState.toStoreState_covers_singleton
      runtimeStateVariable
      legacyLFRuntimeState

end Tests
end Relico
