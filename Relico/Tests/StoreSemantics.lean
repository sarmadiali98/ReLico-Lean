import Relico.DTR.StoreSemantics
import Relico.LF.StoreSemantics
import Relico.Tests.StateStoreCoverage

set_option autoImplicit false

namespace Relico
namespace Tests

def storeRuntimeMessageName :
    MsgName :=
  ⟨"tick"⟩

def storeRuntimeActionName :
    ActionName :=
  ⟨"tick_action"⟩

def dtrStoreAssignmentBefore :
    DTR.StoreState where
  currentTime :=
    0

  stateStore :=
    twoVariableStore

  pendingMessages :=
    []

  activeBody := [
    DTR.Stmt.assign
      secondStateVariableName
      (.stateVar
        stateVariableName)
  ]

def dtrStoreAssignmentAfter :
    DTR.StoreState where
  currentTime :=
    0

  stateStore :=
    StateStore.update
      twoVariableStore
      secondStateVariableName
      12

  pendingMessages :=
    []

  activeBody :=
    []

/--
A DTR assignment may read one declared variable and update another.
-/
theorem dtr_cross_variable_assignment :
    DTR.StoreStep
      [
        stateVariableName,
        secondStateVariableName
      ]
      storeRuntimeMessageName
      dtrStoreAssignmentBefore
      DTR.Label.internal
      dtrStoreAssignmentAfter := by

  apply DTR.StoreStep.assign

  · simp

  · rfl

theorem dtr_cross_variable_assignment_preserves_coverage :
    DTR.StoreState.Covers
      [
        stateVariableName,
        secondStateVariableName
      ]
      dtrStoreAssignmentAfter := by

  apply
    DTR.StoreStep.preserves_coverage
      dtr_cross_variable_assignment

  exact twoVariableStore_covers

example :
    StateStore.lookup
        dtrStoreAssignmentAfter.stateStore
        secondStateVariableName =
      some 12 := by

  simp [
    dtrStoreAssignmentAfter
  ]

example :
    StateStore.lookup
        dtrStoreAssignmentAfter.stateStore
        stateVariableName =
      some 12 := by

  change
    StateStore.lookup
        (StateStore.update
          twoVariableStore
          secondStateVariableName
          12)
        stateVariableName =
      some 12

  rw [
    StateStore.lookup_update_ne
      twoVariableStore
      12
      (by decide)
  ]

  rfl

def lfStoreAssignmentBefore :
    LF.StoreState where
  currentTag :=
    default

  stateStore :=
    twoVariableStore

  pendingActions :=
    []

  activeBody := [
    LF.Stmt.assign
      secondStateVariableName
      (.stateVar
        stateVariableName)
  ]

def lfStoreAssignmentAfter :
    LF.StoreState where
  currentTag :=
    default

  stateStore :=
    StateStore.update
      twoVariableStore
      secondStateVariableName
      12

  pendingActions :=
    []

  activeBody :=
    []

/--
A generated-LF assignment may read one declared reactor state variable
and update another.
-/
theorem lf_cross_variable_assignment :
    LF.StoreStep
      [
        stateVariableName,
        secondStateVariableName
      ]
      storeRuntimeActionName
      lfStoreAssignmentBefore
      LF.Label.internal
      lfStoreAssignmentAfter := by

  apply LF.StoreStep.assign

  · simp

  · rfl

theorem lf_cross_variable_assignment_preserves_coverage :
    LF.StoreState.Covers
      [
        stateVariableName,
        secondStateVariableName
      ]
      lfStoreAssignmentAfter := by

  apply
    LF.StoreStep.preserves_coverage
      lf_cross_variable_assignment

  exact twoVariableStore_covers

example :
    StateStore.lookup
        lfStoreAssignmentAfter.stateStore
        secondStateVariableName =
      some 12 := by

  simp [
    lfStoreAssignmentAfter
  ]

end Tests
end Relico
