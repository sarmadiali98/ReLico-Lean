import Relico.Common.StateStoreCoverage
import Relico.Tests.StoreEvaluation

set_option autoImplicit false

namespace Relico
namespace Tests

theorem twoVariableStore_covers :
    StateStore.Covers
      [
        stateVariableName,
        secondStateVariableName
      ]
      twoVariableStore := by

  intro variableName hMember

  simp at hMember

  rcases hMember with
    hFirst | hSecond

  · subst variableName
    exact ⟨12, rfl⟩

  · subst variableName
    exact ⟨34, rfl⟩

theorem updating_first_variable_preserves_coverage :
    StateStore.Covers
      [
        stateVariableName,
        secondStateVariableName
      ]
      (StateStore.update
        twoVariableStore
        stateVariableName
        99) := by

  exact
    StateStore.covers_update
      [
        stateVariableName,
        secondStateVariableName
      ]
      twoVariableStore
      stateVariableName
      99
      twoVariableStore_covers

theorem updating_second_variable_preserves_coverage :
    StateStore.Covers
      [
        stateVariableName,
        secondStateVariableName
      ]
      (StateStore.update
        twoVariableStore
        secondStateVariableName
        88) := by

  exact
    StateStore.covers_update
      [
        stateVariableName,
        secondStateVariableName
      ]
      twoVariableStore
      secondStateVariableName
      88
      twoVariableStore_covers

theorem coverage_provides_second_value :
    ∃ value,
      StateStore.lookup
          twoVariableStore
          secondStateVariableName =
        some value := by

  exact
    StateStore.lookup_exists_of_covers
      twoVariableStore_covers
      (by simp)

theorem empty_store_does_not_cover_declared_variable :
    ¬ StateStore.Covers
        [stateVariableName]
        StateStore.empty := by

  intro hCovers

  rcases
      hCovers
        stateVariableName
        (by simp)
    with
      ⟨value, hLookup⟩

  have hImpossible :
      (none : Option Int) =
        some value := by
    simpa using hLookup

  cases hImpossible

end Tests
end Relico
