import Relico.Common.StateStore

set_option autoImplicit false

namespace Relico
namespace StateStore

/--
A runtime store covers a declaration list when every declared state
variable has an observable integer binding.

This predicate does not yet prohibit additional bindings. Exact store
domains will be introduced when the model syntax is generalized to
multiple declarations.
-/
def Covers
    (declaredVariables : List VarName)
    (store : StateStore) :
    Prop :=
  ∀ variableName,
    variableName ∈ declaredVariables →
    ∃ value,
      lookup store variableName =
        some value

@[simp]
theorem covers_nil
    (store : StateStore) :
    Covers [] store := by

  intro variableName hMember
  cases hMember

@[simp]
theorem covers_cons
    (declaredVariable : VarName)
    (remainingVariables : List VarName)
    (store : StateStore) :
    Covers
        (declaredVariable :: remainingVariables)
        store ↔
      (∃ value,
        lookup store declaredVariable =
          some value) ∧
      Covers remainingVariables store := by

  constructor

  · intro hCovers

    constructor

    · exact
        hCovers
          declaredVariable
          (by simp)

    · intro variableName hMember

      exact
        hCovers
          variableName
          (by simp [hMember])

  · intro hCoverage
    rcases hCoverage with
      ⟨hDeclaredVariable,
       hRemainingVariables⟩

    intro variableName hMember

    simp only [List.mem_cons] at hMember

    rcases hMember with
      hEqual | hRemaining

    · subst variableName
      exact hDeclaredVariable

    · exact
        hRemainingVariables
          variableName
          hRemaining

/--
A singleton store covers its singleton declaration list.
-/
theorem covers_singleton
    (variableName : VarName)
    (value : Int) :
    Covers
      [variableName]
      (singleton
        variableName
        value) := by

  intro referencedVariable hMember

  simp only [List.mem_singleton] at hMember
  subst referencedVariable

  exact
    ⟨value,
     lookup_singleton_eq
       variableName
       value⟩

/--
Coverage provides a concrete value for every declared variable.
-/
theorem lookup_exists_of_covers
    {declaredVariables : List VarName}
    {store : StateStore}
    (hCovers :
      Covers declaredVariables store)
    {variableName : VarName}
    (hDeclared :
      variableName ∈ declaredVariables) :
    ∃ value,
      lookup store variableName =
        some value := by

  exact
    hCovers
      variableName
      hDeclared

/--
Every declared variable is reported as present in a covering store.
-/
theorem contains_of_covers
    {declaredVariables : List VarName}
    {store : StateStore}
    (hCovers :
      Covers declaredVariables store)
    {variableName : VarName}
    (hDeclared :
      variableName ∈ declaredVariables) :
    contains store variableName =
      true := by

  rcases
      lookup_exists_of_covers
        hCovers
        hDeclared
    with
      ⟨value, hLookup⟩

  change
    (lookup
      store
      variableName).isSome =
      true

  rw [hLookup]
  rfl

/--
Updating any binding preserves coverage of all existing declarations.

For the updated variable, the new value provides the required binding.
For every distinct declared variable, the previous lookup is preserved.
-/
theorem covers_update
    (declaredVariables : List VarName)
    (store : StateStore)
    (targetVariable : VarName)
    (newValue : Int)
    (hCovers :
      Covers declaredVariables store) :
    Covers
      declaredVariables
      (update
        store
        targetVariable
        newValue) := by

  intro variableName hDeclared

  by_cases hSame :
      targetVariable = variableName

  · subst variableName

    exact
      ⟨newValue,
       lookup_update_eq
         store
         targetVariable
         newValue⟩

  · rcases
        hCovers
          variableName
          hDeclared
      with
        ⟨previousValue,
         hPreviousLookup⟩

    refine
      ⟨previousValue, ?_⟩

    rw [
      lookup_update_ne
        store
        newValue
        hSame
    ]

    exact hPreviousLookup

/--
Coverage of a larger declaration set implies coverage of every subset.
-/
theorem covers_of_subset
    {largerVariables smallerVariables : List VarName}
    {store : StateStore}
    (hCovers :
      Covers largerVariables store)
    (hSubset :
      ∀ variableName,
        variableName ∈ smallerVariables →
        variableName ∈ largerVariables) :
    Covers smallerVariables store := by

  intro variableName hMember

  exact
    hCovers
      variableName
      (hSubset
        variableName
        hMember)

end StateStore
end Relico
