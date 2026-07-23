set_option autoImplicit false

namespace Relico

universe u v

/--
A finite store represented as an ordered association list.

The first binding for a key is the observable binding. Store update
replaces that binding when present and appends a new binding otherwise.
-/
abbrev Store
    (Key : Type u)
    (Value : Type v) :=
  List (Key × Value)

namespace Store

/--
The empty finite store.
-/
def empty
    {Key : Type u}
    {Value : Type v} :
    Store Key Value :=
  []

/--
Look up the first binding for a key.
-/
def lookup
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key] :
    Store Key Value →
    Key →
    Option Value

  | [], _ =>
      none

  | (candidate, value) :: remaining, key =>
      if candidate = key then
        some value
      else
        lookup remaining key

/--
Update the first binding for a key.

When the key is absent, append a new binding at the end.
-/
def update
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key] :
    Store Key Value →
    Key →
    Value →
    Store Key Value

  | [], key, value =>
      [(key, value)]

  | (candidate, currentValue) :: remaining,
      key,
      value =>

      if candidate = key then
        (candidate, value) :: remaining
      else
        (candidate, currentValue) ::
          update remaining key value

/--
Test whether a key has a binding.
-/
def contains
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key) :
    Bool :=
  (lookup store key).isSome

@[simp]
theorem lookup_empty
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (key : Key) :
    lookup
        (empty : Store Key Value)
        key =
      none := by
  rfl

/--
Looking up a key immediately after updating it returns the new value.
-/
@[simp]
theorem lookup_update_eq
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key)
    (value : Value) :
    lookup
        (update store key value)
        key =
      some value := by

  induction store with

  | nil =>
      simp [
        update,
        lookup
      ]

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · subst candidate

        simp [
          update,
          lookup
        ]

      · simp [
          update,
          lookup,
          hCandidate,
          inductionHypothesis
        ]

/--
Updating one key does not change the value observed at a distinct key.
-/
theorem lookup_update_ne
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (store : Store Key Value)
    {key other : Key}
    (value : Value)
    (hDifferent :
      key ≠ other) :
    lookup
        (update store key value)
        other =
      lookup store other := by

  induction store with

  | nil =>
      simp [
        update,
        lookup,
        hDifferent
      ]

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidateKey :
          candidate = key

      · subst candidate

        simp [
          update,
          lookup,
          hDifferent
        ]

      · by_cases hCandidateOther :
            candidate = other

        · subst candidate

          simp [
            update,
            lookup,
            hCandidateKey
          ]

        · simp [
            update,
            lookup,
            hCandidateKey,
            hCandidateOther,
            inductionHypothesis
          ]

/--
Two consecutive updates of the same key retain only the second value.
-/
@[simp]
theorem update_same
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key)
    (firstValue secondValue : Value) :
    update
        (update store key firstValue)
        key
        secondValue =
      update store key secondValue := by

  induction store with

  | nil =>
      simp [update]

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · subst candidate

        simp [update]

      · simp [
          update,
          hCandidate,
          inductionHypothesis
        ]

@[simp]
theorem contains_update_eq
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key)
    (value : Value) :
    contains
        (update store key value)
        key =
      true := by

  unfold contains
  rw [lookup_update_eq]
  rfl

end Store
end Relico
