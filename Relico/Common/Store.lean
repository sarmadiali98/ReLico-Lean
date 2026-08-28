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

/--
Two nested updates at distinct keys, read back through `lookup`.

The lemma the general family's `.consume` commutation runs on (decision 0042, the partial
within-tag quotient): two adjacent same-tag events targeting distinct reactors each update
one store key, and the honest statement of "the updates commute" is observational, because
`update` preserves insertion position — the store `update (update s x vx) y vy` lists `x`
before `y` while `update (update s y vy) x vx` lists them the other way round, so an
equation between the stores is false and an equation between their lookups is the theorem.
F74's shadowed-binding caveat is the same phenomenon read from the other side: `lookup`
observes one binding per key, and that is exactly the observation under which the two
orders agree.

Stated as a `lookup` characterization (a nested `if` in three branches) rather than as the
commutation directly, because the characterization is independently useful — it is how a
caller reads *any* doubly-updated store — and the commutation below is then a two-line
corollary rather than a second induction.
-/
theorem lookup_update_two_eq
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (store : Store Key Value)
    (x y : Key)
    (vx vy : Value)
    (hDistinct : x ≠ y)
    (key : Key) :
    lookup
        (update
            (update store x vx)
            y
            vy)
        key =
      if key = x then some vx
      else if key = y then some vy
      else lookup store key := by

  by_cases hKey : key = x

  · subst key

    rw [
      if_pos rfl,
      lookup_update_ne
        (update store x vx)
        vy
        (Ne.symm hDistinct),
      lookup_update_eq
    ]

  · by_cases hKeyY : key = y

    · subst key

      rw [
        if_neg hKey,
        if_pos rfl,
        lookup_update_eq
      ]

    · rw [
        if_neg hKey,
        if_neg hKeyY,
        lookup_update_ne
          (update store x vx)
          vy
          (Ne.symm hKeyY),
        lookup_update_ne
          store
          vx
          (Ne.symm hKey)
      ]

/--
Nested updates at distinct keys commute observationally: every key reads the same under
either order.

The two-line corollary of `lookup_update_two_eq`, and the precise form of the "disjoint
updates commute" fact F76 measured and decision 0042 adopts as the generating case of the
within-tag quotient. The `hDistinct` premise is load-bearing in both directions of the
characterization: with a shared key the two orders would write the same key twice and
`update_same` would make them agree at that key for the *second* value, so the lemma is
false rather than merely unprovable without it.
-/
theorem lookup_update_commute
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (store : Store Key Value)
    (x y : Key)
    (vx vy : Value)
    (hDistinct : x ≠ y)
    (key : Key) :
    lookup
        (update
            (update store x vx)
            y
            vy)
        key =
      lookup
        (update
            (update store y vy)
            x
            vx)
        key := by

  rw [
    lookup_update_two_eq
      store
      x
      y
      vx
      vy
      hDistinct
      key,
    lookup_update_two_eq
      store
      y
      x
      vy
      vx
      (Ne.symm hDistinct)
      key
  ]

  by_cases hKey : key = x <;>
    by_cases hKeyY : key = y <;>
    simp [hKey, hKeyY, hDistinct, Ne.symm hDistinct]

/--
A looked-up binding really is a binding.

Only this direction holds, and the asymmetry is the point. The store `[(key, first), (key, second)]`
contains both bindings while `lookup` observes only the first, exactly as the module note above says, so
membership is the stronger fact and this lemma is how a caller who has the weaker one obtains it.

Stated here rather than where it is used because it is a fact about `Store` and about nothing else. Its
consumer is the general correspondence relation of stage G, which quantifies its per-actor components
over membership so that a shadowed binding is constrained too — see
`Relico/DTR/GeneralRuntime.lean`'s note on attachment through membership for why a lookup-shaped
relation would be unsound there.
-/
theorem mem_of_lookup
    {Key : Type u}
    {Value : Type v}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key)
    (value : Value)
    (hLookup :
      lookup store key =
        some value) :
    (key, value) ∈ store := by

  induction store with

  | nil =>
      simp [
        lookup
      ] at hLookup

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · subst candidate

        simp [
          lookup
        ] at hLookup

        subst hLookup

        exact List.mem_cons.mpr (Or.inl rfl)

      · simp [
          lookup,
          hCandidate
        ] at hLookup

        exact
          List.mem_cons.mpr
            (Or.inr
              (inductionHypothesis
                hLookup))

end Store
end Relico
