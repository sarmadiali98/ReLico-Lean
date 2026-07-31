import Relico.Common.Name
import Relico.Common.Store

set_option autoImplicit false

namespace Relico

/--
The local name by which one actor refers to another actor.

This is intentionally distinct from `ActorName`: a known-rebec name is
relative to one sender, while an actor name identifies the receiver globally.
-/
structure KnownRebecName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

instance : ToString KnownRebecName where
  toString name :=
    name.value

namespace KnownRebecName

def isValid
    (name : KnownRebecName) :
    Prop :=
  name.value ≠ ""

end KnownRebecName

namespace Store

/--
The deterministic ordered key sequence of a finite store.
-/
def keys
    {Key : Type}
    {Value : Type}
    (store : Store Key Value) :
    List Key :=
  store.map
    Prod.fst

/--
No key occurs more than once in the ordered store representation.
-/
def KeysUnique
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (store : Store Key Value) :
    Prop :=
  (keys store).Nodup

instance keysUniqueDecidable
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (store : Store Key Value) :
    Decidable
      (KeysUnique store) := by
  unfold KeysUnique
  infer_instance

@[simp]
theorem keys_empty
    {Key : Type}
    {Value : Type} :
    keys
        (Store.empty :
          Store Key Value) =
      [] := by
  rfl

@[simp]
theorem keys_cons
    {Key : Type}
    {Value : Type}
    (key : Key)
    (value : Value)
    (remaining :
      Store Key Value) :
    keys
        ((key, value) ::
          remaining) =
      key ::
        keys remaining := by
  rfl

@[simp]
theorem keysUnique_empty
    {Key : Type}
    {Value : Type}
    [DecidableEq Key] :
    KeysUnique
        (Store.empty :
          Store Key Value) := by
  simp [
    KeysUnique,
    keys,
    Store.empty
  ]

@[simp]
theorem keysUnique_cons
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (key : Key)
    (value : Value)
    (remaining :
      Store Key Value) :
    KeysUnique
        ((key, value) ::
          remaining) ↔
      key ∉
          keys remaining ∧
        KeysUnique remaining := by
  simp [
    KeysUnique,
    keys
  ]

end Store

namespace Store

/--
Map store values while preserving every key and the deterministic key order.
-/
def mapValuesWithKey
    {Key : Type}
    {Value : Type}
    {MappedValue : Type}
    (mapValue :
      Key →
      Value →
      MappedValue) :
    Store Key Value →
    Store Key MappedValue

  | [] =>
      []

  | (key, value) ::
      remaining =>
      (
        key,
        mapValue
          key
          value
      ) ::
        mapValuesWithKey
          mapValue
          remaining

@[simp]
theorem mapValuesWithKey_nil
    {Key : Type}
    {Value : Type}
    {MappedValue : Type}
    (mapValue :
      Key →
      Value →
      MappedValue) :
    mapValuesWithKey
        mapValue
        ([] :
          Store Key Value) =
      [] := by
  rfl

@[simp]
theorem mapValuesWithKey_cons
    {Key : Type}
    {Value : Type}
    {MappedValue : Type}
    (mapValue :
      Key →
      Value →
      MappedValue)
    (key : Key)
    (value : Value)
    (remaining :
      Store Key Value) :
    mapValuesWithKey
        mapValue
        ((key, value) ::
          remaining) =
      (
        key,
        mapValue
          key
          value
      ) ::
        mapValuesWithKey
          mapValue
          remaining := by
  rfl

theorem keys_mapValuesWithKey
    {Key : Type}
    {Value : Type}
    {MappedValue : Type}
    (mapValue :
      Key →
      Value →
      MappedValue)
    (store :
      Store Key Value) :
    keys
        (mapValuesWithKey
          mapValue
          store) =
      keys store := by

  induction store with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨key, value⟩

      change
        key ::
            keys
              (mapValuesWithKey
                mapValue
                remaining) =
          key ::
            keys remaining

      exact
        congrArg
          (List.cons key)
          inductionHypothesis

theorem lookup_mapValuesWithKey
    {Key : Type}
    {Value : Type}
    {MappedValue : Type}
    [DecidableEq Key]
    (mapValue :
      Key →
      Value →
      MappedValue)
    (store :
      Store Key Value)
    (query :
      Key) :
    lookup
        (mapValuesWithKey
          mapValue
          store)
        query =
      Option.map
        (mapValue query)
        (lookup
          store
          query) := by

  induction store with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨candidate, value⟩

      by_cases hCandidate :
          candidate = query

      · subst candidate

        simp [
          mapValuesWithKey,
          lookup
        ]

      · simp [
          mapValuesWithKey,
          lookup,
          hCandidate,
          inductionHypothesis
        ]

theorem contains_mapValuesWithKey
    {Key : Type}
    {Value : Type}
    {MappedValue : Type}
    [DecidableEq Key]
    (mapValue :
      Key →
      Value →
      MappedValue)
    (store :
      Store Key Value)
    (query :
      Key) :
    contains
        (mapValuesWithKey
          mapValue
          store)
        query =
      contains
        store
        query := by

  unfold contains
  rw [
    lookup_mapValuesWithKey
  ]

  cases
      lookup
        store
        query <;>
    rfl

theorem keysUnique_mapValuesWithKey
    {Key : Type}
    {Value : Type}
    {MappedValue : Type}
    [DecidableEq Key]
    (mapValue :
      Key →
      Value →
      MappedValue)
    (store :
      Store Key Value) :
    KeysUnique
        (mapValuesWithKey
          mapValue
          store) ↔
      KeysUnique store := by

  unfold KeysUnique
  rw [
    keys_mapValuesWithKey
  ]

theorem all_keyPredicate_mapValuesWithKey
    {Key : Type}
    {Value : Type}
    {MappedValue : Type}
    (mapValue :
      Key →
      Value →
      MappedValue)
    (predicate :
      Key →
      Bool)
    (store :
      Store Key Value) :
    (mapValuesWithKey
        mapValue
        store).all
        (fun entry =>
          predicate entry.1) =
      store.all
        (fun entry =>
          predicate entry.1) := by

  induction store with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨key, value⟩

      simp [
        mapValuesWithKey,
        inductionHypothesis
      ]

/--
Zip two ordered stores only when their key sequences match exactly.
-/
def zipValuesWithKey
    {Key : Type}
    {LeftValue : Type}
    {RightValue : Type}
    {ResultValue : Type}
    [DecidableEq Key]
    (combine :
      Key →
      LeftValue →
      RightValue →
      ResultValue) :
    Store Key LeftValue →
    Store Key RightValue →
    Option
      (Store Key ResultValue)

  | [], [] =>
      some []

  | (leftKey, leftValue) ::
      leftRemaining,
    (rightKey, rightValue) ::
      rightRemaining =>

      if leftKey =
          rightKey
      then
        Option.map
          (fun remaining =>
            (
              leftKey,
              combine
                leftKey
                leftValue
                rightValue
            ) ::
              remaining)
          (zipValuesWithKey
            combine
            leftRemaining
            rightRemaining)
      else
        none

  | _, _ =>
      none

theorem keys_zipValuesWithKey_of_eq_some
    {Key : Type}
    {LeftValue : Type}
    {RightValue : Type}
    {ResultValue : Type}
    [DecidableEq Key]
    (combine :
      Key →
      LeftValue →
      RightValue →
      ResultValue)
    {left :
      Store Key LeftValue}
    {right :
      Store Key RightValue}
    {result :
      Store Key ResultValue}
    (hZip :
      zipValuesWithKey
          combine
          left
          right =
        some result) :
    keys result =
        keys left ∧
      keys result =
        keys right := by

  induction left generalizing
      right
      result with

  | nil =>
      cases right with

      | nil =>
          simp [
            zipValuesWithKey
          ] at hZip

          subst result

          constructor <;>
            rfl

      | cons rightHead rightRemaining =>
          simp [
            zipValuesWithKey
          ] at hZip

  | cons leftHead leftRemaining inductionHypothesis =>
      rcases leftHead with
        ⟨leftKey, leftValue⟩

      cases right with

      | nil =>
          simp [
            zipValuesWithKey
          ] at hZip

      | cons rightHead rightRemaining =>
          rcases rightHead with
            ⟨rightKey, rightValue⟩

          by_cases hKeys :
              leftKey = rightKey

          · subst rightKey

            cases hRemaining :
                zipValuesWithKey
                  combine
                  leftRemaining
                  rightRemaining with

            | none =>
                simp [
                  zipValuesWithKey,
                  hRemaining
                ] at hZip

            | some remainingResult =>
                simp [
                  zipValuesWithKey,
                  hRemaining
                ] at hZip

                subst result

                have hTail :=
                  inductionHypothesis
                    hRemaining

                constructor

                · change
                    leftKey ::
                        keys remainingResult =
                      leftKey ::
                        keys leftRemaining

                  exact
                    congrArg
                      (List.cons leftKey)
                      hTail.1

                · change
                    leftKey ::
                        keys remainingResult =
                      leftKey ::
                        keys rightRemaining

                  exact
                    congrArg
                      (List.cons leftKey)
                      hTail.2

          · simp [
              zipValuesWithKey,
              hKeys
            ] at hZip

end Store

/--
Ordered known-rebec bindings belonging to one sender actor.
-/
abbrev KnownRebecBindings :=
  Store KnownRebecName ActorName

/--
Ordered global topology.

Each sender actor maps its local known-rebec names to globally named
receiver actors.
-/
abbrev ActorTopology :=
  Store ActorName KnownRebecBindings

namespace ActorTopology

def empty :
    ActorTopology :=
  Store.empty

/--
Resolve one sender-relative known-rebec name.
-/
def resolve
    (topology : ActorTopology)
    (sender : ActorName)
    (knownRebec : KnownRebecName) :
    Option ActorName :=
  match
      Store.lookup
        topology
        sender
  with

  | none =>
      none

  | some bindings =>
      Store.lookup
        bindings
        knownRebec

/--
All known-rebec names are unique and all receiver actors are declared.
-/
def bindingsWellFormed
    {ActorData : Type}
    (actors :
      Store ActorName ActorData)
    (bindings :
      KnownRebecBindings) :
    Bool :=
  decide
      (Store.KeysUnique bindings) &&
    bindings.all
      (fun binding =>
        (binding.1.value != "") &&
          Store.contains
            actors
            binding.2)

/--
Finite, deterministic, domain-aligned actor topology.

The actor and topology sender sequences must be identical. This makes actor
enumeration explicit rather than quotienting by map permutation.
-/
def wellFormed
    {ActorData : Type}
    (actors :
      Store ActorName ActorData)
    (topology :
      ActorTopology) :
    Bool :=
  decide
      (Store.KeysUnique actors) &&
    decide
      (Store.KeysUnique topology) &&
    (Store.keys actors ==
      Store.keys topology) &&
    actors.all
      (fun actor =>
        actor.1.value != "") &&
    topology.all
      (fun senderBindings =>
        bindingsWellFormed
          actors
          senderBindings.2)

@[simp]
theorem resolve_empty
    (sender : ActorName)
    (knownRebec :
      KnownRebecName) :
    resolve
        empty
        sender
        knownRebec =
      none := by
  rfl

@[simp]
theorem resolve_singleton_eq
    (sender receiver :
      ActorName)
    (knownRebec :
      KnownRebecName) :
    resolve
        [
          (
            sender,
            [
              (
                knownRebec,
                receiver
              )
            ]
          )
        ]
        sender
        knownRebec =
      some receiver := by
  simp [
    resolve,
    Store.lookup
  ]

end ActorTopology

namespace ActorTopology

theorem bindingsWellFormed_mapValuesWithKey
    {ActorData : Type}
    {MappedActorData : Type}
    (mapActor :
      ActorName →
      ActorData →
      MappedActorData)
    (actors :
      Store ActorName ActorData)
    (bindings :
      KnownRebecBindings) :
    bindingsWellFormed
        (Store.mapValuesWithKey
          mapActor
          actors)
        bindings =
      bindingsWellFormed
        actors
        bindings := by

  simp [
    bindingsWellFormed,
    Store.contains_mapValuesWithKey
  ]

theorem actorNameNonemptyAll_mapValuesWithKey
    {ActorData : Type}
    {MappedActorData : Type}
    (mapActor :
      ActorName →
      ActorData →
      MappedActorData)
    (actors :
      Store ActorName ActorData) :
    List.all
        (Store.mapValuesWithKey
          mapActor
          actors)
        (fun actor =>
          actor.fst.value != "") =
      List.all
        actors
        (fun actor =>
          actor.fst.value != "") := by

  induction actors with

  | nil =>
      rfl

  | cons actor remaining inductionHypothesis =>
      rcases actor with
        ⟨actorName, actorData⟩

      simp [
        Store.mapValuesWithKey,
        inductionHypothesis
      ]

theorem wellFormed_mapValuesWithKey
    {ActorData : Type}
    {MappedActorData : Type}
    (mapActor :
      ActorName →
      ActorData →
      MappedActorData)
    (actors :
      Store ActorName ActorData)
    (topology :
      ActorTopology) :
    wellFormed
        (Store.mapValuesWithKey
          mapActor
          actors)
        topology =
      wellFormed
        actors
        topology := by

  simp [
    wellFormed,
    Store.keysUnique_mapValuesWithKey,
    Store.keys_mapValuesWithKey,
    actorNameNonemptyAll_mapValuesWithKey,
    bindingsWellFormed_mapValuesWithKey
  ]

end ActorTopology
end Relico
