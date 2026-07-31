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
end Relico
