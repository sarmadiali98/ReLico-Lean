import Relico.Common.Name
import Relico.Common.Store

set_option autoImplicit false

namespace Relico

/--
A runtime store mapping state-variable names to integer values.
-/
abbrev StateStore :=
  Store VarName Int

namespace StateStore

/--
The empty state-variable store.
-/
def empty :
    StateStore :=
  Store.empty

/--
A store containing exactly one state-variable binding.
-/
def singleton
    (name : VarName)
    (value : Int) :
    StateStore :=
  [(name, value)]

/--
Look up a state-variable value.
-/
def lookup
    (store : StateStore)
    (name : VarName) :
    Option Int :=
  Store.lookup store name

/--
Update or insert a state-variable value.
-/
def update
    (store : StateStore)
    (name : VarName)
    (value : Int) :
    StateStore :=
  Store.update store name value

/--
Test whether a state variable has a binding.
-/
def contains
    (store : StateStore)
    (name : VarName) :
    Bool :=
  Store.contains store name

@[simp]
theorem lookup_empty
    (name : VarName) :
    lookup empty name =
      none := by
  rfl

@[simp]
theorem lookup_singleton_eq
    (name : VarName)
    (value : Int) :
    lookup
        (singleton name value)
        name =
      some value := by
  simp [
    lookup,
    singleton,
    Store.lookup
  ]

theorem lookup_singleton_ne
    (name other : VarName)
    (value : Int)
    (hDifferent :
      name ≠ other) :
    lookup
        (singleton name value)
        other =
      none := by
  simp [
    lookup,
    singleton,
    Store.lookup,
    hDifferent
  ]

@[simp]
theorem lookup_update_eq
    (store : StateStore)
    (name : VarName)
    (value : Int) :
    lookup
        (update store name value)
        name =
      some value := by
  exact
    Store.lookup_update_eq
      store
      name
      value

theorem lookup_update_ne
    (store : StateStore)
    {name other : VarName}
    (value : Int)
    (hDifferent :
      name ≠ other) :
    lookup
        (update store name value)
        other =
      lookup store other := by
  exact
    Store.lookup_update_ne
      store
      value
      hDifferent

@[simp]
theorem update_same
    (store : StateStore)
    (name : VarName)
    (firstValue secondValue : Int) :
    update
        (update
          store
          name
          firstValue)
        name
        secondValue =
      update
        store
        name
        secondValue := by
  exact
    Store.update_same
      store
      name
      firstValue
      secondValue

end StateStore
end Relico
