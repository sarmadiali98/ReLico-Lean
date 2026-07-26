import Relico.Common.Name
import Relico.Common.Store
import Relico.Common.Value

set_option autoImplicit false

namespace Relico

/--
An activation-local store mapping formal parameter names to evaluated
integer payload values.

This is intentionally distinct from `StateStore`, which represents
persistent actor or reactor state.
-/
abbrev ParameterStore :=
  Store VarName Int

namespace ParameterStore

def empty :
    ParameterStore :=
  Store.empty

def singleton
    (parameterName : VarName)
    (value : Int) :
    ParameterStore :=
  [
    (
      parameterName,
      value
    )
  ]

def lookup
    (store : ParameterStore)
    (parameterName : VarName) :
    Option Int :=
  Store.lookup
    store
    parameterName

/--
Bind an ordered payload to an ordered formal-parameter list.

Binding succeeds exactly when the two lists have equal lengths. The
result retains declaration order and therefore preserves the positional
meaning of payload components.
-/
def bindPayload :
    List VarName →
    Payload →
    Option ParameterStore

  | [], [] =>
      some empty

  | parameterName :: remainingParameters,
      value :: remainingValues =>

      match
          bindPayload
            remainingParameters
            remainingValues
      with
      | none =>
          none

      | some remainingStore =>
          some
            ((
              parameterName,
              value
            ) :: remainingStore)

  | _, _ =>
      none

@[simp]
theorem bindPayload_nil :
    bindPayload
        []
        [] =
      some empty := by
  rfl

@[simp]
theorem bindPayload_singleton
    (parameterName : VarName)
    (value : Int) :
    bindPayload
        [
          parameterName
        ]
        [
          value
        ] =
      some
        (singleton
          parameterName
          value) := by
  rfl

@[simp]
theorem bindPayload_missing_values
    (parameterName : VarName)
    (remainingParameters : List VarName) :
    bindPayload
        (parameterName :: remainingParameters)
        [] =
      none := by
  rfl

@[simp]
theorem bindPayload_extra_values
    (value : Int)
    (remainingValues : Payload) :
    bindPayload
        []
        (value :: remainingValues) =
      none := by
  rfl

@[simp]
theorem lookup_singleton
    (parameterName : VarName)
    (value : Int) :
    lookup
        (singleton
          parameterName
          value)
        parameterName =
      some value := by

  simp [
    lookup,
    singleton,
    Store.lookup
  ]

end ParameterStore
end Relico
