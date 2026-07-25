set_option autoImplicit false

namespace Relico

/--
Runtime values supported by the first vertical slice.

More value forms will be added only when the supported DTR fragment expands.
-/
inductive Value where
  | int : Int → Value
deriving Repr, DecidableEq, BEq, Inhabited

namespace Value

def asInt : Value → Option Int
  | .int value => some value

@[simp]
theorem asInt_int (value : Int) :
    asInt (.int value) = some value := by
  rfl

end Value

end Relico

namespace Relico

/--
An ordered finite payload of integer values.

The current verified fragment uses empty payloads. This representation is
introduced independently so subsequent syntax and semantic checkpoints can
carry concrete message arguments without changing their order.
-/
abbrev Payload :=
  List Int

end Relico
