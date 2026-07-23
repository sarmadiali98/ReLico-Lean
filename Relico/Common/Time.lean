set_option autoImplicit false

namespace Relico

/--
Logical time used by the initial DTR and generated-LF semantics.

The first vertical slice uses natural-number time.
-/
abbrev LogicalTime := Nat

/--
A nonnegative logical delay.
-/
structure Delay where
  value : Nat
deriving Repr, DecidableEq, BEq, Inhabited

namespace LogicalTime

def after (time : LogicalTime) (delay : Delay) : LogicalTime :=
  time + delay.value

@[simp]
theorem after_zero (time : LogicalTime) :
    after time { value := 0 } = time := by
  rfl

@[simp]
theorem after_value (time : LogicalTime) (delay : Delay) :
    after time delay = time + delay.value := by
  rfl

theorem le_after (time : LogicalTime) (delay : Delay) :
    time ≤ after time delay := by
  unfold after
  exact Nat.le_add_right time delay.value

end LogicalTime

end Relico
