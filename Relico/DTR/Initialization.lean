import Relico.DTR.RuntimeWellFormed

set_option autoImplicit false

namespace Relico
namespace DTR

/--
The DTR runtime state at constructor entry.

The initial integer value is explicit because vertical slice v0 has not
yet fixed a source-language default initialization convention.
-/
def initialState
    (model : DTR.Model)
    (initialValue : Int) :
    DTR.State where
  currentTime := 0
  stateValue := initialValue
  pendingMessages := []
  activeBody :=
    model.reactiveClass.constructor.body

/--
A well-formed model produces a well-formed constructor-entry state.
-/
theorem initialState_wellFormed
    (model : DTR.Model)
    (initialValue : Int)
    (hModel :
      DTR.Model.WellFormed model) :
    DTR.State.WellFormed
      model
      (initialState model initialValue) := by
  refine {
    activeBodyWellFormed :=
      hModel.constructorBodyWellFormed
    pendingMessagesWellFormed := ?_
  }

  intro pendingMessage hMembership
  simp [initialState] at hMembership

end DTR
end Relico
