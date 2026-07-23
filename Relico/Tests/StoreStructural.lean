import Relico.Correctness.StoreStructural
import Relico.Tests.StoreSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

/--
The cross-variable source body is structurally valid for two declared
state variables.
-/
theorem dtr_crossVariable_body_storeWellFormed :
    DTR.Body.StoreWellFormed
      [
        stateVariableName,
        secondStateVariableName
      ]
      storeRuntimeMessageName
      dtrStoreAssignmentBefore.activeBody := by

  simp [
    DTR.Body.StoreWellFormed,
    DTR.Stmt.StoreWellFormed,
    DTR.Expr.StoreWellFormed,
    dtrStoreAssignmentBefore
  ]

/--
The executable compiler preserves structural validity of the
cross-variable body.
-/
theorem compiled_crossVariable_body_storeWellFormed :
    LF.Body.StoreWellFormed
      [
        stateVariableName,
        secondStateVariableName
      ]
      (Translation.actionNameFor
        storeRuntimeMessageName)
      (Translation.compileBody
        dtrStoreAssignmentBefore.activeBody) := by

  exact
    Correctness.compileBody_storeWellFormed
      dtr_crossVariable_body_storeWellFormed

/--
Coverage and structural well-formedness ensure that the source
cross-variable expression has a concrete runtime value.
-/
theorem crossVariable_expression_is_defined :
    ∃ value,
      DTR.Expr.evaluateStore
          twoVariableStore
          (.stateVar
            stateVariableName) =
        some value := by

  apply
    DTR.Expr.evaluateStore_defined
      (declaredVariables := [
        stateVariableName,
        secondStateVariableName
      ])

  · simp [
      DTR.Expr.StoreWellFormed
    ]

  · exact
      twoVariableStore_covers

/--
The singleton declaration-list predicate remains equivalent to the
original v0 predicate.
-/
example :
    DTR.Expr.StoreWellFormed
        [stateVariableName]
        (.stateVar stateVariableName) ↔
      DTR.Expr.WellFormed
        stateVariableName
        (.stateVar stateVariableName) := by

  exact
    DTR.Expr.storeWellFormed_singleton_iff
      stateVariableName
      (.stateVar stateVariableName)

end Tests
end Relico
