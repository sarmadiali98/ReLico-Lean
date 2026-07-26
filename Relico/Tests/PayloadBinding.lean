import Relico.Translation.PayloadBinding

set_option autoImplicit false

namespace Relico
namespace Tests

def firstPayloadParameter :
    VarName :=
  ⟨"first"⟩

def secondPayloadParameter :
    VarName :=
  ⟨"second"⟩

def payloadParameterStore :
    ParameterStore :=
  [
    (
      firstPayloadParameter,
      7
    ),
    (
      secondPayloadParameter,
      11
    )
  ]

theorem ordered_payload_binding_exact :
    ParameterStore.bindPayload
        [
          firstPayloadParameter,
          secondPayloadParameter
        ]
        [
          7,
          11
        ] =
      some payloadParameterStore := by
  rfl

theorem ordered_payload_binding_first_lookup :
    ParameterStore.lookup
        payloadParameterStore
        firstPayloadParameter =
      some 7 := by

  simp [
    payloadParameterStore,
    firstPayloadParameter,
    secondPayloadParameter,
    ParameterStore.lookup,
    Store.lookup
  ]

theorem ordered_payload_binding_second_lookup :
    ParameterStore.lookup
        payloadParameterStore
        secondPayloadParameter =
      some 11 := by

  simp [
    payloadParameterStore,
    firstPayloadParameter,
    secondPayloadParameter,
    ParameterStore.lookup,
    Store.lookup
  ]

theorem ordered_payload_binding_rejects_missing_value :
    ParameterStore.bindPayload
        [
          firstPayloadParameter,
          secondPayloadParameter
        ]
        [
          7
        ] =
      none := by
  rfl

theorem ordered_payload_binding_rejects_extra_value :
    ParameterStore.bindPayload
        [
          firstPayloadParameter
        ]
        [
          7,
          11
        ] =
      none := by
  rfl

def sourceBoundParameterExpression :
    DTR.PayloadExpr :=
  .parameterVar
    firstPayloadParameter

def targetBoundParameterExpression :
    LF.PayloadExpr :=
  Translation.compilePayloadExpr
    sourceBoundParameterExpression

theorem source_bound_parameter_evaluates :
    DTR.PayloadExpr.evaluate
        42
        payloadParameterStore
        sourceBoundParameterExpression =
      some 7 := by

  simp [
    sourceBoundParameterExpression,
    payloadParameterStore,
    firstPayloadParameter,
    secondPayloadParameter,
    DTR.PayloadExpr.evaluate,
    ParameterStore.lookup,
    Store.lookup
  ]

theorem target_bound_parameter_evaluates :
    LF.PayloadExpr.evaluate
        42
        payloadParameterStore
        targetBoundParameterExpression =
      some 7 := by

  simp [
    targetBoundParameterExpression,
    sourceBoundParameterExpression,
    Translation.compilePayloadExpr,
    payloadParameterStore,
    firstPayloadParameter,
    secondPayloadParameter,
    LF.PayloadExpr.evaluate,
    ParameterStore.lookup,
    Store.lookup
  ]

theorem translated_payload_parameter_evaluation_preserved :
    LF.PayloadExpr.evaluate
        42
        payloadParameterStore
        targetBoundParameterExpression =
      DTR.PayloadExpr.evaluate
        42
        payloadParameterStore
        sourceBoundParameterExpression := by

  exact
    Translation.compilePayloadExpr_preserves_evaluation
      sourceBoundParameterExpression
      42
      payloadParameterStore

def sourcePayloadStateExpression :
    DTR.PayloadExpr :=
  .stateVar
    ⟨"x"⟩

theorem payload_state_expression_evaluates :
    DTR.PayloadExpr.evaluate
        42
        payloadParameterStore
        sourcePayloadStateExpression =
      some 42 := by
  rfl

theorem existing_expression_embedding_preserved :
    Translation.compilePayloadExpr
        (DTR.PayloadExpr.ofExpr
          (.intLiteral 13)) =
      LF.PayloadExpr.ofExpr
        (Translation.compileExpr
          (.intLiteral 13)) := by

  exact
    Translation.compilePayloadExpr_ofExpr
      (.intLiteral 13)

end Tests
end Relico
