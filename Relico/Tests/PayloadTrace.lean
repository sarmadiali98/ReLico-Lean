import Relico.Correctness.PayloadTrace
import Relico.Tests.PayloadSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

def payloadSourceTraceLabels :
    List DTR.PayloadLabel :=
  [
    payloadSemanticsSourceLabel
  ]

def payloadTargetTraceLabels :
    List LF.PayloadLabel :=
  [
    payloadSemanticsTargetLabel
  ]

theorem payload_source_finite_execution :
    DTR.PayloadSteps
      payloadSemanticsMessage
      payloadSemanticsSourceBefore
      payloadSourceTraceLabels
      payloadSemanticsSourceAfter := by

  simpa [
    payloadSourceTraceLabels
  ] using
    DTR.PayloadSteps.cons
      payload_semantics_source_step
      (DTR.PayloadSteps.refl
        payloadSemanticsSourceAfter)

theorem payload_target_finite_execution :
    LF.PayloadSteps
      payloadSemanticsAction
      payloadSemanticsTargetBefore
      payloadTargetTraceLabels
      payloadSemanticsTargetAfter := by

  simpa [
    payloadTargetTraceLabels
  ] using
    LF.PayloadSteps.cons
      payload_semantics_target_step
      (LF.PayloadSteps.refl
        payloadSemanticsTargetAfter)

theorem payload_concrete_trace_corresponds :
    Correctness.PayloadTraceCorresponds
      payloadSourceTraceLabels
      payloadTargetTraceLabels := by

  simpa [
    payloadSourceTraceLabels,
    payloadTargetTraceLabels
  ] using
    Correctness.PayloadTraceCorresponds.cons
      payload_semantics_label_corresponds
      Correctness.PayloadTraceCorresponds.nil

theorem payload_concrete_trace_lengths_equal :
    payloadSourceTraceLabels.length =
      payloadTargetTraceLabels.length := by

  exact
    Correctness.PayloadTraceCorresponds.length_eq
      payload_concrete_trace_corresponds

theorem payload_trace_forward_exists :
    ∃ targetLabels targetAfter,
      LF.PayloadSteps
          payloadSemanticsAction
          payloadSemanticsTargetBefore
          targetLabels
          targetAfter ∧
        Correctness.PayloadTraceCorresponds
          payloadSourceTraceLabels
          targetLabels ∧
        Correctness.PayloadStateCorresponds
          payloadSemanticsSourceAfter
          targetAfter := by

  exact
    Correctness.payloadSteps_forward
      payload_source_finite_execution
      payload_semantics_before_corresponds

theorem payload_trace_backward_exists :
    ∃ sourceLabels sourceAfter,
      DTR.PayloadSteps
          payloadSemanticsMessage
          payloadSemanticsSourceBefore
          sourceLabels
          sourceAfter ∧
        Correctness.PayloadTraceCorresponds
          sourceLabels
          payloadTargetTraceLabels ∧
        Correctness.PayloadStateCorresponds
          sourceAfter
          payloadSemanticsTargetAfter ∧
        DTR.PayloadBody.WellFormed
          payloadSemanticsMessage
          sourceAfter.activeBody := by

  exact
    Correctness.payloadSteps_backward
      payload_target_finite_execution
      payload_semantics_before_corresponds
      payload_semantics_source_body_well_formed

theorem payload_source_finite_execution_preserves_well_formedness :
    DTR.PayloadBody.WellFormed
      payloadSemanticsMessage
      payloadSemanticsSourceAfter.activeBody := by

  exact
    DTR.payloadSteps_preserve_bodyWellFormed
      payload_source_finite_execution
      payload_semantics_source_body_well_formed

end Tests
end Relico
