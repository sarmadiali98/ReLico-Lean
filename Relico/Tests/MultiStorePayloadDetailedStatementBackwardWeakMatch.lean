import Relico.Correctness.MultiStorePayloadDetailedStatementBackwardWeakMatch

set_option autoImplicit false

#check
  Relico.Correctness.compileMultiStorePayloadBody_cons_invert

#check
  Relico.Correctness.compileMultiStorePayloadBody_assign_head

#check
  Relico.Correctness.compileMultiStorePayloadBody_schedule_head

#check
  Relico.Correctness.multiStorePayload_statement_backward_runtime

#check
  Relico.Correctness.multiStorePayloadDetailedRuntime_statement_backward_weak

#print axioms
  Relico.Correctness.compileMultiStorePayloadBody_cons_invert

#print axioms
  Relico.Correctness.compileMultiStorePayloadBody_assign_head

#print axioms
  Relico.Correctness.compileMultiStorePayloadBody_schedule_head

#print axioms
  Relico.Correctness.multiStorePayload_statement_backward_runtime

#print axioms
  Relico.Correctness.multiStorePayloadDetailedRuntime_statement_backward_weak
