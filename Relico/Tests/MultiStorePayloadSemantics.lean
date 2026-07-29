import Relico.Correctness.MultiStorePayloadStatementCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadSemantics

def xName :
    VarName :=
  ⟨"x"⟩

def yName :
    VarName :=
  ⟨"y"⟩

def parameterName :
    VarName :=
  ⟨"amount"⟩

def missingName :
    VarName :=
  ⟨"missing"⟩

def messageName :
    MsgName :=
  ⟨"deliver"⟩

def sourceStateStore :
    StateStore :=
  [
    (xName, 7),
    (yName, 2)
  ]

def activationParameters :
    ParameterStore :=
  [
    (parameterName, 3)
  ]

def payloadExpressions :
    List DTR.MultiStorePayloadExpr :=
  [
    .stateVar xName,
    .parameterVar parameterName,
    .intLiteral 11
  ]

def compiledPayloadExpressions :
    List LF.MultiStorePayloadExpr :=
  Translation.compileMultiStorePayloadExprs
    payloadExpressions

def sourceState
    (body :
      DTR.MultiStorePayloadBody) :
    DTR.MultiStorePayloadState where

  currentTime :=
    10

  stateStore :=
    sourceStateStore

  parameters :=
    activationParameters

  pendingMessages :=
    []

  activeBody :=
    body

def targetState
    (body :
      LF.MultiStorePayloadBody) :
    LF.MultiStorePayloadState where

  currentTag :=
    {
      time := 10
      microstep := 4
    }

  stateStore :=
    sourceStateStore

  parameters :=
    activationParameters

  pendingActions :=
    []

  activeBody :=
    body

/--
Three distinguishable source arguments retain their exact order.
-/
theorem source_payload_order :
    DTR.MultiStorePayloadExpr.evaluateAll
        sourceStateStore
        activationParameters
        payloadExpressions =
      some [7, 3, 11] := by
  rfl

/--
The generated expression list produces the same ordered payload.
-/
theorem target_payload_order :
    LF.MultiStorePayloadExpr.evaluateAll
        sourceStateStore
        activationParameters
        compiledPayloadExpressions =
      some [7, 3, 11] := by
  rfl

/--
Persistent state and activation-local parameters are read from
different stores.
-/
theorem state_and_parameter_lookup :
    DTR.MultiStorePayloadExpr.evaluate
        sourceStateStore
        activationParameters
        (.stateVar xName) =
        some 7 ∧
      DTR.MultiStorePayloadExpr.evaluate
        sourceStateStore
        activationParameters
        (.parameterVar parameterName) =
        some 3 := by
  exact
    ⟨rfl, rfl⟩

/--
A missing source lookup blocks evaluation.
-/
theorem source_missing_lookup :
    DTR.MultiStorePayloadExpr.evaluate
        sourceStateStore
        activationParameters
        (.stateVar missingName) =
      none := by
  rfl

/--
The corresponding generated lookup also fails.
-/
theorem target_missing_lookup :
    LF.MultiStorePayloadExpr.evaluate
        sourceStateStore
        activationParameters
        (.stateVar missingName) =
      none := by
  rfl

def sourceFailedAssignment :
    DTR.MultiStorePayloadState :=
  sourceState
    [
      .assign
        yName
        (.stateVar missingName)
    ]

def targetFailedAssignment :
    LF.MultiStorePayloadState :=
  targetState
    [
      .assign
        yName
        (.stateVar missingName)
    ]

/--
A failed source lookup produces no transition.
-/
theorem source_failed_assignment_blocks :
    DTR.MultiStorePayloadState.step?
        sourceFailedAssignment =
      none := by
  rfl

/--
The compiled target assignment blocks for the same lookup failure.
-/
theorem target_failed_assignment_blocks :
    LF.MultiStorePayloadState.step?
        targetFailedAssignment =
      none := by
  rfl

def sourceAssignmentBefore :
    DTR.MultiStorePayloadState :=
  sourceState
    [
      .assign
        yName
        (.stateVar xName)
    ]

def sourceAssignmentAfter :
    DTR.MultiStorePayloadState :=
  DTR.MultiStorePayloadState.assignmentResult
    sourceAssignmentBefore
    yName
    7
    []

/--
The source assignment executes using the evaluated value.
-/
theorem source_assignment_step :
    DTR.MultiStorePayloadState.step?
        sourceAssignmentBefore =
      some sourceAssignmentAfter := by
  rfl

/--
Assignment updates the selected variable and leaves the other binding
observable with its previous value.
-/
theorem assignment_updates_only_selected_variable :
    StateStore.lookup
        sourceAssignmentAfter.stateStore
        yName =
        some 7 ∧
      StateStore.lookup
        sourceAssignmentAfter.stateStore
        xName =
        some 7 := by
  exact
    ⟨rfl, rfl⟩

def sourceZeroBody :
    DTR.MultiStorePayloadBody :=
  [
    .selfSend
      messageName
      payloadExpressions
      { value := 0 }
  ]

def targetZeroBody :
    LF.MultiStorePayloadBody :=
  Translation.compileMultiStorePayloadBody
    sourceZeroBody

def sourceZeroBefore :
    DTR.MultiStorePayloadState :=
  sourceState
    sourceZeroBody

def targetZeroBefore :
    LF.MultiStorePayloadState :=
  targetState
    targetZeroBody

def sourceZeroAfter :
    DTR.MultiStorePayloadState :=
  DTR.MultiStorePayloadState.selfSendResult
    sourceZeroBefore
    messageName
    [7, 3, 11]
    { value := 0 }
    []

def targetZeroAfter :
    LF.MultiStorePayloadState :=
  LF.MultiStorePayloadState.scheduleResult
    targetZeroBefore
    (Translation.actionNameFor
      messageName)
    [7, 3, 11]
    { value := 0 }
    []

/--
The source zero-delay self-send creates one same-time occurrence.
-/
theorem source_zero_delay_step :
    DTR.MultiStorePayloadState.step?
        sourceZeroBefore =
      some sourceZeroAfter := by
  rfl

/--
The target zero-delay schedule creates one next-microstep occurrence.
-/
theorem target_zero_delay_step :
    LF.MultiStorePayloadState.step?
        targetZeroBefore =
      some targetZeroAfter := by
  rfl

/--
Zero delay preserves metric time while LF advances the microstep.
-/
theorem zero_delay_timing :
    sourceZeroAfter.pendingMessages =
        [
          {
            name := messageName
            arrivalTime := 10
            payload := [7, 3, 11]
          }
        ] ∧
      targetZeroAfter.pendingActions =
        [
          {
            name :=
              Translation.actionNameFor
                messageName

            tag :=
              {
                time := 10
                microstep := 5
              }

            payload :=
              [7, 3, 11]
          }
        ] := by
  exact
    ⟨rfl, rfl⟩

def sourcePositiveBody :
    DTR.MultiStorePayloadBody :=
  [
    .selfSend
      messageName
      payloadExpressions
      { value := 4 }
  ]

def targetPositiveBody :
    LF.MultiStorePayloadBody :=
  Translation.compileMultiStorePayloadBody
    sourcePositiveBody

def sourcePositiveBefore :
    DTR.MultiStorePayloadState :=
  sourceState
    sourcePositiveBody

def targetPositiveBefore :
    LF.MultiStorePayloadState :=
  targetState
    targetPositiveBody

def sourcePositiveAfter :
    DTR.MultiStorePayloadState :=
  DTR.MultiStorePayloadState.selfSendResult
    sourcePositiveBefore
    messageName
    [7, 3, 11]
    { value := 4 }
    []

def targetPositiveAfter :
    LF.MultiStorePayloadState :=
  LF.MultiStorePayloadState.scheduleResult
    targetPositiveBefore
    (Translation.actionNameFor
      messageName)
    [7, 3, 11]
    { value := 4 }
    []

/--
Positive delay advances source and target metric time by the same
amount and resets the target microstep to zero.
-/
theorem positive_delay_timing :
    sourcePositiveAfter.pendingMessages =
        [
          {
            name := messageName
            arrivalTime := 14
            payload := [7, 3, 11]
          }
        ] ∧
      targetPositiveAfter.pendingActions =
        [
          {
            name :=
              Translation.actionNameFor
                messageName

            tag :=
              {
                time := 14
                microstep := 0
              }

            payload :=
              [7, 3, 11]
          }
        ] := by
  exact
    ⟨rfl, rfl⟩

def duplicateSourceStatement :
    DTR.MultiStorePayloadStmt :=
  .selfSend
    messageName
    [.intLiteral 1]
    { value := 0 }

def duplicateSourceStart :
    DTR.MultiStorePayloadState :=
  sourceState
    [
      duplicateSourceStatement,
      duplicateSourceStatement
    ]

def duplicateSourceAfterOne :
    DTR.MultiStorePayloadState :=
  DTR.MultiStorePayloadState.selfSendResult
    duplicateSourceStart
    messageName
    [1]
    { value := 0 }
    [duplicateSourceStatement]

def duplicateSourceAfterTwo :
    DTR.MultiStorePayloadState :=
  DTR.MultiStorePayloadState.selfSendResult
    duplicateSourceAfterOne
    messageName
    [1]
    { value := 0 }
    []

/--
Two equal source sends execute as two separate transitions.
-/
theorem duplicate_source_steps :
    DTR.MultiStorePayloadState.step?
        duplicateSourceStart =
        some duplicateSourceAfterOne ∧
      DTR.MultiStorePayloadState.step?
        duplicateSourceAfterOne =
        some duplicateSourceAfterTwo := by
  exact
    ⟨rfl, rfl⟩

/--
Two equal sends remain two pending occurrences.
-/
theorem duplicate_source_multiplicity :
    duplicateSourceAfterTwo.pendingMessages =
      [
        {
          name := messageName
          arrivalTime := 10
          payload := [1]
        },
        {
          name := messageName
          arrivalTime := 10
          payload := [1]
        }
      ] := by
  rfl

def duplicateTargetStatement :
    LF.MultiStorePayloadStmt :=
  Translation.compileMultiStorePayloadStmt
    duplicateSourceStatement

def duplicateTargetStart :
    LF.MultiStorePayloadState :=
  targetState
    [
      duplicateTargetStatement,
      duplicateTargetStatement
    ]

def duplicateTargetAfterOne :
    LF.MultiStorePayloadState :=
  LF.MultiStorePayloadState.scheduleResult
    duplicateTargetStart
    (Translation.actionNameFor
      messageName)
    [1]
    { value := 0 }
    [duplicateTargetStatement]

def duplicateTargetAfterTwo :
    LF.MultiStorePayloadState :=
  LF.MultiStorePayloadState.scheduleResult
    duplicateTargetAfterOne
    (Translation.actionNameFor
      messageName)
    [1]
    { value := 0 }
    []

/--
The generated semantics also retains both equal action occurrences.
-/
theorem duplicate_target_multiplicity :
    LF.MultiStorePayloadState.step?
        duplicateTargetStart =
        some duplicateTargetAfterOne ∧
      LF.MultiStorePayloadState.step?
        duplicateTargetAfterOne =
        some duplicateTargetAfterTwo ∧
      duplicateTargetAfterTwo.pendingActions.length =
        2 := by
  exact
    ⟨rfl, rfl, rfl⟩

def distinctPayloadStart :
    DTR.MultiStorePayloadState :=
  sourceState
    [
      .selfSend
        messageName
        [.intLiteral 1]
        { value := 0 },

      .selfSend
        messageName
        [.intLiteral 2]
        { value := 0 }
    ]

def distinctPayloadAfterOne :
    DTR.MultiStorePayloadState :=
  DTR.MultiStorePayloadState.selfSendResult
    distinctPayloadStart
    messageName
    [1]
    { value := 0 }
    [
      .selfSend
        messageName
        [.intLiteral 2]
        { value := 0 }
    ]

def distinctPayloadAfterTwo :
    DTR.MultiStorePayloadState :=
  DTR.MultiStorePayloadState.selfSendResult
    distinctPayloadAfterOne
    messageName
    [2]
    { value := 0 }
    []

/--
Occurrences with different payloads remain distinguishable.
-/
theorem distinct_payloads_remain_distinct :
    DTR.MultiStorePayloadState.step?
        distinctPayloadStart =
        some distinctPayloadAfterOne ∧
      DTR.MultiStorePayloadState.step?
        distinctPayloadAfterOne =
        some distinctPayloadAfterTwo ∧
      distinctPayloadAfterTwo.pendingMessages.map
          (fun pending =>
            pending.payload) =
        [[1], [2]] := by
  exact
    ⟨rfl, rfl, rfl⟩

/--
The general expression correspondence theorem applies to the concrete
three-component payload.
-/
theorem compiled_evaluation_agrees :
    LF.MultiStorePayloadExpr.evaluateAll
        sourceStateStore
        activationParameters
        compiledPayloadExpressions =
      DTR.MultiStorePayloadExpr.evaluateAll
        sourceStateStore
        activationParameters
        payloadExpressions := by
  exact
    Correctness.compileMultiStorePayloadExprs_evaluateAll
      sourceStateStore
      activationParameters
      payloadExpressions

/--
The pre-states for the zero-delay example satisfy exact local runtime
correspondence.
-/
theorem zero_before_corresponds :
    Correctness.MultiStorePayloadStateCorresponds
      sourceZeroBefore
      targetZeroBefore := by

  exact {
    currentTime :=
      rfl

    stateStore :=
      rfl

    parameters :=
      rfl

    pendingQueues :=
      Correctness.PayloadQueueCorresponds.nil

    activeBody :=
      rfl
  }

/--
The compiled zero-delay statement executes with exactly the source
payload and preserves state correspondence.
-/
theorem translated_zero_send_forward :
    DTR.MultiStorePayloadStep
        sourceZeroBefore
        sourceZeroAfter ∧
      LF.MultiStorePayloadStep
        targetZeroBefore
        targetZeroAfter ∧
      Correctness.MultiStorePayloadStateCorresponds
        sourceZeroAfter
        targetZeroAfter := by

  exact
    Correctness.multiStorePayload_selfSend_forward
      zero_before_corresponds
      rfl
      rfl

/--
The resulting selected occurrences carry identical ordered payloads.
-/
theorem translated_zero_send_exact_payload :
    sourceZeroAfter.pendingMessages.map
        (fun pending =>
          pending.payload) =
        [[7, 3, 11]] ∧
      targetZeroAfter.pendingActions.map
        (fun pending =>
          pending.payload) =
        [[7, 3, 11]] := by
  exact
    ⟨rfl, rfl⟩

end MultiStorePayloadSemantics
end Tests
end Relico
