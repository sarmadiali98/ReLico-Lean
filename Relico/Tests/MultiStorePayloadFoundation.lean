import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadFoundation

def counterName :
    VarName :=
  ⟨"counter"⟩

def parameterName :
    VarName :=
  ⟨"amount"⟩

def highMessageName :
    MsgName :=
  ⟨"high"⟩

def lowMessageName :
    MsgName :=
  ⟨"low"⟩

def payloadExpressions :
    List DTR.MultiStorePayloadExpr :=
  [
    .stateVar counterName,
    .parameterVar parameterName,
    .intLiteral 11
  ]

/--
State, parameter, and literal payload components evaluate in source
order.
-/
theorem payload_evaluation_preserves_order :
    DTR.MultiStorePayloadExpr.evaluateAll
        [(counterName, 7)]
        [(parameterName, 3)]
        payloadExpressions =
      some [7, 3, 11] := by
  rfl

/--
Compilation preserves the exact expression-list order.
-/
theorem payload_expression_compilation_preserves_order :
    Translation.compileMultiStorePayloadExprs
        payloadExpressions =
      [
        LF.MultiStorePayloadExpr.stateVar
          counterName,
        LF.MultiStorePayloadExpr.parameterVar
          parameterName,
        LF.MultiStorePayloadExpr.intLiteral
          11
      ] := by
  rfl

/--
Zero delay remains representable and is preserved exactly by the
structural translation.
-/
theorem zero_delay_payload_send_is_preserved :
    Translation.compileMultiStorePayloadStmt
        (.selfSend
          highMessageName
          payloadExpressions
          { value := 0 }) =
      LF.MultiStorePayloadStmt.schedule
        (Translation.actionNameFor
          highMessageName)
        (Translation.compileMultiStorePayloadExprs
          payloadExpressions)
        { value := 0 } := by
  rfl

def highMessageServer :
    DTR.MultiStorePayloadMessageServer where

  name :=
    highMessageName

  parameters :=
    [parameterName]

  body :=
    [
      .assign
        counterName
        (.parameterVar parameterName)
    ]

  priority :=
    some 1

def lowMessageServer :
    DTR.MultiStorePayloadMessageServer where

  name :=
    lowMessageName

  parameters :=
    []

  body :=
    [
      .selfSend
        highMessageName
        payloadExpressions
        { value := 4 }
    ]

  priority :=
    some 4

def duplicatePriorityMessageServer :
    DTR.MultiStorePayloadMessageServer where

  name :=
    ⟨"duplicate"⟩

  parameters :=
    []

  body :=
    []

  priority :=
    some 1

/--
The selected Option-C source fragment accepts pairwise-distinct local
priorities.
-/
theorem distinct_priority_fixture_is_well_formed :
    DTR.MultiStorePayloadMessageServers.PrioritiesDistinct
      [
        lowMessageServer,
        highMessageServer
      ] := by
  decide

/--
Equal local priorities are explicitly rejected by the fragment
predicate.
-/
theorem duplicate_priority_fixture_is_rejected :
    ¬DTR.MultiStorePayloadMessageServers.PrioritiesDistinct
      [
        highMessageServer,
        duplicatePriorityMessageServer
      ] := by
  decide

/--
Smaller numeric priority is normalized before larger numeric priority.
-/
theorem priority_normalization_regression :
    DTR.MultiStorePayloadMessageServerPriority.normalize
        [
          lowMessageServer,
          highMessageServer
        ] =
      [
        highMessageServer,
        lowMessageServer
      ] := by
  rfl

/--
Formal-parameter order and priority metadata survive reaction
compilation exactly.
-/
theorem reaction_signature_and_priority_are_preserved :
    (Translation.compileMultiStorePayloadReaction
        highMessageServer).parameters =
        [parameterName] ∧
      (Translation.compileMultiStorePayloadReaction
        highMessageServer).priority =
        some 1 := by
  exact
    ⟨rfl, rfl⟩

def payloadReactiveClass :
    DTR.MultiStorePayloadReactiveClass where

  name :=
    ⟨"PayloadCounter"⟩

  stateVariables :=
    [
      {
        name :=
          counterName

        initialValue :=
          0
      }
    ]

  constructor :=
    {
      body :=
        []
    }

  messageServers :=
    [
      lowMessageServer,
      highMessageServer
    ]

/--
Generated logical actions and reactions share the same normalized
priority order.
-/
theorem reactor_action_and_reaction_order_agree :
    let compiled :=
      Translation.compileMultiStorePayloadReactor
        payloadReactiveClass

    compiled.logicalActions.map
        (fun action =>
          action.name) =
        [
          Translation.actionNameFor
            highMessageName,
          Translation.actionNameFor
            lowMessageName
        ] ∧
      compiled.messageReactions.map
          (fun reaction =>
            reaction.name) =
        [
          Translation.messageReactionNameFor
            highMessageName,
          Translation.messageReactionNameFor
            lowMessageName
        ] := by
  exact
    ⟨rfl, rfl⟩

end MultiStorePayloadFoundation
end Tests
end Relico
