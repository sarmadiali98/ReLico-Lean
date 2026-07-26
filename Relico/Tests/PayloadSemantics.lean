import Relico.Correctness.PayloadStep

set_option autoImplicit false

namespace Relico
namespace Tests

def payloadSemanticsVariable :
    VarName :=
  ⟨"x"⟩

def payloadSemanticsMessage :
    MsgName :=
  ⟨"deliver"⟩

def payloadSemanticsAction :
    ActionName :=
  Translation.actionNameFor
    payloadSemanticsMessage

def payloadSemanticsDelay :
    Delay :=
  { value := 2 }

def payloadSemanticsCurrentTag :
    LF.Tag where

  time :=
    3

  microstep :=
    0

def payloadSemanticsSourceBefore :
    DTR.PayloadState where

  currentTime :=
    3

  stateValue :=
    42

  pendingMessages :=
    []

  activeBody := [
    DTR.PayloadStmt.selfSendInt
      payloadSemanticsMessage
      (.stateVar
        payloadSemanticsVariable)
      payloadSemanticsDelay
  ]

def payloadSemanticsSourceLabel :
    DTR.PayloadLabel :=
  .sendInt
    payloadSemanticsMessage
    (LogicalTime.after
      3
      payloadSemanticsDelay)
    42

def payloadSemanticsSourceAfter :
    DTR.PayloadState where

  currentTime :=
    3

  stateValue :=
    42

  pendingMessages := [
    DTR.PendingMessage.scheduleWithPayload
      3
      payloadSemanticsMessage
      [
        42
      ]
      payloadSemanticsDelay
  ]

  activeBody :=
    []

def payloadSemanticsTargetBefore :
    LF.PayloadState where

  currentTag :=
    payloadSemanticsCurrentTag

  stateValue :=
    42

  pendingActions :=
    []

  activeBody := [
    LF.PayloadStmt.scheduleInt
      payloadSemanticsAction
      (.stateVar
        payloadSemanticsVariable)
      payloadSemanticsDelay
  ]

def payloadSemanticsTargetLabel :
    LF.PayloadLabel :=
  .scheduleInt
    payloadSemanticsAction
    (LF.Tag.schedule
      payloadSemanticsCurrentTag
      payloadSemanticsDelay)
    42

def payloadSemanticsTargetAfter :
    LF.PayloadState where

  currentTag :=
    payloadSemanticsCurrentTag

  stateValue :=
    42

  pendingActions := [
    LF.PendingAction.scheduleWithPayload
      payloadSemanticsCurrentTag
      payloadSemanticsAction
      [
        42
      ]
      payloadSemanticsDelay
  ]

  activeBody :=
    []

theorem payload_semantics_before_corresponds :
    Correctness.PayloadStateCorresponds
      payloadSemanticsSourceBefore
      payloadSemanticsTargetBefore := by

  exact {
    currentTime :=
      rfl

    stateValue :=
      rfl

    pendingEvents :=
      Correctness.payloadQueueCorresponds_nil

    activeBody :=
      rfl
  }

theorem payload_semantics_source_step :
    DTR.PayloadStep
      payloadSemanticsMessage
      payloadSemanticsSourceBefore
      payloadSemanticsSourceLabel
      payloadSemanticsSourceAfter := by

  exact
    DTR.PayloadStep.selfSendInt
      (declaredMessageServer :=
        payloadSemanticsMessage)
      (currentTime :=
        3)
      (stateValue :=
        42)
      (pendingMessages :=
        [])
      (targetMessage :=
        payloadSemanticsMessage)
      (payloadExpression :=
        .stateVar
          payloadSemanticsVariable)
      (delay :=
        payloadSemanticsDelay)
      (evaluatedValue :=
        42)
      (remaining :=
        [])
      rfl
      rfl

theorem payload_semantics_target_step :
    LF.PayloadStep
      payloadSemanticsAction
      payloadSemanticsTargetBefore
      payloadSemanticsTargetLabel
      payloadSemanticsTargetAfter := by

  exact
    LF.PayloadStep.scheduleInt
      (declaredAction :=
        payloadSemanticsAction)
      (currentTag :=
        payloadSemanticsCurrentTag)
      (stateValue :=
        42)
      (pendingActions :=
        [])
      (targetAction :=
        payloadSemanticsAction)
      (payloadExpression :=
        .stateVar
          payloadSemanticsVariable)
      (delay :=
        payloadSemanticsDelay)
      (evaluatedValue :=
        42)
      (remaining :=
        [])
      rfl
      rfl

theorem payload_semantics_label_corresponds :
    Correctness.PayloadLabelCorresponds
      payloadSemanticsSourceLabel
      payloadSemanticsTargetLabel := by

  unfold
    Correctness.PayloadLabelCorresponds

  exact
    ⟨rfl,
     rfl,
     rfl⟩

theorem payload_semantics_after_corresponds :
    Correctness.PayloadStateCorresponds
      payloadSemanticsSourceAfter
      payloadSemanticsTargetAfter := by

  refine {
    currentTime :=
      rfl

    stateValue :=
      rfl

    pendingEvents :=
      ?_

    activeBody :=
      rfl
  }

  exact
    Correctness.payloadQueueCorresponds_append_scheduleWithPayload
      Correctness.payloadQueueCorresponds_nil
      3
      payloadSemanticsCurrentTag
      payloadSemanticsMessage
      [
        42
      ]
      payloadSemanticsDelay
      rfl

theorem payload_semantics_forward_exists :
    ∃ targetLabel targetAfter,
      LF.PayloadStep
          payloadSemanticsAction
          payloadSemanticsTargetBefore
          targetLabel
          targetAfter ∧
        Correctness.PayloadLabelCorresponds
          payloadSemanticsSourceLabel
          targetLabel ∧
        Correctness.PayloadStateCorresponds
          payloadSemanticsSourceAfter
          targetAfter := by

  exact
    Correctness.payloadStep_forward
      payload_semantics_before_corresponds
      payload_semantics_source_step

theorem payload_semantics_source_queue_exact :
    payloadSemanticsSourceAfter.pendingMessages =
      [
        DTR.PendingMessage.scheduleWithPayload
          3
          payloadSemanticsMessage
          [
            42
          ]
          payloadSemanticsDelay
      ] := by
  rfl

theorem payload_semantics_target_queue_exact :
    payloadSemanticsTargetAfter.pendingActions =
      [
        LF.PendingAction.scheduleWithPayload
          payloadSemanticsCurrentTag
          payloadSemanticsAction
          [
            42
          ]
          payloadSemanticsDelay
      ] := by
  rfl

end Tests
end Relico
