import Relico.DTR.BoundPayloadSyntax

set_option autoImplicit false

namespace Relico

namespace DTR
namespace BoundPayloadStmt

/--
Positive-delay timing restriction for parameter-aware self-sends.

The restriction removes the source/target scheduler mismatch caused by DTR
logical-time ties and LF microstep refinement.
-/
def PriorityTimingWellFormed :
    DTR.BoundPayloadStmt →
    Prop

  | .selfSendInt
      _targetMessage
      _payloadExpression
      delay =>
        0 < delay.value

@[simp]
theorem priorityTimingWellFormed_selfSendInt
    (targetMessage : MsgName)
    (payloadExpression : DTR.PayloadExpr)
    (delay : Delay) :
    PriorityTimingWellFormed
        (.selfSendInt
          targetMessage
          payloadExpression
          delay) ↔
      0 < delay.value := by

  rfl

end BoundPayloadStmt

namespace BoundPayloadBody

/--
Every parameter-aware self-send in a source body has strictly positive delay.
-/
def PriorityTimingWellFormed :
    DTR.BoundPayloadBody →
    Prop

  | [] =>
      True

  | statement :: remaining =>
      DTR.BoundPayloadStmt.PriorityTimingWellFormed
          statement ∧
        PriorityTimingWellFormed
          remaining

@[simp]
theorem priorityTimingWellFormed_nil :
    PriorityTimingWellFormed
      ([] : DTR.BoundPayloadBody) := by

  trivial

@[simp]
theorem priorityTimingWellFormed_cons
    (statement : DTR.BoundPayloadStmt)
    (remaining : DTR.BoundPayloadBody) :
    PriorityTimingWellFormed
        (statement :: remaining) ↔
      DTR.BoundPayloadStmt.PriorityTimingWellFormed
          statement ∧
        PriorityTimingWellFormed
          remaining := by

  rfl

theorem priorityTimingWellFormed_head
    {statement : DTR.BoundPayloadStmt}
    {remaining : DTR.BoundPayloadBody}
    (hTiming :
      PriorityTimingWellFormed
        (statement :: remaining)) :
    DTR.BoundPayloadStmt.PriorityTimingWellFormed
      statement := by

  exact hTiming.1

theorem priorityTimingWellFormed_tail
    {statement : DTR.BoundPayloadStmt}
    {remaining : DTR.BoundPayloadBody}
    (hTiming :
      PriorityTimingWellFormed
        (statement :: remaining)) :
    PriorityTimingWellFormed
      remaining := by

  exact hTiming.2

end BoundPayloadBody
end DTR

end Relico
