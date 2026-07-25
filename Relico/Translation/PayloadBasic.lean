import Relico.DTR.PayloadSyntax
import Relico.LF.PayloadSyntax
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Compile the additive one-integer source payload statement into the
corresponding typed LF scheduling statement.
-/
def compilePayloadStmt :
    DTR.PayloadStmt →
    LF.PayloadStmt

  | .selfSendInt
      messageName
      payloadExpression
      delay =>

      .scheduleInt
        (actionNameFor
          messageName)
        (compileExpr
          payloadExpression)
        delay

def compilePayloadBody
    (body : DTR.PayloadBody) :
    LF.PayloadBody :=
  body.map
    compilePayloadStmt

@[simp]
theorem compilePayloadStmt_selfSendInt
    (messageName : MsgName)
    (payloadExpression : DTR.Expr)
    (delay : Delay) :
    compilePayloadStmt
        (.selfSendInt
          messageName
          payloadExpression
          delay) =
      .scheduleInt
        (actionNameFor
          messageName)
        (compileExpr
          payloadExpression)
        delay := by
  rfl

end Translation
end Relico
