import Relico.DTR.BoundPayloadSyntax
import Relico.LF.BoundPayloadSyntax
import Relico.Translation.NameGeneration
import Relico.Translation.PayloadBinding

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Compile one parameter-aware payload statement.
-/
def compileBoundPayloadStmt :
    DTR.BoundPayloadStmt →
    LF.BoundPayloadStmt

  | .selfSendInt
      messageName
      payloadExpression
      delay =>

      .scheduleInt
        (actionNameFor
          messageName)
        (compilePayloadExpr
          payloadExpression)
        delay

/--
Compile a complete parameter-aware payload body.
-/
def compileBoundPayloadBody :
    DTR.BoundPayloadBody →
    LF.BoundPayloadBody

  | [] =>
      []

  | statement :: remaining =>
      compileBoundPayloadStmt
          statement ::
        compileBoundPayloadBody
          remaining

/--
Compile a source payload message server into its generated payload
reaction.

Formal-parameter order and priority metadata are preserved exactly.
-/
def compilePayloadMessageServer
    (server : DTR.PayloadMessageServer) :
    LF.PayloadReaction := {

  logicalAction :=
    actionNameFor
      server.name

  parameters :=
    server.parameters

  body :=
    compileBoundPayloadBody
      server.body

  priority :=
    server.priority
}

@[simp]
theorem compileBoundPayloadStmt_selfSendInt
    (messageName : MsgName)
    (payloadExpression : DTR.PayloadExpr)
    (delay : Delay) :
    compileBoundPayloadStmt
        (.selfSendInt
          messageName
          payloadExpression
          delay) =
      LF.BoundPayloadStmt.scheduleInt
        (actionNameFor
          messageName)
        (compilePayloadExpr
          payloadExpression)
        delay := by
  rfl

@[simp]
theorem compileBoundPayloadBody_nil :
    compileBoundPayloadBody
        [] =
      [] := by
  rfl

@[simp]
theorem compileBoundPayloadBody_cons
    (statement : DTR.BoundPayloadStmt)
    (remaining : DTR.BoundPayloadBody) :
    compileBoundPayloadBody
        (statement :: remaining) =
      compileBoundPayloadStmt
          statement ::
        compileBoundPayloadBody
          remaining := by
  rfl

@[simp]
theorem compilePayloadMessageServer_logicalAction
    (server : DTR.PayloadMessageServer) :
    (compilePayloadMessageServer
      server).logicalAction =
      actionNameFor
        server.name := by
  rfl

@[simp]
theorem compilePayloadMessageServer_parameters
    (server : DTR.PayloadMessageServer) :
    (compilePayloadMessageServer
      server).parameters =
      server.parameters := by
  rfl

@[simp]
theorem compilePayloadMessageServer_body
    (server : DTR.PayloadMessageServer) :
    (compilePayloadMessageServer
      server).body =
      compileBoundPayloadBody
        server.body := by
  rfl

@[simp]
theorem compilePayloadMessageServer_priority
    (server : DTR.PayloadMessageServer) :
    (compilePayloadMessageServer
      server).priority =
      server.priority := by
  rfl

end Translation
end Relico
