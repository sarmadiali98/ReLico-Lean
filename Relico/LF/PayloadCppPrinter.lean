import Relico.LF.CppPrinter
import Relico.LF.PayloadSyntax

set_option autoImplicit false

namespace Relico
namespace LF
namespace CppPrinter

/--
Render a typed integer logical-action declaration.
-/
def renderIntLogicalActionDecl
    (actionName : ActionName) :
    String :=
  "  logical action " ++
    actionName.value ++
    ": int"

/--
Render one integer-payload scheduling statement.

The reactor-cpp API expects the payload before the delay.
-/
def renderPayloadStmt :
    LF.PayloadStmt →
    String

  | .scheduleInt
      actionName
      payloadExpression
      delay =>

      actionName.value ++
        ".schedule(" ++
        renderExpr payloadExpression ++
        ", " ++
        renderDelay delay ++
        ");"

/--
Render the reactor-cpp expression that reads the current typed logical
action payload.
-/
def renderIntPayloadRead
    (actionName : ActionName) :
    String :=
  "*" ++
    actionName.value ++
    ".get()"

/--
A concrete executable LF/C++ program for the first one-integer payload
vertical slice.
-/
structure IntPayloadProgram where

  reactorName :
    ReactorName

  stateVariable :
    VarName

  logicalAction :
    ActionName

  initialPayload :
    LF.Expr

  delay :
    Delay

  reactorInstance :
    LF.ReactorInstance

deriving Repr, DecidableEq, BEq, Inhabited

/--
Render a complete standalone LF/C++ program containing:

* one integer reactor-state variable;
* one integer logical action;
* startup scheduling with a concrete translated payload expression;
* one triggered reaction that reads the action payload.
-/
def renderIntPayloadProgram
    (program : IntPayloadProgram) :
    String :=

  targetHeader ++
    "\n\n" ++

    "reactor " ++
    program.reactorName.value ++
    " {\n" ++

    "  state " ++
    program.stateVariable.value ++
    ": int = 0\n" ++

    renderIntLogicalActionDecl
      program.logicalAction ++
    "\n\n" ++

    "  reaction(startup) -> " ++
    program.logicalAction.value ++
    " {=\n" ++

    "    " ++
    renderPayloadStmt
      (.scheduleInt
        program.logicalAction
        program.initialPayload
        program.delay) ++
    "\n" ++

    "  =}\n\n" ++

    "  reaction(" ++
    program.logicalAction.value ++
    ") {=\n" ++

    "    " ++
    program.stateVariable.value ++
    " = " ++
    renderIntPayloadRead
      program.logicalAction ++
    ";\n" ++

    "  =}\n" ++
    "}\n\n" ++

    renderMain
      program.reactorInstance ++
    "\n"

@[simp]
theorem renderPayloadStmt_scheduleInt
    (actionName : ActionName)
    (payloadExpression : LF.Expr)
    (delay : Delay) :
    renderPayloadStmt
        (.scheduleInt
          actionName
          payloadExpression
          delay) =
      actionName.value ++
        ".schedule(" ++
        renderExpr payloadExpression ++
        ", " ++
        renderDelay delay ++
        ");" := by
  rfl

end CppPrinter
end LF
end Relico
