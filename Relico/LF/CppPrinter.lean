import Relico.LF.Syntax

set_option autoImplicit false

namespace Relico
namespace LF
namespace CppPrinter

/--
The concrete Lingua Franca target emitted by ReLico v0.
-/
def targetHeader : String :=
  "target Cpp"

/--
Render an LF expression as C++ target code.
-/
def renderExpr :
    LF.Expr → String
  | .intLiteral value =>
      toString value
  | .stateVar variableName =>
      variableName.value

/--
Render a v0 delay as a C++ chrono millisecond literal.

The concrete backend interprets each `Delay.value` unit as one
millisecond.
-/
def renderDelay
    (delay : Delay) :
    String :=
  toString delay.value ++ "ms"

/--
Render one generated LF statement inside a C++ reaction body.
-/
def renderStmt :
    LF.Stmt → String
  | .assign target expression =>
      target.value ++
        " = " ++
        renderExpr expression ++
        ";"

  | .schedule action delay =>
      action.value ++
        ".schedule(" ++
        renderDelay delay ++
        ");"

/--
Render a reaction trigger.
-/
def renderTrigger :
    LF.Trigger → String
  | .startup =>
      "startup"
  | .logicalAction action =>
      action.value

/--
Render the statements inside a reaction code block.
-/
def renderBody
    (body : LF.Body) :
    String :=
  String.intercalate
    "\n"
    (body.map
      (fun statement =>
        "    " ++ renderStmt statement))

/--
Render one generated reaction using LF target-code delimiters.
-/
def renderReaction
    (reaction : LF.Reaction) :
    String :=
  "  reaction(" ++
    renderTrigger reaction.trigger ++
    ") {=\n" ++
    renderBody reaction.body ++
    "\n  =}"

/--
Render the generated reactor.

The single integer state variable receives a concrete C++ initial value
of zero. The generated startup reaction performs the translated source
constructor initialization.
-/
def renderReactor
    (reactor : LF.Reactor) :
    String :=
  "reactor " ++ reactor.name.value ++ " {\n" ++
    "  state " ++ reactor.stateVar.value ++
    ": int = 0\n" ++
    "  logical action " ++
    reactor.logicalAction.value ++
    ": void\n\n" ++
    renderReaction reactor.startupReaction ++
    "\n\n" ++
    renderReaction reactor.messageReaction ++
    "\n}"

/--
Render the top-level LF main reactor and its generated instance.
-/
def renderMain
    (reactorInstance : LF.ReactorInstance) :
    String :=
  "main reactor Main {\n" ++
    "  " ++ reactorInstance.name.value ++
    " = new " ++
    reactorInstance.reactorName.value ++
    "()\n" ++
    "}"

/--
Render a complete LF/C++ source file.
-/
def renderProgram
    (program : LF.Program) :
    String :=
  targetHeader ++
    "\n\n" ++
    renderReactor program.reactor ++
    "\n\n" ++
    renderMain program.reactorInstance ++
    "\n"

@[simp]
theorem targetHeader_is_cpp :
    targetHeader = "target Cpp" := by
  rfl

end CppPrinter
end LF
end Relico
