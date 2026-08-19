import Relico.LF.CppPrinter
import Relico.LF.StoreCppPrinter
import Relico.LF.GeneralSyntax

set_option autoImplicit false

namespace Relico
namespace LF
namespace CppPrinter

/-!
# Printing the general generated-LF family

Layer per function, `Except String String` at every layer that can refuse, mirroring
`MultiStorePayloadCppPrinter`'s naming and its separator discipline: pieces are joined
with `String.intercalate`, never with manual `++ "\n" ++` chains, so an empty block
cannot leave a stray blank line behind.

Two things printed here are the reason the family exists: port declarations, which
precede state per Fig. 5's `{PortDecl* StateDecl* ActionDecl* ReactionDecl*}`, and
connections in `main`, which carry a delay.

`renderDelay` is deliberately **not** reused for connection delays. It produces `1ms`,
and every one of its existing call sites is *inside* a `{= … =}` block where the text is
C++ and `1ms` is a `std::chrono` literal — which says nothing about LF's own time syntax.
`renderLfTime` answers the LF question instead. Probe 10 has since measured that `0ms`,
`0 ms` and `0 msec` all compile, so the spelling was never the risk it looked like; the
separation stands for a better reason, that folding two functions answering two different
questions together would let a change to one silently retarget the other.

Two choices here are not forced by the design, and are recorded rather than buried.

The effect list is separated by `", "`, following the sibling printers and the 24
committed fixtures, where Fig. 1b writes `-> reading,sendReading` with no space. Nothing
in the target cares, and consistency inside this repo is worth more than typographic
agreement with one figure.

An input-port trigger's parameter is read as `*p.get()`, by analogy with the logical-action
read that this repo already emits and `lfc` already accepts. That analogy is **not** itself
measured: probe 10 compiled a hand-written `reaction(in) -> out`, not generated C++ that
dereferences a port. The stage that runs `lfc` over a generated port-bearing file owns
confirming it.

Nothing here sorts anything, and no `wellFormed` hypothesis is taken. Printing is total
except for the inherited multi-value-payload refusal, which well-formedness does not and
must not exclude.
-/

/--
Render a delay in LF's own time syntax, for use *outside* `{= … =}`.

Separate from `renderDelay` on purpose: see the module note.
-/
def renderLfTime
    (delay : Delay) :
    String :=
  toString delay.value ++
    " msec"

/--
Render one general expression as reactor-cpp target code.

State references and reaction-local parameter references are both ordinary C++
identifiers in the emitted body.
-/
def renderGeneralExpr :
    LF.GeneralExpr →
    String

  | .intLiteral value =>
      toString value

  | .stateVar variableName =>
      variableName.value

  | .parameterVar parameterName =>
      parameterName.value

/--
Render one general statement.

`setPort` becomes reactor-cpp's `p.set(v);`, which is what Fig. 1b's body writes.

The payload refusal is inherited verbatim from `MultiStorePayloadCppPrinter`, at the same
layer and with the same message. Stage C is representation and printing; loosening a
C++-side limit is neither.
-/
def renderGeneralStmt :
    LF.GeneralStmt →
    Except String String

  | .assign target expression =>
      .ok
        (target.value ++
          " = " ++
          renderGeneralExpr
            expression ++
          ";")

  | .schedule
      action
      payloadExpressions
      delay =>

      match payloadExpressions with

      | [] =>
          .ok
            (action.value ++
              ".schedule(" ++
              renderDelay delay ++
              ");")

      | [payloadExpression] =>
          .ok
            (action.value ++
              ".schedule(" ++
              renderGeneralExpr
                payloadExpression ++
              ", " ++
              renderDelay delay ++
              ");")

      | _ =>
          .error
            ("logical action `" ++
              action.value ++
              "` has more than one payload value; " ++
              "the current C++ printer foundation supports at most one integer payload")

  | .setPort port value =>
      .ok
        (port.value ++
          ".set(" ++
          renderGeneralExpr value ++
          ");")

/--
Collect the names a body has effects on, in first-occurrence order.

Both effect kinds are collected in **one** pass over the body, so a body that sets a port
and schedules an action lists them interleaved exactly as it produces them. Fig. 1b's
`-> reading,sendReading` matches its own body's `reading.set(0); sendReading.schedule(5ms);`
in that order, which makes the paper's example evidence for the rule rather than merely
consistent with it.

Deriving the list from the body — instead of storing an `effects` field — is what makes it
impossible to print an effect the body does not produce, or to omit one it does.
-/
def generalEffectNames
    (body : LF.GeneralBody) :
    List String :=
  body.foldl
    (fun names statement =>
      match statement with

      | .assign _ _ =>
          names

      | .schedule action _ _ =>
          if names.contains action.value then
            names
          else
            names ++
              [action.value]

      | .setPort port _ =>
          if names.contains port.value then
            names
          else
            names ++
              [port.value])
    []

/--
Render the LF effect clause, or nothing at all when there are no effects.

The empty case is measured rather than assumed: the external-send fixture prints
`reaction(in) {= … =}` with no arrow, and `lfc` accepts and runs it. It arises for a real
model whenever a message server only assigns state variables.
-/
def renderGeneralEffects
    (body : LF.GeneralBody) :
    String :=
  match generalEffectNames body with

  | [] =>
      ""

  | effectNames =>
      " -> " ++
        String.intercalate
          ", "
          effectNames

/--
Render one input-port declaration.
-/
def renderInputPortDecl
    (port : PortName) :
    String :=
  "  input " ++
    port.value ++
    ": int"

/--
Render one output-port declaration.
-/
def renderOutputPortDecl
    (port : PortName) :
    String :=
  "  output " ++
    port.value ++
    ": int"

/--
Render a reactor's port block: inputs first, then outputs.

Inputs before outputs matches Fig. 1b's `Controller` and Fig. 2b. The whole block precedes
state and actions, per `Reactor ::= reactor R (ParamList?) {PortDecl* StateDecl* ActionDecl*
ReactionDecl*}`. Existing families printed state, then action, then reactions, so this
prepends a block rather than reordering one — their output is unchanged.
-/
def renderGeneralPortDecls
    (reactor : LF.GeneralReactor) :
    String :=
  String.intercalate
    "\n"
    ((reactor.inputPorts.map
      renderInputPortDecl) ++
      (reactor.outputPorts.map
        renderOutputPortDecl))

/--
Render one logical-action declaration.

Zero formal parameters map to `void`, one to `int`. More remain representable in the
verified AST and are refused here, for the same reason as a multi-value payload.
-/
def renderGeneralActionDecl
    (action : LF.GeneralAction) :
    Except String String :=
  match action.parameters with

  | [] =>
      .ok
        ("  logical action " ++
          action.name.value ++
          ": void")

  | [_] =>
      .ok
        ("  logical action " ++
          action.name.value ++
          ": int")

  | _ =>
      .error
        ("logical action `" ++
          action.name.value ++
          "` declares more than one parameter; " ++
          "the current C++ printer foundation supports at most one integer payload")

/--
Render ordered logical-action declarations.
-/
def renderGeneralActionDecls
    (actions :
      List LF.GeneralAction) :
    Except String String := do

  let declarations ←
    actions.mapM
      renderGeneralActionDecl

  pure
    (String.intercalate
      "\n"
      declarations)

/--
Render a reaction trigger.

All three constructors are written out, so the stage that adds a fourth trigger gets a
build error here rather than a silently mis-printed reaction.
-/
def renderGeneralTrigger :
    LF.GeneralTrigger →
    String

  | .startup =>
      "startup"

  | .logicalAction action =>
      action.value

  | .inputPort port =>
      port.value

/--
Render reaction-local payload extraction.

A one-integer payload is bound to the source formal parameter name before the translated
statements run. A port is read the same way an action is, `*p.get()`; see the module note
on why that analogy is not yet measured.

Every trigger-and-arity combination is enumerated. A startup reaction with parameters is an
error rather than an ignored field, because nothing could deliver a value to it.
-/
def renderGeneralParameterRead
    (reaction :
      LF.GeneralReaction) :
    Except String String :=
  match reaction.trigger,
      reaction.parameters
  with

  | .startup, [] =>
      .ok ""

  | .startup, _ =>
      .error
        ("startup reaction `" ++
          reaction.name.value ++
          "` must not declare payload parameters")

  | .logicalAction _, [] =>
      .ok ""

  | .logicalAction action,
      [parameter] =>
      .ok
        ("    auto " ++
          parameter.value ++
          " = *" ++
          action.value ++
          ".get();")

  | .logicalAction action, _ =>
      .error
        ("reaction `" ++
          reaction.name.value ++
          "` for logical action `" ++
          action.value ++
          "` declares more than one parameter; " ++
          "the current C++ printer foundation supports at most one integer payload")

  | .inputPort _, [] =>
      .ok ""

  | .inputPort port,
      [parameter] =>
      .ok
        ("    auto " ++
          parameter.value ++
          " = *" ++
          port.value ++
          ".get();")

  | .inputPort port, _ =>
      .error
        ("reaction `" ++
          reaction.name.value ++
          "` for input port `" ++
          port.value ++
          "` declares more than one parameter; " ++
          "the current C++ printer foundation supports at most one integer payload")

/--
Render one reaction body, including trigger-payload extraction when required.
-/
def renderGeneralBody
    (reaction :
      LF.GeneralReaction) :
    Except String String := do

  let parameterRead ←
    renderGeneralParameterRead
      reaction

  let statements ←
    reaction.body.mapM
      renderGeneralStmt

  let statementLines :=
    statements.map
      (fun statement =>
        "    " ++
          statement)

  let lines :=
    if parameterRead == "" then
      statementLines
    else
      parameterRead ::
        statementLines

  pure
    (String.intercalate
      "\n"
      lines)

/--
Render one reaction.
-/
def renderGeneralReaction
    (reaction :
      LF.GeneralReaction) :
    Except String String := do

  let body ←
    renderGeneralBody
      reaction

  pure
    ("  reaction(" ++
      renderGeneralTrigger
        reaction.trigger ++
      ")" ++
      renderGeneralEffects
        reaction.body ++
      " {=\n" ++
      body ++
      "\n  =}")

/--
Render message reactions in their existing declaration order.

Order is preserved and nothing is sorted: reaction declaration order is what decides
same-tag execution order in the target, so a sort inserted here would be a silent semantic
change.
-/
def renderGeneralMessageReactions :
    List LF.GeneralReaction →
    Except String String

  | [] =>
      .ok ""

  | [reaction] =>
      renderGeneralReaction
        reaction

  | reaction :: remaining => do
      let renderedReaction ←
        renderGeneralReaction
          reaction

      let renderedRemaining ←
        renderGeneralMessageReactions
          remaining

      pure
        (renderedReaction ++
          "\n\n" ++
          renderedRemaining)

/--
Render the startup reaction, or nothing when its body is empty.

Fig. 1b's and Fig. 2b's `Controller` each have no startup reaction, and a DTR class whose
constructor neither assigns nor sends produces exactly that case. Printing
`reaction(startup) {= =}` instead has no precedent to lean on: all 24 committed
`expected/lf-source/*.lf` files have a startup reaction with a non-empty body, so the empty
one is untested territory and a stage about ports is not the place to explore it.
-/
def renderGeneralStartupReaction
    (reactor : LF.GeneralReactor) :
    Except String String :=
  match reactor.startupReaction.body with

  | [] =>
      .ok ""

  | _ :: _ =>
      renderGeneralReaction
        reactor.startupReaction

/--
Render one reactor.

Blocks are filtered for emptiness and then joined, rather than assembled by nested
`if`/`else` on which ones are present. With ports there are three declaration blocks and
two reaction blocks, so the nested form would need eight cases and would get one wrong;
this form is the same code whichever blocks happen to be empty, including all of them.
-/
def renderGeneralReactor
    (reactor : LF.GeneralReactor) :
    Except String String := do

  let actionDeclarations ←
    renderGeneralActionDecls
      reactor.logicalActions

  let startupReaction ←
    renderGeneralStartupReaction
      reactor

  let messageReactions ←
    renderGeneralMessageReactions
      reactor.messageReactions

  let portDeclarations :=
    renderGeneralPortDecls
      reactor

  let stateDeclarations :=
    renderStateVariableDecls
      reactor.stateVariables

  let declarations :=
    String.intercalate
      "\n"
      ([portDeclarations,
        stateDeclarations,
        actionDeclarations].filter
          (fun block =>
            block != ""))

  let reactions :=
    String.intercalate
      "\n\n"
      ([startupReaction,
        messageReactions].filter
          (fun block =>
            block != ""))

  let sections :=
    String.intercalate
      "\n\n"
      ([declarations,
        reactions].filter
          (fun block =>
            block != ""))

  pure
    ("reactor " ++
      reactor.name.value ++
      " {\n" ++
      sections ++
      "\n}\n")

/--
Render one instantiation.

Instantiations stay argument-free. Fig. 1b and Fig. 2b both write `new TempSensor(v=1)`,
but that is P21: the figures render DTR state variables as LF *parameters*, contradicting
Table III's `statevars ↦ state variables` row, and `ArgList ::= Expr (, Expr)*` cannot even
derive the named form `v=1`. This repo initialises state inside the reactor
(`state x: int = 0`) and instantiates with `new Controller()`. Changing that would be a
translation decision, which is a later stage's, not a printing decision, which is this one's.
-/
def renderGeneralInstance
    (reactorInstance : LF.ReactorInstance) :
    String :=
  "  " ++
    reactorInstance.name.value ++
    " = new " ++
    reactorInstance.reactorName.value ++
    "()"

/--
Render one connection.

`->` is emitted, not `→`: Fig. 5 and Fig. 1b both print the arrow as `->` in source text,
and the `→` in the grammar's metasyntax is typography.
-/
def renderGeneralConnection
    (connection : LF.GeneralConnection) :
    String :=
  "  " ++
    connection.sourceInstance.value ++
    "." ++
    connection.sourcePort.value ++
    " -> " ++
    connection.targetInstance.value ++
    "." ++
    connection.targetPort.value ++
    " after " ++
    renderLfTime
      connection.delay

/--
Render the main reactor: every instantiation, then every connection.

The main reactor stays unnamed, preserving `renderMain`'s existing documented reason, that
generated source should not depend on its own filename.
-/
def renderGeneralMain
    (program : LF.GeneralProgram) :
    String :=
  "main reactor {\n" ++
    String.intercalate
      "\n"
      ((program.instances.map
        renderGeneralInstance) ++
        (program.connections.map
          renderGeneralConnection)) ++
    "\n}"

/--
Render a complete general LF/C++ source file.
-/
def renderGeneralProgram
    (program : LF.GeneralProgram) :
    Except String String := do

  let reactors ←
    program.reactors.mapM
      renderGeneralReactor

  pure
    (targetHeader ++
      "\n\n" ++
      String.intercalate
        "\n"
        reactors ++
      "\n" ++
      renderGeneralMain
        program ++
      "\n")

@[simp]
theorem renderGeneralExpr_intLiteral
    (value : Int) :
    renderGeneralExpr
        (.intLiteral value) =
      toString value := by
  rfl

@[simp]
theorem renderGeneralExpr_stateVar
    (variableName : VarName) :
    renderGeneralExpr
        (.stateVar variableName) =
      variableName.value := by
  rfl

@[simp]
theorem renderGeneralExpr_parameterVar
    (parameterName : VarName) :
    renderGeneralExpr
        (.parameterVar parameterName) =
      parameterName.value := by
  rfl

end CppPrinter
end LF
end Relico
