import Relico.LF.CppPrinter
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

Nothing here sorts anything, and no `wellFormed` hypothesis is taken.

Printing is **no longer** refused for a multi-value payload. Stage C's three sites said
*"the current C++ printer foundation supports at most one integer payload"*, which read
as a report about the target and was a statement about this file; real `lfc 0.11.0`
compiled and ran a struct-carrying action payload, so the limit was ours. Finding F23.

Two refusals remain, and each is worth distinguishing because a refusal nobody can
trigger is as bad as a missing one.

An instance whose reactor does not resolve, or whose argument count disagrees with that
reactor's parameter list, is refused rather than truncated. A `zip` here would silently
drop surplus arguments and emit a program that compiles and is wrong, which is the worst
outcome available. `GeneralProgram.instanceArgumentsMatch` excludes both conditions, so
for a well-formed program this refusal is unreachable — which is the point of having
written the predicate rather than trusting the printer.

A startup reaction's parameters are **no longer** refused, and that change is a defect
stage D found in this printer rather than a choice it made. Stage C refused them because
nothing can deliver a value to a startup reaction, which is true of a *payload* and false
of what stage D puts in that list: `assembleGeneralStartupReaction` sets the startup
reaction's parameters to the constructor's formals, deliberately, so that
`GeneralReactor.exprWellFormed` resolves `.parameterVar` inside a constructor body — and
that is pinned, not read off, by
`Translation.compileGeneralReactiveClass_startupParameters`. Those names are the
*reactor's* parameters, and a reactor parameter is readable in a reaction body with no
binder and no trigger at all (measured, `docs/STAGE_D_DESIGN.md` §5.5), so the right
emission is the empty string and not a diagnostic. Left as it was, the arm would have
refused `frontend/fixtures/general/constructor-arguments.rebeca` — a committed positive
fixture of this very family — for no reason but that its constructor has a parameter list
*and* a body. Finding F33.

An input-port trigger with two or more parameters is refused, and this one is a genuine
disagreement with `docs/STAGE_D_DESIGN.md` §6, which said all three parameter-read
refusals go. It is wrong on this one. A `GeneralPortDecl` carries a single declared type
and therefore delivers exactly one value, so there is no struct to name and no second
value to bind — unlike an action, whose own parameter list supplies both. The design
sentence generalized from the action case; the type says otherwise and the type wins.
Filed as F30. Stage D emits no ports at all, so the arm is unreachable either way, and
stage E owns whatever a multi-parameter arrival should mean.
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
Render a declared type in LF's own spelling.

The **sole** owner of the two emitted strings. Stage C hardwired `": int"` at three
separate sites, which made the type of every port and every payload a fact about this
file rather than about the program; stage D's widening would have added a fourth such
site instead of removing three. `LF.GeneralType.int` is spelled `int` and
`LF.GeneralType.boolean` is spelled `bool` — the Lean-side name and the target-side
spelling differ for `boolean`, which is exactly why one function should know it.

Both spellings are measured under real `lfc 0.11.0`, in port, state and action-payload
position.
-/
def renderGeneralType :
    LF.GeneralType →
    String

  | .int =>
      "int"

  | .boolean =>
      "bool"

/--
Render a value as target-language text.

`true` and `false` rather than `1` and `0`: the emitted text sits in LF type positions
and in C++ initializers, and a `bool` parameter given `1` would compile while saying
something the source did not.
-/
def renderGeneralValue :
    LF.GeneralValue →
    String

  | .int value =>
      toString value

  | .bool true =>
      "true"

  | .bool false =>
      "false"

/--
Render the initial value a declaration of a type starts at.

A thin composition, named so that the state declaration and the reactor parameter list
cannot disagree about what `int` starts at. `GeneralType.initialValue` fixes the value
and this fixes its spelling; neither the declaration sites nor a future reader has to
know both.
-/
def renderGeneralInitialValue
    (declaredType : LF.GeneralType) :
    String :=
  renderGeneralValue
    (LF.GeneralType.initialValue
      declaredType)

/--
Render a binary operator.

C++'s spellings, one per constructor, written out rather than grouped, so that the stage
which adds a fourteenth operator gets a build error here. Every one of these appears
inside a `{= … =}` block where the text is verbatim C++, so the spellings are guaranteed
by the C++ standard rather than by anything about LF — which is why none of them needed a
probe.
-/
def renderGeneralBinaryOp :
    LF.GeneralBinaryOp →
    String

  | .add =>
      "+"

  | .sub =>
      "-"

  | .mul =>
      "*"

  | .div =>
      "/"

  | .mod =>
      "%"

  | .eq =>
      "=="

  | .ne =>
      "!="

  | .lt =>
      "<"

  | .le =>
      "<="

  | .gt =>
      ">"

  | .ge =>
      ">="

  | .logicalAnd =>
      "&&"

  | .logicalOr =>
      "||"

/--
Render a unary operator.

No trailing space is emitted and none is wanted: `-x` and `!flag` are the C++ forms, and
`- x` would be legal but would put a space where the source has none.
-/
def renderGeneralUnaryOp :
    LF.GeneralUnaryOp →
    String

  | .negate =>
      "-"

  | .logicalNot =>
      "!"

/--
Render one general expression as reactor-cpp target code.

State references and reaction-local parameter references are both ordinary C++
identifiers in the emitted body. A reactor parameter is read the same way, with no
declaration and no trigger, which is measured.

**Every operator application is fully parenthesized**, and the redundant parentheses are
the point. A printer that emitted bare infix would be asserting that its own precedence
and associativity agree with C++'s, and this development has verified no such table. The
committed fixture `accumulator = left + right * 2 - 1;` is exactly the expression that
punishes a wrong assertion, and it prints here as
`((left + (right * 2)) - 1)` — uglier, and correct without an argument. Only operator
*applications* get parentheses; a literal or an identifier is already atomic, so wrapping
it would add noise without removing an assumption.

Total: it returns `String`, not `Except String String`. No expression is unprintable,
and that is what the widening was for.
-/
def renderGeneralExpr :
    LF.GeneralExpr →
    String

  | .intLiteral value =>
      toString value

  | .boolLiteral value =>
      renderGeneralValue
        (.bool value)

  | .stateVar variableName =>
      variableName.value

  | .parameterVar parameterName =>
      parameterName.value

  | .binary operator left right =>
      "(" ++
        renderGeneralExpr
          left ++
        " " ++
        renderGeneralBinaryOp
          operator ++
        " " ++
        renderGeneralExpr
          right ++
        ")"

  | .unary operator operand =>
      "(" ++
        renderGeneralUnaryOp
          operator ++
        renderGeneralExpr
          operand ++
        ")"

/--
The C++ name of the struct that carries one action's payload.

`<ReactorName>_<ActionName>_Args`. The **single** owner of this spelling: the preamble
declares the struct, the action declaration names it as its type, a `schedule` constructs
it and a reaction body destructures it, so four sites agree by construction rather than
by four string literals agreeing by luck.

This naming rule has **no paper basis** — the paper supplies none here, exactly as it
supplies none for port names (ledger P20). It is this project's choice, recorded as
finding F25 rather than presented as inherited.

The reactor name is part of it because an action name is unique only within its reactor,
and a program-level preamble is one C++ scope: two classes with a `logic` message server
of arity two would otherwise declare `logic_Args` twice.
-/
def generalPayloadStructName
    (reactorName : ReactorName)
    (action : ActionName) :
    String :=
  reactorName.value ++
    "_" ++
    action.value ++
    "_Args"

/--
Render one general statement.

`setPort` becomes reactor-cpp's `p.set(v);`, which is what Fig. 1b's body writes.

**Total as of stage D.** The arity-≥2 arm used to be `.error "… at most one integer
payload"`; it now constructs the payload struct, `<Struct>{<e1>, <e2>, …}`, in the form
measured under real `lfc`: `argsAction.schedule(Args2{1, 2, true}, 0ms);`.

`reactorName` is here only to name that struct, and passing the name rather than the whole
reactor is deliberate — it states the entire dependency. The name is the *declaring*
reactor's, which is the same reactor as the scheduling one: `stmtWellFormed` requires a
scheduled action to be declared on the reactor whose body schedules it, and stage D emits
self-sends only.
-/
def renderGeneralStmt
    (reactorName : ReactorName) :
    LF.GeneralStmt →
    String

  | .assign target expression =>
      target.value ++
        " = " ++
        renderGeneralExpr
          expression ++
        ";"

  | .schedule
      action
      payloadExpressions
      delay =>

      match payloadExpressions with

      | [] =>
          action.value ++
            ".schedule(" ++
            renderDelay delay ++
            ");"

      | [payloadExpression] =>
          action.value ++
            ".schedule(" ++
            renderGeneralExpr
              payloadExpression ++
            ", " ++
            renderDelay delay ++
            ");"

      | first :: second :: remaining =>
          action.value ++
            ".schedule(" ++
            generalPayloadStructName
              reactorName
              action ++
            "{" ++
            String.intercalate
              ", "
              ((first :: second :: remaining).map
                renderGeneralExpr) ++
            "}, " ++
            renderDelay delay ++
            ");"

  | .setPort port value =>
      port.value ++
        ".set(" ++
        renderGeneralExpr value ++
        ");"

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
    (port : LF.GeneralPortDecl) :
    String :=
  "  input " ++
    port.name.value ++
    ": " ++
    renderGeneralType
      port.declaredType

/--
Render one output-port declaration.
-/
def renderOutputPortDecl
    (port : LF.GeneralPortDecl) :
    String :=
  "  output " ++
    port.name.value ++
    ": " ++
    renderGeneralType
      port.declaredType

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
Render one state-variable declaration.

New in stage D rather than a reuse of `renderStateVariableDecl`, and the reason is in the
type: the inherited `LF.StateVariableDecl` carries `initialValue : Int` and no type at
all, so a `boolean` state variable was untranslatable at the level of its own
*declaration* — its initial value is `false`, which has no `Int` counterpart. The
inherited function is left untouched for the integer-only families that use it.

The initial value is **derived** from the declared type, so `state flag: bool = 0` is not
merely unemitted but unstateable. `state x: int = 0` is byte-identical to what stage C
printed.
-/
def renderGeneralStateVariableDecl
    (declaration : LF.GeneralStateVariableDecl) :
    String :=
  "  state " ++
    declaration.name.value ++
    ": " ++
    renderGeneralType
      declaration.declaredType ++
    " = " ++
    renderGeneralInitialValue
      declaration.declaredType

/--
Render ordered state-variable declarations.
-/
def renderGeneralStateVariableDecls
    (declarations :
      List LF.GeneralStateVariableDecl) :
    String :=
  String.intercalate
    "\n"
    (declarations.map
      renderGeneralStateVariableDecl)

/--
Render one logical-action declaration.

Arity 0 is `: void` and arity 1 is the parameter's own declared type, both unchanged in
bytes from the fixtures for the cases they already covered. Arity ≥ 2 is the payload
struct, which is where stage C refused.
-/
def renderGeneralActionDecl
    (reactorName : ReactorName)
    (action : LF.GeneralAction) :
    String :=
  "  logical action " ++
    action.name.value ++
    ": " ++
    (match action.parameters with

      | [] =>
          "void"

      | [parameter] =>
          renderGeneralType
            parameter.declaredType

      | _ :: _ :: _ =>
          generalPayloadStructName
            reactorName
            action.name)

/--
Render ordered logical-action declarations.
-/
def renderGeneralActionDecls
    (reactorName : ReactorName)
    (actions :
      List LF.GeneralAction) :
    String :=
  String.intercalate
    "\n"
    (actions.map
      (renderGeneralActionDecl
        reactorName))

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
The C++ local that a multi-value payload is bound to before its fields are destructured.

`<action>_payload`. Derived from the action name rather than fixed, and the reason is a
recorded exposure rather than a preference: this identifier shares a scope with the
source-derived parameter binders below it, and nothing proves a source model has no
message-server parameter called `arithmetic_payload`. The inherited payload family emits a
bare `auto payload = …`, so the exposure is not introduced here, and deriving from the
action name narrows a collision to a source identifier that mentions an action name.

Fixing it properly means a freshness condition over the union of all source identifiers in
a reactor, which is a well-formedness obligation and does not belong inside a printer. It
is filed as F29 rather than patched here.

One function so that the binding site and every field read cannot disagree.
-/
def generalPayloadBinderName
    (action : ActionName) :
    String :=
  action.value ++
    "_payload"

/--
Render reaction-local payload extraction.

A single-value payload is bound to the source formal parameter name before the translated
statements run. A multi-value payload is bound once as a struct and then destructured, one
`auto` per parameter, in the form measured under real `lfc`:

```
    auto arithmetic_action_payload = *arithmetic_action.get();
    auto left = arithmetic_action_payload.left;
    auto right = arithmetic_action_payload.right;
```

One binder per parameter, named from the source, so the body below refers to a payload
component by the identifier the source used and the translation of expressions needs no
renaming pass. The struct's own name is never mentioned — `auto` infers it — which is why
this function needs no reactor name.

A port is read the same way an action is, `*p.get()`; see the module note on why that
analogy is not yet measured.

Every trigger-and-arity combination is enumerated, with one exception that is deliberate
rather than economical: a startup reaction emits no read **at any arity**, so its two
arities are one arm. Stage C had the second arity as an error, on the ground that nothing
can deliver a value to a startup reaction. That ground is sound about a payload and wrong
about what stage D puts in the list — `assembleGeneralStartupReaction` fills it with the
constructor's formals, which are the *reactor's* parameters and are readable in a reaction
body with no binder at all. Emitting nothing is therefore the whole job here. See the
module note and finding F33; the arms are not collapsed by a wildcard, so the stage that
adds a fourth trigger still gets a build error.

An input port with two or more parameters is an error because a `GeneralPortDecl` declares
one type and so delivers one value: unlike an action, it carries no parameter list to
destructure. Unreachable in stage D, which emits no ports.
-/
def renderGeneralParameterRead
    (reaction :
      LF.GeneralReaction) :
    Except String String :=
  match reaction.trigger,
      reaction.parameters
  with

  | .startup, _ =>
      .ok ""

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

  | .logicalAction action,
      first :: second :: remaining =>
      .ok
        (String.intercalate
          "\n"
          (("    auto " ++
            generalPayloadBinderName
              action ++
            " = *" ++
            action.value ++
            ".get();") ::
            ((first :: second :: remaining).map
              (fun parameter =>
                "    auto " ++
                  parameter.value ++
                  " = " ++
                  generalPayloadBinderName
                    action ++
                  "." ++
                  parameter.value ++
                  ";"))))

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

  | .inputPort port,
      _ :: _ :: _ =>
      .error
        ("reaction `" ++
          reaction.name.value ++
          "` for input port `" ++
          port.value ++
          "` declares more than one parameter; " ++
          "a port declares one type and so carries one value, " ++
          "and unlike a logical action it has no parameter list to destructure")

/--
Render one reaction body, including trigger-payload extraction when required.

`reactorName` is threaded only so that a `schedule` of a multi-value payload can name its
struct.
-/
def renderGeneralBody
    (reactorName : ReactorName)
    (reaction :
      LF.GeneralReaction) :
    Except String String := do

  let parameterRead ←
    renderGeneralParameterRead
      reaction

  let statements :=
    reaction.body.map
      (renderGeneralStmt
        reactorName)

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
    (reactorName : ReactorName)
    (reaction :
      LF.GeneralReaction) :
    Except String String := do

  let body ←
    renderGeneralBody
      reactorName
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
def renderGeneralMessageReactions
    (reactorName : ReactorName) :
    List LF.GeneralReaction →
    Except String String

  | [] =>
      .ok ""

  | [reaction] =>
      renderGeneralReaction
        reactorName
        reaction

  | reaction :: remaining => do
      let renderedReaction ←
        renderGeneralReaction
          reactorName
          reaction

      let renderedRemaining ←
        renderGeneralMessageReactions
          reactorName
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
        reactor.name
        reactor.startupReaction

/--
Render one reactor parameter, with its default.

Every parameter carries a default and it is always `GeneralType.initialValue` of the
parameter's type, so the declaration never has to consult the instance list, and a
parameter without a default — which would make an argumentless instantiation illegal — is
not representable. Measured form: `reactor Configured(bound: int = 0, active: bool =
false)`.
-/
def renderGeneralParameterDecl
    (parameter : LF.GeneralTypedParameter) :
    String :=
  parameter.name.value ++
    ": " ++
    renderGeneralType
      parameter.declaredType ++
    " = " ++
    renderGeneralInitialValue
      parameter.declaredType

/--
Render a reactor's parameter list, or nothing at all when it has none.

The empty case emits the empty string rather than `()`, which keeps every existing
parameterless fixture reactor byte-identical. Fig. 5 spells the production
`reactor R (ParamList?)`, so the absent form is the grammar's own.

Takes the list rather than the reactor, which is the whole dependency and also makes the
byte-identity claim provable by `rfl` — see `renderGeneralParameterList_nil` — instead of
by a rewrite under a hypothesis.
-/
def renderGeneralParameterList :
    List LF.GeneralTypedParameter →
    String

  | [] =>
      ""

  | first :: remaining =>
      "(" ++
        String.intercalate
          ", "
          ((first :: remaining).map
            renderGeneralParameterDecl) ++
        ")"

/--
Render one reactor.

Blocks are filtered for emptiness and then joined, rather than assembled by nested
`if`/`else` on which ones are present. With ports there are three declaration blocks and
two reaction blocks, so the nested form would need eight cases and would get one wrong;
this form is the same code whichever blocks happen to be empty, including all of them.

The reactor's own name is passed down to every reaction, where it is needed to name a
multi-value payload struct.
-/
def renderGeneralReactor
    (reactor : LF.GeneralReactor) :
    Except String String := do

  let startupReaction ←
    renderGeneralStartupReaction
      reactor

  let messageReactions ←
    renderGeneralMessageReactions
      reactor.name
      reactor.messageReactions

  let actionDeclarations :=
    renderGeneralActionDecls
      reactor.name
      reactor.logicalActions

  let portDeclarations :=
    renderGeneralPortDecls
      reactor

  let stateDeclarations :=
    renderGeneralStateVariableDecls
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
      renderGeneralParameterList
        reactor.parameters ++
      " {\n" ++
      sections ++
      "\n}\n")

/--
Pair positional arguments with the names their reactor declares, or fail.

`Option` rather than `Except` so that the caller, which knows the instance name, writes the
diagnostic; this recursion knows only two lists and could not say which instance went
wrong.

Count agreement and rendering are **one** recursion, which is what makes truncation
unrepresentable. `List.zip` is the tempting alternative and is the reason this function
exists: it silently drops the surplus, so an instance supplying three arguments to a
two-parameter reactor would emit a program that compiles and is wrong. Refusing is the only
safe answer available to a printer.

Types are deliberately **not** checked here. `GeneralProgram.instanceArgumentsMatch` checks
them, and a printer that re-derived the judgement would be a second source of truth that
can disagree with the first.
-/
def renderGeneralArguments :
    List LF.GeneralValue →
    List LF.GeneralTypedParameter →
    Option (List String)

  | [], [] =>
      some []

  | value :: remainingValues,
      parameter :: remainingParameters =>

      match renderGeneralArguments
        remainingValues
        remainingParameters
      with

      | none =>
          none

      | some remaining =>
          some
            ((parameter.name.value ++
              "=" ++
              renderGeneralValue
                value) ::
              remaining)

  | _, _ =>
      none

/--
Render one instantiation.

Arguments are named, not positional, and the names come from the reactor's own parameter
list: `configuredOn = new Configured(bound=7, active=true)`, which is the measured form.
An argumentless instance prints `new Controller()` exactly as stage C did, so every
existing fixture is byte-identical.

The instance carries its arguments **positionally** while the emitted LF is named, and
recovering the names from the single authoritative list is what makes a name disagreement
unrepresentable rather than merely unchecked.

This is the one printer site whose lookup can fail, and it refuses rather than truncates —
see the module note. `program.reactor?` is used rather than a local search over
`program.reactors` on purpose: it is the same lookup `GeneralProgram.instanceArgumentsMatch`
performs, so "well-formed" and "printable" cannot come apart through two lookups
disagreeing.

The old docstring here recorded that instantiations *stay* argument-free, on the grounds
that Fig. 1b's `new TempSensor(v=1)` is P21 — the figures render DTR **state variables** as
LF parameters, contradicting Table III's `statevars ↦ state variables` row. That reading of
P21 stands and this change does not weaken it: state variables are still initialised inside
the reactor, and what lands in an argument list here is a *constructor parameter*, which is
a different source construct that Fig. 5's own `ParamList?` and `ArgList` provide for. What
the grammar still cannot derive is the **named** form `v=1`; `ArgList ::= Expr (, Expr)*`
admits only positional arguments, so the emitted named form remains a divergence from Fig.
5 and is filed as F31 rather than quietly adopted.
-/
def renderGeneralInstance
    (program : LF.GeneralProgram)
    (reactorInstance : LF.GeneralReactorInstance) :
    Except String String :=
  match program.reactor? reactorInstance.reactorName with

  | none =>
      .error
        ("instance `" ++
          reactorInstance.name.value ++
          "` names reactor `" ++
          reactorInstance.reactorName.value ++
          "`, which this program does not declare")

  | some reactor =>

      match renderGeneralArguments
        reactorInstance.arguments
        reactor.parameters
      with

      | none =>
          .error
            ("instance `" ++
              reactorInstance.name.value ++
              "` supplies " ++
              toString reactorInstance.arguments.length ++
              " argument(s) to reactor `" ++
              reactorInstance.reactorName.value ++
              "`, which declares " ++
              toString reactor.parameters.length ++
              " parameter(s)")

      | some renderedArguments =>
          .ok
            ("  " ++
              reactorInstance.name.value ++
              " = new " ++
              reactorInstance.reactorName.value ++
              "(" ++
              String.intercalate
                ", "
                renderedArguments ++
              ")")

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

`Except` as of stage D, because an instantiation can now fail to resolve. The whole program
is refused rather than a partial `main` emitted: a `main reactor` missing one instance would
compile and would be a different model.
-/
def renderGeneralMain
    (program : LF.GeneralProgram) :
    Except String String := do

  let instances ←
    program.instances.mapM
      (renderGeneralInstance
        program)

  pure
    ("main reactor {\n" ++
      String.intercalate
        "\n"
        (instances ++
          (program.connections.map
            renderGeneralConnection)) ++
      "\n}")

/--
Render the C++ fields of a payload struct, in parameter order.

Type before name, because these are C++ declarations and not LF ones. One line, fields
separated by a single space, which is the form that was measured: `struct Args2 { int left;
int right; bool flag; };`.
-/
def generalStructFields
    (parameters :
      List LF.GeneralTypedParameter) :
    String :=
  String.intercalate
    " "
    (parameters.map
      (fun parameter =>
        renderGeneralType
          parameter.declaredType ++
          " " ++
          parameter.name.value ++
          ";"))

/--
The struct declaration one action needs, if it needs one.

`none` for arity 0 and 1, which are `: void` and a primitive type and so need no carrier.
The `Option` is what lets the program-level collection be derived by filtering rather than
by a separate arity test that could disagree with
`renderGeneralActionDecl`'s.
-/
def generalActionStructDecl?
    (reactorName : ReactorName)
    (action : LF.GeneralAction) :
    Option String :=
  match action.parameters with

  | [] =>
      none

  | [_] =>
      none

  | first :: second :: remaining =>
      some
        ("  struct " ++
          generalPayloadStructName
            reactorName
            action.name ++
          " { " ++
          generalStructFields
            (first :: second :: remaining) ++
          " };")

/--
Every struct declaration one reactor's actions need.

Explicit recursion rather than `List.filterMap`, matching this development's practice of
depending on no list combinator whose name has churned across Lean releases.
-/
def generalReactorStructDecls
    (reactorName : ReactorName) :
    List LF.GeneralAction →
    List String

  | [] =>
      []

  | action :: remaining =>

      match generalActionStructDecl?
        reactorName
        action
      with

      | none =>
          generalReactorStructDecls
            reactorName
            remaining

      | some declaration =>
          declaration ::
            generalReactorStructDecls
              reactorName
              remaining

/--
Every struct declaration a program needs, in reactor then action order.
-/
def generalProgramStructDecls :
    List LF.GeneralReactor →
    List String

  | [] =>
      []

  | reactor :: remaining =>
      generalReactorStructDecls
        reactor.name
        reactor.logicalActions ++
        generalProgramStructDecls
          remaining

/--
Render the program-level preamble, or nothing at all when no struct is needed.

**Derived from the reactors, never stored.** This follows the rule `generalEffectNames`
states above: a stored struct list could declare a struct no action uses, or omit one an
action needs, and both are printable. Derived, neither is expressible.

The empty case emits the empty string, so a program with no multi-value payload — which
includes every existing fixture and the byte-pinned base program of the `lfc` gate — gets no
preamble and its bytes do not move.

Takes the derived declarations rather than the program, for the same reason
`renderGeneralParameterList` does: the empty case is then `rfl`, and the derivation stays
one named function that the caller applies.
-/
def renderGeneralPreamble :
    List String →
    String

  | [] =>
      ""

  | first :: remaining =>
      "public preamble {=\n" ++
        String.intercalate
          "\n"
          (first :: remaining) ++
        "\n=}\n\n"

/--
Render a complete general LF/C++ source file.
-/
def renderGeneralProgram
    (program : LF.GeneralProgram) :
    Except String String := do

  let reactors ←
    program.reactors.mapM
      renderGeneralReactor

  let main ←
    renderGeneralMain
      program

  pure
    (targetHeader ++
      "\n\n" ++
      renderGeneralPreamble
        (generalProgramStructDecls
          program.reactors) ++
      String.intercalate
        "\n"
        reactors ++
      "\n" ++
      main ++
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

@[simp]
theorem renderGeneralExpr_boolLiteral
    (value : Bool) :
    renderGeneralExpr
        (.boolLiteral value) =
      renderGeneralValue
        (.bool value) := by
  rfl

@[simp]
theorem renderGeneralExpr_binary
    (operator : LF.GeneralBinaryOp)
    (left right : LF.GeneralExpr) :
    renderGeneralExpr
        (.binary operator left right) =
      "(" ++
        renderGeneralExpr left ++
        " " ++
        renderGeneralBinaryOp operator ++
        " " ++
        renderGeneralExpr right ++
        ")" := by
  rfl

@[simp]
theorem renderGeneralExpr_unary
    (operator : LF.GeneralUnaryOp)
    (operand : LF.GeneralExpr) :
    renderGeneralExpr
        (.unary operator operand) =
      "(" ++
        renderGeneralUnaryOp operator ++
        renderGeneralExpr operand ++
        ")" := by
  rfl

/-!
### The two claims stage D's "existing output does not move" argument rests on

Both are pinned as theorems rather than left to the byte comparison in the gate. The gate
checks one concrete program, which is evidence; these are the statements that make the
evidence generalize to every parameterless reactor and every payload-free program.

What is *not* claimed here is that any particular program is byte-identical. That is a fact
about specific programs, and `frontend/lean-bridge/GeneralLfPrinterTestMain.lean` pins it by
comparing whole strings — `expectedProgramText` for the parameterless payload-free program,
`expectedWidenedProgramText` for the one that exercises both features at once. Naming the
instrument matters here: an earlier draft of this note credited the byte comparison to
`frontend/check-general-lf-target.sh`, which contains none. That script answers the question
a string comparison cannot, whether real `lfc` accepts those bytes, and it is the weaker
claim of the two that is worth the compiler.
-/

@[simp]
theorem renderGeneralParameterList_nil :
    renderGeneralParameterList [] =
      "" := by
  rfl

@[simp]
theorem renderGeneralPreamble_nil :
    renderGeneralPreamble [] =
      "" := by
  rfl

end CppPrinter
end LF
end Relico
