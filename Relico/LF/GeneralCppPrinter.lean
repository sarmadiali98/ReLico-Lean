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
read that this repo already emits and `lfc` already accepts. Stage C wrote here that the
analogy was **not** measured, on the ground that probe 10 compiled a hand-written
`reaction(in) -> out` that never dereferenced a port. That is now half false, and the two
halves are worth separating rather than replacing with a blanket claim.

The **struct** form is measured. Probe `struct_as_port_type` — section 11 of
`tools/paper-measurements/lf_semantics_probe.sh`, run 2026-08-20 — compiles and runs
`auto p = *in.get();` followed by `p.left`, `p.right` and `p.flag` on a port typed by a
`public preamble` struct, and prints `RELICO_STRUCT_PORT 9 1`. That is the shape
`renderGeneralParameterRead` emits at arity ≥ 2, field reads included.

The **scalar** form — `auto x = *in.get();` on an `input in: int` — is measured by no probe
at all, and that is the narrower gap stage C's paragraph should have named. Both halves are
hand-written LF rather than generated LF in any case, so `GENERAL_LF_TARGET_OK` running over
a generated port-bearing file is still what closes them, and stage E is the stage that owns
it.

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
Wrap a rendered inline statement sequence in braces.

Two callers, the two arms of a rendered conditional, and it exists so that the spelling of an
**empty** branch is decided in one place. `LF.stmtWellFormed`'s `ifThenElse` arm checks each
branch with `List.all`, which holds of the empty list, so an empty branch is well-formed, a
bridge main can construct one directly, and this printer is total and therefore has to spell it.
`{}` rather than `{  }`, because two spaces around nothing is a rendering artefact and not a
style.
-/
def renderGeneralBraced
    (statements : String) :
    String :=
  if statements == "" then
    "{}"
  else
    "{ " ++
      statements ++
      " }"

/- The two statement renderers below are mutually recursive, because
`LF.GeneralStmt.ifThenElse` carries two nested bodies: rendering a statement needs the body
renderer, and the body renderer needs the statement renderer. A `mutual` block does not accept
a docstring, so each definition carries its own. -/
mutual

/--
Render one general statement.

`setPort` becomes reactor-cpp's `p.set(v);`, which is what Fig. 1b's body writes.

**Total as of stage D.** The arity-≥2 arm used to be `.error "… at most one integer
payload"`; it now constructs the payload struct, `<Struct>{<e1>, <e2>, …}`, in the form
measured under real `lfc`: `argsAction.schedule(Args2{1, 2, true}, 0ms);`.

**`Except` again as of stage E**, and not because a set became fallible: a set of arity ≥ 2
must name a C++ struct that this function cannot compute. That struct is named from the
**receiving** reactor and the message (`LF.GeneralPortPayload.struct`), because the two ends
of a connection have different port names and different declaring reactors and the receiver
is the only thing they share, so the name has to be read off the port declaration. Hence the
output-port list, and hence a refusal channel for a set of a port the reactor does not
declare.

`reactorName` and `outputPorts` are two parameters rather than one `reactor`, continuing
what stage D wrote here about passing the name: together they state the entire dependency,
and separately they say something the collapsed form would hide. `reactorName` names a
*scheduled* action's struct, which belongs to the declaring reactor — `stmtWellFormed`
requires a scheduled action to be declared on the reactor whose body schedules it.
`outputPorts` names a *set* port's struct, which belongs to somebody else's reactor
entirely. That the two payload struct names come from two different reactors is §4.1's
asymmetry reaching the printer.

The `setPort` arms enumerate the payload constructor and the argument list *together*, with
no wildcard on the payload. `docs/STAGE_E_DESIGN.md` §5.3 records that `input p: void` is
unmeasured under `lfc 0.11.0` and that the day the probe runs `GeneralPortPayload` gains a
constructor; a wildcard here would print something plausible for it instead of failing to
build.

Four of those six arms refuse. Each is unreachable from a well-formed program — the
`.setPort` arm of `stmtWellFormed` checks the argument count against
`LF.GeneralPortPayload.arity` — which is what lets them be refusals with distinct messages
rather than bytes chosen by guesswork. A struct payload of arity 0 or 1 is representable and
never built, since the translation emits `scalar` at arity 1 and refuses arity 0.

The output-only `.trace` arm emits one `std::printf` line for its literal tag. It
does not contribute an effect name; `generalProgramPreambleEntries` derives the
corresponding `<cstdio>` preamble entry from the bodies that contain such a line.

**Stage H's `ifThenElse` arm emits the whole conditional on one line**,
`if (<c>) { <then> } else { <else> }`, with both branch bodies rendered inline by
`renderGeneralBranchBody`. That is a formatting decision with a reason, and the reason is not
taste. Every arm of this function returns a string containing **no newline**, and
`renderGeneralBody` relies on it: it prefixes exactly one four-space indent to each rendered
statement, and to that statement's first line only. A conditional broken across lines would
therefore emit its interior flush left. Keeping the single-line invariant is what lets the
conditional be added without changing this function's signature, without threading a nesting
depth, and without disturbing any pinned printer expectation. Threading a depth is the better
long-term rendering and is deliberately deferred to a formatting pass that can be measured
against the gate rather than assumed.

The `else` branch is always emitted, even when empty, because `LF.GeneralStmt.ifThenElse`
always carries two bodies and this printer renders the structure it is given rather than
guessing which halves were meant.
-/
def renderGeneralStmt
    (reactorName : ReactorName)
    (outputPorts :
      List LF.GeneralPortDecl) :
    LF.GeneralStmt →
    Except String String

  | .assign target expression =>
      .ok
        (target.value ++
          " = " ++
          renderGeneralExpr
            expression ++
          ";")

  | .trace tag =>
      .ok
        ("std::printf(\"" ++
          tag ++
          "\\n\");")

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

      | first :: second :: remaining =>
          .ok
            (action.value ++
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
              ");")

  | .setPort port arguments =>

      match
          outputPorts.find?
            (fun declared =>
              declared.name == port)
      with

      | none =>
          .error
            ("statement sets port `" ++
              port.value ++
              "`, which is not declared as an output of the reactor being rendered")

      | some declared =>

          match declared.payload,
              arguments
          with

          | .scalar _, [] =>
              .error
                ("statement sets port `" ++
                  port.value ++
                  "` with no value, but that port declares a scalar payload " ++
                  "and so carries exactly one")

          | .scalar _, [argument] =>
              .ok
                (port.value ++
                  ".set(" ++
                  renderGeneralExpr
                    argument ++
                  ");")

          | .scalar _, _ :: _ :: _ =>
              .error
                ("statement sets port `" ++
                  port.value ++
                  "` with more than one value, but that port declares a scalar " ++
                  "payload and so carries exactly one")

          | .struct _ _ _, [] =>
              .error
                ("statement sets port `" ++
                  port.value ++
                  "` with no value; whether a payload-struct port of arity zero is " ++
                  "accepted by lfc 0.11.0 is unmeasured, so the translation refuses " ++
                  "to build one (see the stage E design, section 5.3)")

          | .struct _ _ _, [_] =>
              .error
                ("statement sets port `" ++
                  port.value ++
                  "` with one value, but that port declares a payload struct; the " ++
                  "translation emits a scalar payload at arity one, so a one-field " ++
                  "struct is representable and never built")

          | .struct receiver message _,
              first :: second :: remaining =>
              .ok
                (port.value ++
                  ".set(" ++
                  generalPayloadStructName
                    receiver
                    message ++
                  "{" ++
                  String.intercalate
                    ", "
                    ((first :: second :: remaining).map
                      renderGeneralExpr) ++
                  "});")

  | .ifThenElse condition thenBody elseBody => do

      let thenRendered ←
        renderGeneralBranchBody
          reactorName
          outputPorts
          thenBody

      let elseRendered ←
        renderGeneralBranchBody
          reactorName
          outputPorts
          elseBody

      pure
        ("if (" ++
          renderGeneralExpr
            condition ++
          ") " ++
          renderGeneralBraced
            thenRendered ++
          " else " ++
          renderGeneralBraced
            elseRendered)

  | .localDecl name declaredType value =>
      .ok
        (renderGeneralType
            declaredType ++
          " " ++
          name.value ++
          " = " ++
          renderGeneralExpr
            value ++
          ";")

/--
Render one conditional branch's body as a single inline statement sequence.

Statements are separated by one space rather than by a newline, which is the whole reason this
function is not `renderGeneralBody`: that one indents each statement and joins with newlines,
and it also renders a reaction's trigger-payload preamble, which a branch does not have. The
two are different jobs that happen to walk the same list.

Recursion is written out over the list rather than expressed with `mapM`, so that the recursive
calls are syntactically visible to the termination checker on a nested inductive.

An empty body renders as the empty string, and `renderGeneralBraced` turns that into `{}`.
A refusal from any statement propagates, so a branch containing a set of an undeclared output
port refuses exactly as the same statement outside a branch would.
-/
def renderGeneralBranchBody
    (reactorName : ReactorName)
    (outputPorts :
      List LF.GeneralPortDecl) :
    LF.GeneralBody →
    Except String String

  | [] =>
      .ok ""

  | [statement] =>
      renderGeneralStmt
        reactorName
        outputPorts
        statement

  | statement :: remaining => do

      let rendered ←
        renderGeneralStmt
          reactorName
          outputPorts
          statement

      let renderedRemaining ←
        renderGeneralBranchBody
          reactorName
          outputPorts
          remaining

      pure
        (rendered ++
          " " ++
          renderedRemaining)

end

/- `generalEffectNames` and `generalEffectNamesFrom` are mutually recursive because
`LF.GeneralStmt.ifThenElse` carries two nested bodies. A `mutual` block does not accept a
docstring, so each definition carries its own. -/
mutual

/--
Collect the names a body has effects on, in first-occurrence order.

Both effect kinds are collected in **one** pass over the body, so a body that sets a port
and schedules an action lists them interleaved exactly as it produces them. Fig. 1b's
`-> reading,sendReading` matches its own body's `reading.set(0); sendReading.schedule(5ms);`
in that order, which makes the paper's example evidence for the rule rather than merely
consistent with it.

Deriving the list from the body — instead of storing an `effects` field — is what makes it
impossible to print an effect the body does not produce, or to omit one it does.

**Stage H's `ifThenElse` arm unions both branches, and that union is what makes the emitted
program compile.** A `setPort` or `schedule` inside a branch is an effect the reaction may
perform, and reactor-cpp requires a reaction to declare every port it may write, so omitting a
branch's effects would emit LF that `lfc` rejects. The consequence is stated rather than
hidden: a reaction now declares the effects of **both** arms even though one firing performs at
most one arm's worth. That is the same conservative static reading `LF.setPortNamesOfBody`
takes, and it is deliberately not path-dependent, because an effect clause is a property of the
emitted artefact and cannot depend on a run.

Deduplication and ordering are unchanged. The accumulator threads through the nested folds, so
a name is still added only when `names.contains` says it is absent, a port set in both arms
appears once, and first appearance still fixes position. The then-branch is folded before the
else-branch, so a name first set in the then-branch orders before one first set only in the
else-branch, and both order before names first set after the conditional.

Written as a `mutual` accumulator pair rather than a `foldl` with an inner `match`, because the
`ifThenElse` arm has to traverse two nested bodies and therefore has to call the body-level
function; a recursive call inside a function passed to `foldl` is invisible to structural
recursion on a nested inductive.
-/
def generalEffectNames :
    LF.GeneralBody →
    List String
  | body =>
      generalEffectNamesFrom
        []
        body

/-- The effect names of a body, accumulated onto the names already found. -/
def generalEffectNamesFrom :
    List String →
    LF.GeneralBody →
    List String

  | names, [] =>
      names

  | names, .assign _ _ :: remaining =>
      generalEffectNamesFrom
        names
        remaining

  | names, .trace _ :: remaining =>
      generalEffectNamesFrom
        names
        remaining

  | names, .schedule action _ _ :: remaining =>
      generalEffectNamesFrom
        (if names.contains action.value then
          names
        else
          names ++
            [action.value])
        remaining

  | names, .setPort port _ :: remaining =>
      generalEffectNamesFrom
        (if names.contains port.value then
          names
        else
          names ++
            [port.value])
        remaining

  | names, .ifThenElse _ thenBody elseBody :: remaining =>
      generalEffectNamesFrom
        (generalEffectNamesFrom
          (generalEffectNamesFrom
            names
            thenBody)
          elseBody)
        remaining

  | names, .localDecl _ _ _ :: remaining =>
      generalEffectNamesFrom
        names
        remaining

end

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
The LF type a port declaration prints.

`renderGeneralActionDecl` derives an action's printed type from its **arity** — `void`, the
bare scalar, or the payload struct — and a port cannot be done that way, because a port
stores *what it carries* rather than a parameter list. So this dispatches on the payload
constructor, which is the port-side analogue and not the same rule.

The consequence is worth stating because it looks like an inconsistency and is not one: a
`struct` payload prints the struct name at every arity, including the arities the
translation never builds, whereas an action of arity 1 prints its parameter's own type. Two
declarations disagreeing about one struct is therefore impossible from this direction —
whatever the payload names is what gets printed, and `generalPortStructDecl?` declares
exactly that struct from the same field.

There is no `void` arm because `GeneralPortPayload` has no `void` constructor, and that
absence is a measurement gap rather than a judgment: see the type's own docstring and
`docs/STAGE_E_DESIGN.md` §5.3.
-/
def renderGeneralPortPayloadType :
    LF.GeneralPortPayload →
    String

  | .scalar declaredType =>
      renderGeneralType
        declaredType

  | .struct receiver message _ =>
      generalPayloadStructName
        receiver
        message

/--
Render one input-port declaration.
-/
def renderInputPortDecl
    (port : LF.GeneralPortDecl) :
    String :=
  "  input " ++
    port.name.value ++
    ": " ++
    renderGeneralPortPayloadType
      port.payload

/--
Render one output-port declaration.
-/
def renderOutputPortDecl
    (port : LF.GeneralPortDecl) :
    String :=
  "  output " ++
    port.name.value ++
    ": " ++
    renderGeneralPortPayloadType
      port.payload

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

`<trigger>_payload`. Derived from the trigger's name rather than fixed, and the reason is a
recorded exposure rather than a preference: this identifier shares a scope with the
source-derived parameter binders below it, and nothing proves a source model has no
message-server parameter called `arithmetic_payload`. The inherited payload family emits a
bare `auto payload = …`, so the exposure is not introduced here, and deriving from the
trigger name narrows a collision to a source identifier that mentions a trigger name.

Fixing it properly means a freshness condition over the union of all source identifiers in
a reactor, which is a well-formedness obligation and does not belong inside a printer. It
is filed as F29 rather than patched here.

Takes a `String` as of stage E, because both trigger kinds that can carry a multi-value
payload now reach it: a logical action for a self-send and an input port for an external
one. Naming the parameter `triggerName` and not `actionName` is the whole of the change —
the spelling was never about actions, it was about whatever the reaction is triggered by,
and stage D simply had only one such thing.

One function so that the binding site and every field read cannot disagree.
-/
def generalPayloadBinderName
    (triggerName : String) :
    String :=
  triggerName ++
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

A port is read the same way an action is, `*p.get()`, and as of stage E the arity-≥2 arm
for a port is a destructuring rather than an error. The module note above records which half
of that analogy is measured and which is not, and by which probe.

Every trigger-and-arity combination is enumerated, with one exception that is deliberate
rather than economical: a startup reaction emits no read **at any arity**, so its two
arities are one arm. Stage C had the second arity as an error, on the ground that nothing
can deliver a value to a startup reaction. That ground is sound about a payload and wrong
about what stage D puts in the list — `assembleGeneralStartupReaction` fills it with the
constructor's formals, which are the *reactor's* parameters and are readable in a reaction
body with no binder at all. Emitting nothing is therefore the whole job here. See the
module note and finding F33; the arms are not collapsed by a wildcard, so the stage that
adds a fourth trigger still gets a build error.

An input port with two or more parameters was an error through stage D, on the ground that a
`GeneralPortDecl` declares one type and so delivers one value and, unlike an action, has no
parameter list to destructure. §5.2 of `docs/STAGE_E_DESIGN.md` makes the first half of that
sentence false — a port now declares a payload — and the second half was never the obstacle:
the parameter list being destructured is the *reaction's*, and a port-triggered reaction gets
it from the message server exactly as an action-triggered one does. So the arm is now the
struct-destructuring arm, and the two multi-value arms differ in nothing but which name they
pass to `generalPayloadBinderName`.

That makes this function **total as of stage E**: every one of its seven arms succeeds. The
`Except` is kept rather than narrowed to `String` because `renderGeneralBody` is `Except`
regardless — a `setPort` it renders can refuse — so narrowing here would move a `←` to a
`let` in one caller and buy nothing.
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
              action.value ++
            " = *" ++
            action.value ++
            ".get();") ::
            ((first :: second :: remaining).map
              (fun parameter =>
                "    auto " ++
                  parameter.value ++
                  " = " ++
                  generalPayloadBinderName
                    action.value ++
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
      first :: second :: remaining =>
      .ok
        (String.intercalate
          "\n"
          (("    auto " ++
            generalPayloadBinderName
              port.value ++
            " = *" ++
            port.value ++
            ".get();") ::
            ((first :: second :: remaining).map
              (fun parameter =>
                "    auto " ++
                  parameter.value ++
                  " = " ++
                  generalPayloadBinderName
                    port.value ++
                  "." ++
                  parameter.value ++
                  ";"))))

/--
Render one reaction body, including trigger-payload extraction when required.

`reactorName` is threaded only so that a `schedule` of a multi-value payload can name its
struct, and `outputPorts` only so that a `set` of one can name *its* struct — which is a
different reactor's. Both are the declaring reactor's own data; see `renderGeneralStmt` for
why the two are not one argument.
-/
def renderGeneralBody
    (reactorName : ReactorName)
    (outputPorts :
      List LF.GeneralPortDecl)
    (reaction :
      LF.GeneralReaction) :
    Except String String := do

  let parameterRead ←
    renderGeneralParameterRead
      reaction

  let statements ←
    reaction.body.mapM
      (renderGeneralStmt
        reactorName
        outputPorts)

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
    (outputPorts :
      List LF.GeneralPortDecl)
    (reaction :
      LF.GeneralReaction) :
    Except String String := do

  let body ←
    renderGeneralBody
      reactorName
      outputPorts
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
change. Stage E makes that sentence load-bearing rather than cautionary: a receiver now has
one reaction per sending instance for the same message server, and which of them runs first
at one tag is decided here and nowhere else.
-/
def renderGeneralMessageReactions
    (reactorName : ReactorName)
    (outputPorts :
      List LF.GeneralPortDecl) :
    List LF.GeneralReaction →
    Except String String

  | [] =>
      .ok ""

  | [reaction] =>
      renderGeneralReaction
        reactorName
        outputPorts
        reaction

  | reaction :: remaining => do
      let renderedReaction ←
        renderGeneralReaction
          reactorName
          outputPorts
          reaction

      let renderedRemaining ←
        renderGeneralMessageReactions
          reactorName
          outputPorts
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

This one takes the whole reactor and so needs no port argument, which is not an
inconsistency with its siblings but the reason they have one: they are called with a
reactor's name and its ports where the reactor itself is not in scope.
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
        reactor.outputPorts
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
multi-value payload struct, and as of stage E so is its output-port list, which names the
payload struct of a `set`. The distinction between the two is in `renderGeneralStmt`.
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
      reactor.outputPorts
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
One payload struct declaration, from the name it declares and the fields it carries.

Split out in stage E because three kinds of declaration now reach it — a logical action's, an
input port's and an output port's — and the alternative was the same string fragments written
three times, which is how two of the three would eventually have drifted. The two-space indent
belongs to the preamble, not to the struct, and is kept here so that every caller inherits it.
-/
def generalPayloadStructDecl
    (structName : String)
    (parameters :
      List LF.GeneralTypedParameter) :
    String :=
  "  struct " ++
    structName ++
    " { " ++
    generalStructFields
      parameters ++
    " };"

/--
The struct declaration one action needs, paired with the name it declares, if it needs one.

`none` for arity 0 and 1, which are `: void` and a primitive type and so need no carrier.
The `Option` is what lets the program-level collection be derived by filtering rather than
by a separate arity test that could disagree with
`renderGeneralActionDecl`'s.

The declared **name is carried alongside** the declaration as of stage E, and only because the
program-level collection deduplicates on it. One struct is now named by up to three kinds of
declaration — the receiver's logical action when the message is also self-sent, the sender's
output port, and one input port per sending instance — and recovering a name by parsing a
rendered C++ declaration back out would be a worse answer to the same question.
-/
def generalActionStructEntry?
    (reactorName : ReactorName)
    (action : LF.GeneralAction) :
    Option (String × String) :=
  match action.parameters with

  | [] =>
      none

  | [_] =>
      none

  | first :: second :: remaining =>
      let structName :=
        generalPayloadStructName
          reactorName
          action.name

      some
        (structName,
          generalPayloadStructDecl
            structName
            (first :: second :: remaining))

/--
The struct declaration one port needs, paired with the name it declares, if it needs one.

Dispatches on the **payload constructor** and not on arity, which is the one difference from
`generalActionStructEntry?` and is forced rather than chosen: `renderGeneralPortPayloadType`
prints the struct name whenever the payload is a `struct`, so a declaration has to exist
whenever the payload is a `struct`, including at the arities the translation never builds. An
arity test here would let a port declare a type the preamble does not declare, which is the
single failure the derived-never-stored rule exists to prevent.

One function serves both directions. An input port and an output port declare the same struct
from the same field, so a walk per direction would be two copies of one rule.
-/
def generalPortStructEntry?
    (port : LF.GeneralPortDecl) :
    Option (String × String) :=
  match port.payload with

  | .scalar _ =>
      none

  | .struct receiver message parameters =>
      let structName :=
        generalPayloadStructName
          receiver
          message

      some
        (structName,
          generalPayloadStructDecl
            structName
            parameters)

/--
Every struct entry one reactor's actions need.

Explicit recursion rather than `List.filterMap`, matching this development's practice of
depending on no list combinator whose name has churned across Lean releases.
-/
def generalActionStructEntries
    (reactorName : ReactorName) :
    List LF.GeneralAction →
    List (String × String)

  | [] =>
      []

  | action :: remaining =>

      match generalActionStructEntry?
        reactorName
        action
      with

      | none =>
          generalActionStructEntries
            reactorName
            remaining

      | some entry =>
          entry ::
            generalActionStructEntries
              reactorName
              remaining

/--
Every struct entry one list of ports needs.

Same explicit recursion, and no reactor name parameter: a port's struct is named by the
**receiving** reactor, which the payload already carries, and the reactor a port is declared
on is the sender for one direction and the receiver for the other. Passing the declaring
reactor's name in would therefore be passing in the wrong name half the time.
-/
def generalPortStructEntries :
    List LF.GeneralPortDecl →
    List (String × String)

  | [] =>
      []

  | port :: remaining =>

      match generalPortStructEntry?
        port
      with

      | none =>
          generalPortStructEntries
            remaining

      | some entry =>
          entry ::
            generalPortStructEntries
              remaining

/--
Every struct entry one reactor needs: its actions, then its inputs, then its outputs.

Actions first keeps every committed fixture's preamble byte-identical, since no fixture that
exists today has a struct-typed port and so the port walks contribute nothing to them. Inputs
before outputs is the order `renderGeneralPortDecls` prints in, so that the preamble and the
port block of one reactor tell the same story in the same sequence.
-/
def generalReactorStructEntries
    (reactor : LF.GeneralReactor) :
    List (String × String) :=
  generalActionStructEntries
      reactor.name
      reactor.logicalActions ++
    generalPortStructEntries
        reactor.inputPorts ++
      generalPortStructEntries
        reactor.outputPorts

/--
Every struct entry a program needs, in reactor order, with duplicates still present.
-/
def generalProgramStructEntries :
    List LF.GeneralReactor →
    List (String × String)

  | [] =>
      []

  | reactor :: remaining =>
      generalReactorStructEntries
        reactor ++
        generalProgramStructEntries
          remaining

/--
Drop every entry whose struct name has already been declared, keeping the first.

The deduplication is **by name**, not by rendered declaration, and the difference is
load-bearing in both directions.

Identical declarations must collapse. A message server that is both self-sent and externally
received is named by one logical action and by two or more ports, and `lfc` compiles a
`public preamble` containing one `struct Collector_report_Args`, not three copies of it.
Deduplicating on the rendered string would handle this case too, and only this case.

Declarations that share a name and differ must also collapse, because C++ rejects a file that
declares one struct twice with different fields, so emitting both would trade a wrong preamble
for no build at all. Keeping the first is the only behaviour here that leaves a *legal* file.

That second half has a cost worth writing down rather than leaving for a reader to find: when
two declarations share a name and differ in their fields, this silently keeps the first, and
nothing in this printer notices. It cannot arise from the translation, where the name is a
function of the receiving reactor and the message while the fields are a function of that same
message server's formals, and DTR well-formedness makes message-server names unique within a
class. It can arise from a hand-built `LF.GeneralProgram`, and no LF-side predicate rules it
out: `connectionWellFormed` compares the two ends of one *connection*, which is not the same
as comparing two declarations of one struct name across a whole program. That gap is finding
**F41**, and the reason it is not closed here is that a printer is the wrong layer to discover
it in — a well-formedness clause quantifying over every declaration of a name is the right one.
-/
def generalDedupStructDecls :
    List String →
    List (String × String) →
    List String

  | _, [] =>
      []

  | declared, (structName, declaration) :: remaining =>
      if declared.contains structName then
        generalDedupStructDecls
          declared
          remaining
      else
        declaration ::
          generalDedupStructDecls
            (structName :: declared)
            remaining

/--
Every struct declaration a program needs, in reactor then action then port order, each
declared exactly once.
-/
def generalProgramStructDecls
    (reactors : List LF.GeneralReactor) :
    List String :=
  generalDedupStructDecls
    []
    (generalProgramStructEntries
      reactors)

/--
Whether a program contains a target-output trace statement.

The C++ line emitted by `renderGeneralStmt` uses `std::printf`, so the
program-level preamble must include `<cstdio>` exactly when a trace body needs
it. The check is derived from the same reaction bodies that are rendered; no
caller can forget to update a stored preamble flag.
-/
def generalBodyHasTrace :
    LF.GeneralBody →
    Bool

  | [] =>
      false

  | .trace _ :: _ =>
      true

  | _ :: remaining =>
      generalBodyHasTrace remaining

/--
Whether any startup or message reaction in a program contains a trace.
-/
def generalProgramHasTrace
    (program : LF.GeneralProgram) :
    Bool :=
  program.reactors.any
    (fun reactor =>
      generalBodyHasTrace reactor.startupReaction.body ||
        reactor.messageReactions.any
          (fun reaction =>
            generalBodyHasTrace reaction.body))

/--
The derived entries for a program-level preamble, including the C++ header
needed by trace statements.
-/
def generalProgramPreambleEntries
    (program : LF.GeneralProgram) :
    List String :=
  let declarations :=
    generalProgramStructDecls
      program.reactors

  if generalProgramHasTrace program then
    "#include <cstdio>" :: declarations
  else
    declarations

/--
Render the program-level preamble, or nothing at all when no struct or trace
support is needed.

**Derived from the reactors, never stored.** This follows the rule `generalEffectNames`
states above: a stored struct list could declare a struct nothing uses, or omit one an
action or a port needs, and both are printable. Derived, neither is expressible. Stage E is
where that stops being a matter of taste — a struct is now named by an action and by ports on
two *different* reactors, so a stored list would have to be kept in agreement with three
declarations at once, and the failure would be a program that names a type its own preamble
does not declare.

The empty case emits the empty string, so a program with no multi-value payload
and no trace — which includes every existing fixture and the byte-pinned base
program of the `lfc` gate — gets no preamble and its bytes do not move.

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
        (generalProgramPreambleEntries
          program) ++
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
