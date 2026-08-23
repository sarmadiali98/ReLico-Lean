# Stage D design — the DTR → LF translation, without external sends

Status: **design, not implemented.** Stages B and C each had a design document written and reviewed
before any Lean was added, and this follows that pattern. Nothing in `Relico/` changes until this is
approved.

Stage D is the fourth of the approved A–H translator-generalization plan, whose §6 states it as
*"D translation sans external sends"*. Stage C delivered the LF representation and a printer, gated
twice — `GENERAL_LEAN_GATE_OK` (506 jobs, 45 assertions) and `GENERAL_LF_TARGET_OK` (real `lfc 0.11.0`
accepts, compiles and runs the printer's own output). Stage D is the first stage that connects the two
syntaxes.

## 1. What stage D is, and exactly where its boundary falls

Stage D is a function from a well-formed general DTR model to a general LF program, plus the theorems
that say the function preserves the structure the later stages will need.

In scope:

| DTR construct | LF construct |
|---|---|
| reactive class | reactor |
| state variable declaration | state declaration |
| message server | one logical action **and** one reaction triggered by it |
| constructor | the mandatory `startupReaction` |
| self-send `self.m(args) after(d)` | `m.schedule(<args>, <d>);` |
| assignment | assignment |
| actor instance | reactor instance |

Out of scope, and deliberately so: external sends. A `GeneralStmt.send` whose target is
`.knownRebec _` is what produces an output port, an input port, a connection and a port-triggered
reaction, and that is stages E and F. Stage D therefore emits **no ports and no connections** — the
reactor's `inputPorts` and `outputPorts` are `[]` and the program's `connections` is `[]`.

That is legal rather than a placeholder, and stage C established it on purpose. `GeneralProgram`'s
docstring records that Fig. 5 puts a `+` on reactors and instances and a `*` only on connections, so
an empty connection list is the grammar's own case; and `lfc` was measured to accept a program whose
declared input port is unconnected, which is the weaker neighbouring fact.

**What stage D must refuse.** An external send is representable in a well-formed DTR model, so the
translation cannot simply not mention it. Three candidate treatments, and the one chosen:

1. *Drop it.* Rejected outright. Silently discarding a send changes what the model means, and it is
   exactly the class of defect this generalization exists to remove.
2. *Translate it now.* Rejected: it is stage E, it needs the port-naming rule that ledger entry **P20**
   shows the paper does not supply (Fig. 1b names a port after the message server, Fig. 2b after the
   output port plus a capitalized instance — the two figures disagree), and P20 is still open on a
   paper decision.
3. **Refuse it, with a diagnostic naming the construct and the stage.** Chosen. The translation returns
   `Except String` and an external send produces an error mentioning the target rebec and the message
   name.

Choice 3 has a consequence worth stating plainly rather than discovering later: **stage D's translation
is a partial function, and it is partial on a construct that is inside the fragment.** That is not the
same kind of partiality as the printer's. The printer is partial because a target limitation is real;
stage D is partial because a *stage boundary* is real, and the partiality is scheduled to disappear at
stage E. The design keeps the two distinguishable by putting them at different layers and giving the
stage-boundary refusal a diagnostic that names the stage, so a reader can tell "not yet" from "not
possible".

## 2. What stage D inherits — five gaps, one cause

Stage C's design recorded divergence 9.5 as an expression-constructor asymmetry. Measured against the
source, it is that plus four more, and they share one cause: **the LF layer of this family was
assembled from an earlier integer-only, single-payload family, so the word "general" in its file names
describes its ports and connections, not its data.**

| | DTR side | LF side |
|---|---|---|
| expression constructors | 6 — `intLiteral boolLiteral stateVar parameterVar binary unary` | **3** — `intLiteral stateVar parameterVar` |
| operators | `GeneralBinaryOp` 13 constructors, `GeneralUnaryOp` 2 | **do not exist** |
| types | `GeneralType = int │ boolean`, `GeneralValue = int Int │ bool Bool` | **no type representation at all** |
| state declaration | `GeneralStateVariableDecl.declaredType : GeneralType` | `LF.StateVariableDecl` = `name` + `initialValue : Int` |
| message-server parameters | `GeneralTypedParameter.declaredType : GeneralType` | `GeneralAction.parameters : List VarName`, untyped |
| payload arity | unbounded | **≤ 1**, refused at three printer sites |
| constructor arguments | `GeneralConstructor.parameters` + per-instance `GeneralActorInstance.arguments` | **no reactor parameter list**; `new R()` printed with no arguments |

Gap by gap, with the evidence:

**Gap 1 — expressions.** `LF.GeneralExpr` cannot represent `boolLiteral`, `binary` or `unary`.
`renderGeneralExpr` (`GeneralCppPrinter` :66) has exactly three arms to match.

**Gap 2 — type erasure.** There is no LF type. `renderInputPortDecl` (:204), `renderOutputPortDecl`
(:214) and `renderGeneralActionDecl` (:255) each hardwire the *string literal* `": int"`. And
`LF.StateVariableDecl` — which `GeneralReactor.stateVariables` reuses — is defined in
`Relico/LF/StoreSyntax.lean:12` with `initialValue : Int`. A DTR `boolean flag` has initial value
`.bool false`, which has no `Int` counterpart, so stage D cannot translate the **declaration**, quite
apart from any expression.

**Gap 3 — payload arity.** `renderGeneralActionDecl` (:257), and `renderGeneralParameterRead` at
:339 and :360, all refuse more than one parameter with *"the current C++ printer foundation supports at
most one integer payload"*. A message server with two parameters therefore cannot be printed — and
`msgsrv arithmetic(int left, int right)` is in the committed fixture.

**Gap 4 — untyped action parameters.** `GeneralAction.parameters : List VarName` with a docstring
stating *"the value domain is integer-only, as in the payload family this borrows its shape from"*. A
`msgsrv logic(boolean first, boolean second)` has nowhere to record that its parameters are booleans.

**Gap 5 — no reactor parameters, so instances of one class are indistinguishable.** `GeneralReactor`
has no parameter list and `renderGeneralInstance` (:553) emits `name ++ " = new " ++ reactorName ++ "()"`.
The committed fixture `frontend/fixtures/general/constructor-arguments.rebeca` declares
`Configured(int bound, boolean active)` and instantiates it **twice with different arguments** —
`configuredOn():(7, true)` and `configuredOff():(0, false)`. Both would print as `new Configured()`.
This gap is different in kind from the other four: it is not inherited from the payload family's data
model, it is a production of the paper's own grammar that stage C did not carry over —
`Reactor ::= reactor R (ParamList?) {PortDecl* StateDecl* ActionDecl* ReactionDecl*}`, quoted in stage C's
own `GeneralReactor` docstring. §5.5 restores it.

None of these is a defect in stage C's own terms — stage C was representation and printing for ports and
connections, and it did that, gated twice. They are debts that come due precisely when a translation
first has to carry DTR data into LF, which is stage D.

## 3. The decision the LF syntax explicitly deferred to this stage, and why the evidence makes it

`Relico/LF/GeneralSyntax.lean` lines 60–63 hand this stage the choice in as many words:

> *"The stage that writes the translation is the one that has to either widen this type or restrict its
> own domain, and leaving the two sides visibly unequal is what forces that choice to be made in the
> open instead of inside a default branch."*

So: widen the LF side, or restrict the translation's domain to what the LF side can already hold.

**Restricting the domain is not a live option, and the reason is measured, not aesthetic.**
`frontend/fixtures/general/expressions.rebeca` is a **committed positive fixture of this very family**.
It contains `boolean flag;`, all five arithmetic operators, unary minus, all six comparisons, `&&`,
`||`, `!`, and a `true` literal. Its committed `expressions.parser.json` carries **18 `binary`, 3
`unary` and 2 `boolLiteral`** nodes. `Relico/Frontend/GeneralElaborator.lean` really constructs them —
`.boolLiteral` at 349–359, `.binary` at 410, the operator readers at 265 and 294. And
`Relico/DTR/GeneralWellFormed.lean` constrains expressions **not at all**.

A domain-restricted stage D would therefore refuse this repository's own frontend, on this repository's
own positive fixture, for this repository's own family. It would also miss the governing direction by
its own terms — the 2026-08-17 decision was to stop authoring benchmarks until *"the translator
accepts all kinds of DTR models in such a way that is described in the paper"*, and a translator that
cannot carry `accumulator = left + right;` accepts approximately no real model.

**Decision: widen the LF side.** The translation of expressions and declarations becomes **total**; the
printer stays the only partial component. That split is not invented here — `LF/GeneralSyntax.lean`
lines 84–91 already names it as this repository's convention: *"Keeping `schedule`'s argument list
unbounded also keeps the translation total and the printer partial, which is the split this repository
already has."*

### 3.1 What this costs, stated up front

Widening means **editing files stage C committed four commits ago**: `Relico/LF/GeneralSyntax.lean`,
`Relico/LF/GeneralWellFormed.lean`, `Relico/LF/GeneralCppPrinter.lean` and the 25 printer assertions in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean`. Consequences to accept deliberately:

- **Both gates must be re-run, not just the cheap one.** `GENERAL_LEAN_GATE_OK` and
  `GENERAL_LF_TARGET_OK`. The second is what makes widening safe to attempt at all: every new construct
  the printer learns to emit gets compiled and run by a real `lfc` before it is believed. Stage C's last
  act bought exactly this.
- `EXPECTED_PRINTER_ASSERTIONS` in `frontend/check-general-lean.sh:182` rises, and the new value must be
  predicted before the gate is run rather than read off after it.
- The 32-line base program the printer's assertions pin **must not change bytes**, so that the widening
  is demonstrably additive. Arity 0 keeps `: void`; arity 1 keeps the bare `: int`. If those bytes move,
  the widening has changed existing behaviour and that is a separate discussion.

### 3.2 An honest alternative that was considered and rejected

*Leave the LF side alone and put the widening in a stage D′ after E–H.* Rejected: every later stage
builds on the translation, so each would be written against a data model known to be wrong, and the
widening would then touch stages D through H at once instead of stage C's three files now. Cost grows
with delay and nothing is learned by waiting.

## 4. Measured target facts that constrain the design

Every claim in this section was established by running real `lfc 0.11.0` on the Mac, on 2026-08-19,
before this design was written. Zero occurrences in the repository means unverified, not unavailable, so
each construct the widened printer will emit was probed first.

**`bool` is a first-class LF type in all three positions the widening needs.** One program, `lfc` exit
0, `SUCCESS (compiling generated C++ code)`, binary exit 0:

- `output flagOut: bool` and `input flagIn: bool` — bool-typed ports.
- `state flag: bool = false` — bool state with a boolean initializer.
- `logical action notify: bool` — bool action payload, read back with `auto w = *notify.get();`.

Fixtures already show `: void` and `: int` for action payloads, so `bool` completes the set.

**Operators need no probe, now or ever.** Inside `{= … =}` the text is verbatim C++ that LF passes
through untouched, so `+ - * / %`, `== != < <= > >=` and `&& || !` are guaranteed by the C++ standard
rather than by anything about LF. The only LF-level risk was ever in the *type* positions above. This is
worth recording because it prevents a future session spending a Mac round trip re-checking arithmetic.

**A multi-value action payload is available by two routes, and both were measured to work.** Two files
compiled separately so neither could mask the other; both `lfc` exit 0, both binaries exit 0:

- **Route A** — a struct in a program-level `public preamble`: `struct Args2 { int left; int right; bool
  flag; };` with `logical action argsAction: Args2`, scheduled as `argsAction.schedule(Args2{1, 2,
  true}, 0ms);` and read as `auto a = *argsAction.get(); … a.left … a.flag`. Printed `RELICO_STRUCT 3 1`,
  so both values and a mixed `bool` field survive.
- **Route B** — a code-block type carrying a comma: `logical action pairAction: {= std::pair<int,int>
  =}`. Printed `RELICO_PAIR 7`.

So the printer's *"the current C++ printer foundation supports at most one integer payload"* is a
limitation of **this repository's printer**, not of the target. Recorded as a finding, because that
message reads as though it were reporting a target constraint.

**Route A is chosen, on merit rather than necessity.** Its struct field names are the source formal
parameter names, its arity is unbounded, and mixed types are natural. Route B forces positional
`std::get<i>` access for arity above two and discards the parameter names, which would make the emitted
body harder to relate to the source and would put an index where the source has an identifier. Route A
also supplies the per-parameter type that Gap 4 needs, so one mechanism closes gaps 2, 3 and 4.

**Precedence is a claim the printer would be making.** The fixture contains
`accumulator = left + right * 2 - 1;`. A printer that emits infix operators without parentheses is
asserting that its own operator precedence agrees with C++'s. The design does not make that assertion:
**every binary and unary application is fully parenthesized.** The output is uglier and unambiguously
correct, and the correctness argument is one line rather than a table.

## 5. The widened LF representation

New types on the LF side rather than reuse of the DTR ones. That is this repository's existing
convention and it is stated in `DTR/GeneralSyntax.lean` lines 48–51 about `GeneralValue`: *"This is
deliberately a new type rather than a widening of `Relico.Value`."* Sharing a type across the two
syntaxes would also make the translation's structural theorems vacuous in the worst way — a theorem that
a translated expression equals its source is uninteresting when both sides are literally the same term.

### 5.1 A type, and no redundant initial value

```
inductive GeneralType where
  | int
  | boolean
```

`GeneralStateVariableDecl` carries **only** a name and a declared type — no initial value:

```
structure GeneralStateVariableDecl where
  name : VarName
  declaredType : LF.GeneralType
```

This is a deliberate narrowing relative to the `LF.StateVariableDecl` it replaces, which carries
`initialValue : Int`. The justification is on the DTR side: a source-level initializer is rejected
upstream, `GeneralStateVariableDecl` has no initializer field, and `GeneralType.initialValue` together
with the theorem `typeOf_initialValue` make the initial valuation a function of the declared type alone.
Carrying a separate initial value would create a field that can disagree with the type and a
well-formedness conjunct to forbid the disagreement. The printer emits `= 0` for `int` and `= false` for
`boolean`.

`LF.StateVariableDecl` in `StoreSyntax.lean` is **not** touched; the earlier families keep it.

### 5.2 Typed ports and typed action parameters

```
structure GeneralPortDecl where
  name : PortName
  declaredType : LF.GeneralType

structure GeneralTypedParameter where
  name : VarName
  declaredType : LF.GeneralType
```

`GeneralReactor.inputPorts` and `.outputPorts` become `List LF.GeneralPortDecl`, and
`GeneralAction.parameters` becomes `List LF.GeneralTypedParameter`.

Stage D emits no ports, so nothing but the printer exercises the port type this stage. Widening it now
anyway, rather than at stage E, because a port carries a message server's payload and so needs exactly
the same treatment as an action — doing it once is one change to the representation, doing it twice is
two, and the second would have to reopen files the first had just settled.

### 5.3 Expressions, mirroring the DTR side

```
inductive GeneralBinaryOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | logicalAnd | logicalOr

inductive GeneralUnaryOp where
  | negate | logicalNot

inductive GeneralExpr where
  | intLiteral : Int → GeneralExpr
  | boolLiteral : Bool → GeneralExpr
  | stateVar : VarName → GeneralExpr
  | parameterVar : VarName → GeneralExpr
  | binary : LF.GeneralBinaryOp → GeneralExpr → GeneralExpr → GeneralExpr
  | unary : LF.GeneralUnaryOp → GeneralExpr → GeneralExpr
```

Constructor-for-constructor and operator-for-operator with DTR, which is what lets the translation of
expressions be a total structural map and its correctness theorem be an induction with no side
conditions.

### 5.4 The payload struct is DERIVED, never stored

A message server with two or more parameters needs a C++ struct, and the program needs a
`public preamble` declaring it. The struct list is **computed from the reactors**, not carried as a field
on `GeneralProgram`.

That follows stage C's own rule for effects, stated in `GeneralCppPrinter` lines 147–148: *"Deriving the
list from the body — instead of storing an `effects` field — is what makes it impossible to print an
effect the body does not produce, or to omit one it does."* The same argument applies exactly: a stored
struct list could declare a struct no action uses, or omit one an action needs, and both are printable.
Derived, neither is expressible.

Naming: `<ReactorName>_<ActionName>_Args`, fields in parameter order with the parameter's own name and
`int`/`bool` from its declared type. Derivable from the LF program alone — the printer never sees DTR.
This naming rule has **no paper basis**; the paper supplies no rule here, exactly as it supplies none for
port names (ledger P20). It is this project's choice and is recorded as such.

Action type selection, arity by arity:

| parameters | emitted action type | rationale |
|---|---|---|
| 0 | `: void` | unchanged from fixtures |
| 1 | `: int` or `: bool` | byte-identical to fixtures for the `int` case |
| ≥ 2 | `: <ReactorName>_<ActionName>_Args` | measured route A |

### 5.5 Reactor parameters — restoring Fig. 5's `ParamList?`

Gap 5 needs no new mechanism, it needs a restored one. Two fields:

```
structure GeneralReactor where
  name : ReactorName
  parameters : List LF.GeneralTypedParameter     -- new
  inputPorts : List LF.GeneralPortDecl
  outputPorts : List LF.GeneralPortDecl
  stateVariables : List LF.GeneralStateVariableDecl
  logicalActions : List LF.GeneralAction
  startupReaction : LF.GeneralReaction
  messageReactions : List LF.GeneralReaction

structure GeneralReactorInstance where
  name : ActorName
  reactorName : ReactorName
  arguments : List LF.GeneralValue               -- positional, one per reactor parameter
```

`GeneralProgram.instances` moves from `List LF.ReactorInstance` to `List LF.GeneralReactorInstance`;
`LF.ReactorInstance` itself is left untouched for the earlier families that use it.

Measured target forms, from the parameter probe: the declaration is
`reactor Configured(bound: int = 0, active: bool = false) {`, the instantiation is
`configuredOn = new Configured(bound=7, active=true)`, and a parameter is readable directly in a reaction
body with no trigger or extra declaration. Defaults come from `GeneralType.initialValue`, so the
declaration never needs the instance arguments and every parameter has a default.

`arguments` is **positional** while the emitted LF is **named**: the names come from the reactor's own
parameter list at print time. That is deliberate — positional is what the source has, and generating the
names from the single authoritative list means arity is the only thing that can disagree, which is one
well-formedness obligation rather than a possible mismatch between two independently stored name lists.

**The rejected alternative, recorded so it is not re-proposed:** emit one reactor per *instance*, inlining
that instance's arguments as constants. It would work and would need no parameter list. It is rejected
because Table III maps a reactive **class** to a reactor, and `GeneralProgram`'s docstring makes the
sharing load-bearing — several instances of one class share a single reactor declaration whose port set is
the union over its instances, which is the object §III-F's cost bound ranges over. Specializing per
instance would quietly change what that bound is about.

## 6. Printer changes, site by site

Named precisely so the review can check them and so the diff has no surprises. Line numbers are as of
`55dcdc4`.

**`renderGeneralType`, new.** `.int → "int"`, `.boolean → "bool"`. Sole owner of the two spellings; the
three hardwired `": int"` string literals at :204, :214 and :255 all become calls to it.

**`renderGeneralExpr` (:66) gains three arms.** `boolLiteral true → "true"`, `boolLiteral false →
"false"`; `binary` and `unary` fully parenthesized:

```
  | .binary op left right =>
      "(" ++ renderGeneralExpr left ++ " " ++ renderBinaryOp op ++ " "
          ++ renderGeneralExpr right ++ ")"
  | .unary op operand =>
      "(" ++ renderUnaryOp op ++ renderGeneralExpr operand ++ ")"
```

Operator spellings are C++'s, one for one: `+ - * / % == != < <= > >= && ||` and `- !`. The function
stays **total** — it returns `String`, not `Except String String`. No expression is unprintable, and that
is the point of widening.

**`renderInputPortDecl` (:199) and `renderOutputPortDecl` (:209)** take a `GeneralPortDecl` and render its
type. A port whose declared type is `.int` prints exactly the bytes it prints today.

**`renderGeneralStateDecl`** renders `= 0` for `int` and `= false` for `boolean`, so `state x: int = 0` is
unchanged.

**`renderGeneralActionDecl` (:240) loses its error case.** The arity-≥2 arm returns the struct name
instead of `.error`. Whether the function still needs `Except` at all is answered in §7.

**`renderGeneralParameterRead` (:310) loses two error cases** (:339, :360) and gains a multi-parameter
form. For arity ≥ 2 on an action:

```
    auto <action>_payload = *<action>.get();
    auto left = <action>_payload.left;
    auto right = <action>_payload.right;
```

One binder per parameter, so the body below can refer to parameters by their source names and the
translation of expressions needs no renaming pass.

**`renderGeneralStmt` (:88) loses its multi-payload refusal** (:124). `schedule` with arity ≥ 2 emits
`<action>.schedule(<Struct>{<e1>, <e2>}, <delay>);`.

**`renderGeneralProgram` (:604) gains a preamble block** when any action in any reactor has arity ≥ 2,
placed after `target Cpp` and before the first reactor. When no action has arity ≥ 2 — which includes the
current base program — **no preamble is emitted at all**, so the 32 pinned bytes do not move.

**`renderGeneralReactor` (:487) gains a parameter list on the header line.** With no parameters the header
is `"reactor " ++ name ++ " {"` exactly as today; with parameters it is
`"reactor " ++ name ++ "(" ++ intercalate ", " params ++ ") {"`, each parameter rendered as
`<name> ++ ": " ++ renderGeneralType <type> ++ " = " ++ renderInitialValue <type>`. The empty case must
stay byte-identical, since every existing fixture reactor is parameterless.

**`renderGeneralInstance` (:553) gains named arguments.** Today `"  " ++ name ++ " = new " ++ reactorName
++ "()"`. It becomes the same string with the arguments zipped against the reactor's parameter list into
`bound=7, active=true`. That means the function needs the *reactor*, not just the instance, so it takes the
reactor list (or a lookup) as an argument. A zero-argument instance prints `()` as before.

This is the one printer site where a lookup can fail: an instance may name a reactor that is not in the
program, or supply the wrong number of arguments. Both are well-formedness questions, and §8 says which
side of the total/partial line they land on rather than leaving the printer to invent an answer.

### 6.1 A naming-hygiene finding, recorded rather than solved

`<action>_payload` is a generated C++ identifier in the same scope as the source-derived parameter
binders, and nothing proves a source model cannot contain a message-server parameter or state variable
called `arithmetic_payload`. The existing repository has the same exposure — the payload family emits
`auto payload = *dispatch_action.get();` — so this is inherited, not introduced. It is recorded here as a
finding rather than fixed, because fixing it properly means a freshness condition over the union of all
source identifiers in a reactor, which is a well-formedness obligation and belongs with the other
uniqueness checks rather than inside a printer. Deriving the binder from the action name at least makes a
collision require a source identifier that mentions an action name, which is narrower than the inherited
bare `payload`.

## 7. The translation, function by function

One new file, `Relico/Translation/GeneralBasic.lean`, in `namespace Relico.Translation` beside its
siblings. It imports the DTR general syntax, the LF general syntax and `NameGeneration`.

**The naming layer already exists and stage D adds nothing to it.** `Relico/Translation/NameGeneration.lean`
defines `reactorNameFor` (class name verbatim), `actionNameFor` (`msg ++ "_action"`),
`startupReactionName` (`"startup"`) and `messageReactionNameFor` (`msg ++ "_reaction"`), and it already
proves `actionNameFor_injective` and `messageReactionNameFor_injective`. Stage D reuses all four unchanged;
the only new name in the whole stage is the payload struct of §5.4, which is a printer-side derivation and
never enters the LF syntax tree.

### 7.1 The total layer

Each of these is a plain function, no `Except`, exhaustive match, no wildcard:

| function | signature |
|---|---|
| `compileGeneralType` | `DTR.GeneralType → LF.GeneralType` |
| `compileGeneralValue` | `DTR.GeneralValue → LF.GeneralValue` |
| `compileGeneralBinaryOp` | `DTR.GeneralBinaryOp → LF.GeneralBinaryOp` — 13 arms |
| `compileGeneralUnaryOp` | `DTR.GeneralUnaryOp → LF.GeneralUnaryOp` — 2 arms |
| `compileGeneralExpr` | `DTR.GeneralExpr → LF.GeneralExpr` — 6 arms, structural recursion |
| `compileStateVariableDecl` | `DTR.GeneralStateVariableDecl → LF.GeneralStateVariableDecl` |
| `compileTypedParameter` | `DTR.GeneralTypedParameter → LF.GeneralTypedParameter` |
| `compileMessageServerAction` | `DTR.GeneralMessageServer → LF.GeneralAction` |
| `compileActorInstance` | `DTR.GeneralActorInstance → LF.GeneralReactorInstance` |

These are the functions §3's widening buys. Every one of them is an identity-shaped map, and that is the
strongest argument that the widening was the right call: after it, the data half of the translation has
**no failure cases at all**, so there is no diagnostic to write, no error string to test, and no
unreachable branch to justify. Before it, five of the nine could not be written.

`compileGeneralExpr` recurses on `.binary` and `.unary`; the other four arms are leaves. Totality is by
structural recursion and needs no termination argument.

`compileMessageServerAction` maps a message server to `⟨actionNameFor server.name, server.parameters.map
compileTypedParameter⟩` — the widened `GeneralAction` of §5 carries typed parameters, which is what makes
this total rather than an arity check.

### 7.2 The partial layer

Exactly one thing can fail in stage D, and it is the stage boundary itself:

```
def compileGeneralStmt :
    DTR.GeneralStmt →
    Except String LF.GeneralStmt
  | .assign target expr =>
      .ok (.assign target (compileGeneralExpr expr))
  | .send .selfTarget message arguments delay =>
      .ok (.schedule (actionNameFor message)
             (arguments.map compileGeneralExpr) delay)
  | .send (.knownRebec rebec) message _ _ =>
      .error (...)
```

The `.knownRebec` arm's message must name the stage that will implement it, not merely report a refusal.
Stage B's diagnostic style is the model. Wording:

```
  "send to known rebec '" ++ rebec.value ++ "'.'" ++ message.value ++ "' is an external send; "
    ++ "stage D translates self-sends only, and external sends are stage E"
```

`compileGeneralBody : DTR.GeneralBody → Except String (List LF.GeneralStmt)` is written by **explicit
top-level recursion**, not `mapM`, matching the house pattern in
`Relico/Translation/GlobalMultiStorePayloadBasic.lean` — `nil` and `cons` arms, so the two `@[simp]`
equations of §9 hold by `rfl` and order preservation is provable by induction rather than by unfolding a
monadic combinator.

`Except String` propagates outward from there: `compileMessageServerReaction`, `compileConstructor`,
`compileReactiveClass` and `compileModel` are all `Except`, and none of them introduces a *new* failure —
they only pass one along. That is a property worth stating as a theorem, and §9 does.

### 7.3 Reactions, reactors, program

`compileMessageServerReaction server` builds
`⟨messageReactionNameFor server.name, .logicalAction (actionNameFor server.name),
server.parameters.map (·.name), body, none⟩`.

`priority := none` **deliberately**, even though `GeneralMessageServer.priority` may be `some n` and
`GeneralReaction.priority` exists to receive it. Local message-server priority is realized in LF by
**reaction declaration order**, which is the one ordering hook the target actually gives us (measured:
declaration order decides same-tag order), and choosing that order is a sort over the message-server list
that stage G owns together with the actor-priority observable. Stage D emits declaration order = source
order and records the dropped priority as an explicit, tested divergence rather than half-wiring a field
whose meaning is not yet decided. A stage D that wrote `priority := some n` would look finished and be
unproved.

`compileConstructor ctor` produces the `startupReaction`:
`⟨startupReactionName, .startup, ctor.parameters.map (·.name), body, none⟩`. The constructor's parameters
become the **reactor's** parameters (§5.5), so the reaction's parameter list here names identifiers that
are in scope as reactor members — which is exactly the measured fact that a parameter is readable in a
reaction body with no trigger.

`compileReactiveClass cls` assembles the reactor: `reactorNameFor cls.name`;
`parameters := cls.constructor.parameters.map compileTypedParameter`;
`inputPorts := []` and `outputPorts := []`; `stateVariables := cls.stateVariables.map
compileStateVariableDecl`; `logicalActions := cls.messageServers.map compileMessageServerAction`;
`startupReaction`; `messageReactions := cls.messageServers.map compileMessageServerReaction` — the last two
under `Except`.

The two empty port lists are stage D's boundary made visible in one place. `knownRebecs` is **read but not
translated**: it contributes nothing to the reactor, and that is correct here, because a known rebec becomes
a port only when something sends on it, which is stage E. §8 states the accompanying obligation — that a
class with known rebecs is still translatable as long as no `.knownRebec` send occurs — because that is
what makes the fixtures with unused known rebecs pass rather than fail.

`compileModel model` returns `LF.GeneralProgram` with `reactors := model.classes.map compileReactiveClass`
(under `Except`), `instances := model.instances.map compileActorInstance`, and `connections := []`. Empty
connections is the same boundary from the other side: no external sends means no connections, and stage C's
connection layer sits unused and ready.

## 8. Totality and the refusal boundary

This repository's convention, stated in `Relico/LF/GeneralSyntax.lean` lines 84–91, is **translation total,
printer partial**. Stage D can hold to that almost exactly, and the exceptions are worth naming precisely,
because a refusal nobody can trigger is as bad as a missing one.

### 8.1 The translation refuses exactly one thing

`.send (.knownRebec _) _ _ _`. That is the entire refusal surface. Everything below is explicitly **not** a
failure, and each line is a claim the gate should test rather than a hope:

- a `boolean` state variable, parameter, or expression — §3's widening;
- any of the 13 binary or 2 unary operators, at any nesting depth;
- a message server with two or more parameters, of mixed types — §5.4;
- a class that declares **known rebecs it never sends on** — the corpus contains these, and refusing them
  would make stage D narrower than the fragment it must accept;
- a class with no state variables, no message servers, or an empty constructor body — all three are
  permitted by `GeneralReactiveClass`'s own docstring as considered divergences;
- two instances of one class with different constructor arguments — §5.5;
- a self-send with a non-zero delay.

### 8.2 The one place a *new* partiality appears, and how it is contained

§6 named it: rendering an instance's named arguments needs the reactor's parameter names, so
`renderGeneralInstance` must look the reactor up, and it can fail two ways — unknown reactor name, or an
argument count that does not match the parameter count.

The printer is already `Except String`, so this costs no new machinery. The decision that matters is that it
must **refuse rather than truncate**. A `zip` would silently drop surplus arguments and quietly emit a
program that compiles and is wrong, which is the worst outcome available here.

Both conditions then belong in `Relico/LF/GeneralWellFormed.lean` as a predicate over the program — every
instance names a declared reactor, and its argument count equals that reactor's parameter count — so that for
well-formed programs the printer's refusal is unreachable.

**And the predicate must be asserted in the gate, not merely defined.** This project has already fallen into
that trap once: stage B found `PrioritiesDistinct` defined in the LF well-formedness file and **never
enforced anywhere**, which is indistinguishable from not having it. Stage D's predicate gets at least one
positive and one negative assertion in the bridge test main, or it does not count as done.

### 8.3 Where DTR well-formedness is assumed, and where it is not

`compileGeneralStmt` translates a self-send to `schedule (actionNameFor message)` **without checking that a
message server of that name exists on the class**. That is not an oversight: it is `GeneralWellFormed`'s job,
and duplicating the check inside the translation would create a second source of truth that can disagree
with the first.

The consequence is precise and worth stating rather than hiding — the translation of an ill-formed model may
schedule an action that no reaction triggers on, which `lfc` accepts and which then simply never fires. So
the correctness statements of §9 are conditional on DTR well-formedness, and that hypothesis appears in the
statements themselves, not in a comment above them. Stage D need not *prove* the connection to be honest
about it.

Note also what the translation could not check even if it wanted to: arity agreement between a send's
argument list and the target message server's parameter list. The action carries typed parameters and the
`schedule` carries expressions, and nothing in `LF.GeneralStmt` ties the two lists together. That is a gap in
the **representation**, not in the checking, and §10 records it as an open question rather than letting §9's
theorems appear to close it.

## 9. Theorems owed, and the stage D gate

### 9.1 The structural lemmas, in the house pattern

`Relico/Translation/GlobalMultiStorePayloadBasic.lean` fixes the shape: `@[simp]` `_nil` and `_cons`
equations proved by `rfl`, a `_keys` lemma by list induction closed with `congrArg`, and a `_topology`
lemma by `rfl`. Stage D owes the same four shapes over its own recursions:

| theorem | statement | proof |
|---|---|---|
| `compileGeneralBody_nil` | `compileGeneralBody [] = .ok []` | `rfl` |
| `compileGeneralBody_cons` | the `cons` equation in terms of `compileGeneralStmt` | `rfl` |
| `compileModel_connections` | a successful `compileModel` has `connections = []` | `rfl` |
| `compileReactiveClass_ports` | a successful reactor has `inputPorts = []` and `outputPorts = []` | `rfl` |
| `compileModel_reactorNames` | reactor names are `model.classes.map (reactorNameFor ·.name)` | induction + `congrArg` |

The last three are stage D's boundary stated as arithmetic rather than as prose: they are what makes "no
ports, no connections" a checked property of the translation instead of a claim in this document. When stage
E arrives, `compileModel_connections` is the theorem that must *change*, which is the cheapest possible alarm
that the boundary has moved.

### 9.2 The order-preservation lemmas, which are load-bearing later

```
theorem compileReactiveClass_actionNames :
    ... (compileReactiveClass cls).logicalActions.map (·.name)
      = cls.messageServers.map (fun s => actionNameFor s.name)

theorem compileReactiveClass_reactionNames :
    ... (compileReactiveClass cls).messageReactions.map (·.name)
      = cls.messageServers.map (fun s => messageReactionNameFor s.name)
```

These look like bookkeeping and are not. Reaction **declaration order** is the only deterministic ordering
hook the target gives us (measured: swapping two reaction declarations swaps their same-tag execution order),
so stage G's priority work will be a permutation of `messageReactions`. Proving now that stage D's order *is*
source order gives stage G a fixed starting point to permute away from, and makes any accidental reordering
in between a failing proof rather than a silent behavioural change.

Two more, cheap and worth having: `compileActorInstance` preserves argument count and order, and
`(compileGeneralValue v).typeOf = compileGeneralType v.typeOf` — the type-preservation lemma mirroring DTR's
existing `@[simp] typeOf_initialValue`. The second requires an LF-side `GeneralValue.typeOf`, which §5's
widening should define for exactly this reason.

### 9.3 The theorem that pins the refusal surface

```
theorem compileModel_isOk_iff_no_external_send :
    (compileModel model).isOk ↔ ∀ class ∈ model.classes, ∀ stmt ∈ (all bodies of class),
      ¬ stmt.isExternalSend
```

Both directions matter, and for different reasons. Left-to-right says stage D never accepts something it
cannot represent. **Right-to-left is the one that earns its keep:** it says the refusal is *exactly* the
external send and nothing broader — no accidental refusal of a bool, a nested operator, a three-parameter
message server or a parameterised instance. §8.1 lists seven things that must not fail; this direction proves
all seven at once instead of testing them one at a time, and it will keep proving them as the fragment grows.

If the full iff proves expensive, the honest fallback is to prove right-to-left in full and state
left-to-right for the shapes the gate exercises — not to weaken the statement quietly.

### 9.4 The gate

Both gates must run, because stage D edits four files stage C committed at `55dcdc4`.

**`GENERAL_LEAN_GATE_OK`.** Predictions to be written down *before* the run, as stage C did:

- `lake build` job count. The rule is job count = import closure of `Relico.lean` + 2, currently **506**.
  Stage D adds exactly one file to that closure, `Relico/Translation/GeneralBasic.lean`, so the prediction is
  **507**. If the observed number is anything else, the cause is a missing or extra import, and that is
  diagnosed before anything else is believed.
- `EXPECTED_PRINTER_ASSERTIONS` at `frontend/check-general-lean.sh:182` rises from **25**. The new count is
  fixed when the assertions are written and stated in the same message as the run, never adjusted afterwards
  to match what happened.

New assertions the gate owes, at minimum: every operator spelling round-tripped through
`renderGeneralExpr`; full parenthesization of `left + right * 2 - 1`; `state flag: bool = false`; a bool port;
a `: void`, a `: int` and a struct action type; the `<action>_payload` multi-binder form; a parameterised
reactor header and a `new R(bound=7, active=true)` instance; the §8.2 well-formedness predicate **positive and
negative**; and the external-send refusal, asserted on its **message text**, so that the diagnostic keeps
naming stage E rather than degrading into a bare `.error`.

**`GENERAL_LF_TARGET_OK`.** Re-running it unchanged proves only that the widening did not *break* the existing
base program — which is necessary (the 32 pinned bytes must not move: the base program has no arity-≥2 action
and no reactor parameters, so no preamble and no parameter list are emitted) but proves nothing about the new
capability.

So the gate gains a **second** emitted program and a second selector, `emit-widened`, alongside the existing
`emit-program`: a program that uses a bool state variable, a nested parenthesized arithmetic expression, a
two-parameter action with its derived struct, and two instances of one parameterised reactor with different
arguments. Both are compiled by real `lfc` and both binaries are run. The base program stays byte-pinned;
the widened one is where the new bytes are proved. Adding capability to the printer while leaving the target
gate exercising only the old capability would be the exact failure mode the `lfc` gate was created to end.

## 10. What this design found, and what it cannot decide alone

### 10.1 Findings, for the ledger

The corrections ledger ran P1–P22 for the paper plus F1–F20 from stage B when this document was written,
and it then lived under a gitignored `tmp/` path — which meant the project's most reusable artefact was the
one thing a fresh clone did not get. **That is resolved since, 2026-08-23:** the paper series is tracked at
`docs/PAPER_CORRECTIONS.md` and runs through **P23**, and the findings series continued past stage B into
`docs/STAGE_E_FINDINGS.md`, which holds **F34–F57**. A fresh clone gets both. Stage D's findings are written here in the meantime, numbered **F21–F29**, and graduating the
ledger into the repository is a task in its own right rather than something to keep postponing.

**These findings were numbered D1–D9 when this document was first committed, and that was a collision.**
`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md` already defines a `D1–D9` series meaning *divergences
from the paper's DTR fragment restrictions*, and those labels are cited from Lean source —
`Relico/DTR/GeneralWellFormed.lean` says *"One class satisfies D6"* at line 92 and *"D8 for one argument
list"* at line 108. The old D8 there is *"instance arguments may be boolean literals, not only integer
literals"*, which is close enough in subject matter to this document's original D8 to mislead a reader
badly. Continuing stage B's single findings series as F21–F29 is the fix; the mapping was
D1→F21 … D9→F29, applied uniformly, and no reference to the fragment series was touched.

Findings about **this repository**:

- **F21.** The LF half of the "general" family was assembled from an earlier integer-only, single-payload,
  parameterless family. Five distinct gaps (§2), one cause. "General" described its ports and connections,
  never its data.
- **F22.** Stage C dropped Fig. 5's `Reactor ::= reactor R (ParamList?)` production while quoting that very
  grammar line in its own docstring, so two instances of one class with different constructor arguments are
  currently indistinguishable in LF (§5.5).
- **F23.** `GeneralCppPrinter`'s three refusals saying *"the current C++ printer foundation supports at most one
  integer payload"* describe **our** limit and not the target's. Measured: a preamble struct and a
  `{= std::pair<int,int> =}` code-block type both compile, run and carry their values, including a mixed
  `bool` field. The comment is accurate about the foundation and misleading about the cause; it should be
  reworded when the refusal is removed.
- **F24.** A correction to our own record: `-Wunused-private-field` fires only for a field neither read **nor**
  written. Stage C's warning was about a state variable no reaction touched at all. The warning is narrower
  than previously recorded — still reachable, so the gate's non-fatal-warning policy stays justified.
- **F28, corrected during implementation — the original wording was wrong.** This document first claimed that
  arity agreement between a `schedule` and its action is *"not merely unchecked but unstateable at the LF
  level"*. Reading the source refutes it: `LF/GeneralWellFormed.lean` `stmtWellFormed` lines 154–158 already
  require `declared.parameters.length == arguments.length`, so arity **is** checked for any program that
  passed well-formedness, and stage D inherits that guarantee rather than owing it. The claim survives only
  in the weaker form that the *type* `GeneralStmt` does not relate the two lists, which is true of every
  name-resolution obligation in this layer and is not a finding on its own.
  What is genuinely open is *type* agreement: an argument whose type differs from its declared parameter's
  passes that check. Closing it needs a typing judgment on `LF.GeneralExpr`, which in turn needs a reaction's
  parameters to carry types — deliberately not done, since their types are already fixed by the action the
  reaction triggers on and duplicating them creates a second version of the same fact. Filed in this
  narrowed form, and the wrong version is left visible above rather than quietly rewritten, because a design
  document that silently repairs itself is not evidence of anything.
- **F29.** The generated binder `<action>_payload` shares a C++ scope with source-derived identifiers.
  Inherited, not introduced — the payload family emits a bare `auto payload = …` — and properly fixed by a
  freshness condition in well-formedness, not in a printer (§6.1).

Findings about **the paper**:

- **F25.** The paper supplies no naming rule for a multi-value payload carrier. §5.4's
  `<ReactorName>_<ActionName>_Args` is this project's invention, exactly like the port-naming rule of P20. It
  is filed as a finding so that the rule is visibly ours rather than silently attributed to Table III.
- **F27.** Local message-server priority appears in neither SOS table and the paper gives no tie rule, so what
  a translation should *do* with `msgsrv m(...) : 3` has no source of truth. Stage D therefore drops it
  deliberately (§7.3) rather than guessing, and the drop is itself the divergence.
- **F26, provisional and not yet filed.** Whether Fig. 5's `ActionDecl` production admits a *typed* action at
  all, and whether it admits more than one payload value, has **not** been checked against the PDF in this
  session. It is written down as an open check, not as a finding, because filing a paper fault on an unread
  production is exactly the failure this project's trust order exists to prevent. It must be read before F26
  is claimed either way.

### 10.2 Open questions — these are decisions, not tasks

1. **Approve widening the LF side.** It edits four files stage C committed at `55dcdc4`
   (`LF/GeneralSyntax.lean`, `LF/GeneralWellFormed.lean`, `LF/GeneralCppPrinter.lean` and the bridge test
   main) and re-runs both gates. The alternative — restrict stage D's domain to integers and simple
   expressions — is dead on evidence, not on taste: `frontend/fixtures/general/expressions.rebeca` is a
   committed **positive** fixture of this family using every operator and a boolean, its parser JSON carries
   18 binary / 3 unary / 2 boolLiteral nodes, the elaborator constructs them, and DTR well-formedness
   restricts expressions not at all. A restricted stage D would refuse this repo's own frontend on this
   repo's own fixture (§3).
2. **Approve the second target-gate program.** `emit-widened` costs one more `lfc` compile and one more binary
   run per gate invocation — a real cost in Mac round trips. Declining it leaves the widened printer output
   never compiled by a real compiler, which is the situation the `lfc` gate was created to end (§9.4).
3. **Approve dropping local message-server priority to stage G** (`priority := none`), on the grounds that
   realizing it means choosing a reaction declaration order and the paper supplies no tie rule (F27).
4. **Confirm P20 stays deferred.** Stage D emits no ports, so the port-naming disagreement between Fig. 1b
   (`receiveReading`) and Fig. 2b (`readingFromTemp`) does not block it. It blocks E and F, and it is a paper
   decision that only you can make.
5. **Decide whether F25 and F27 are filed as paper findings or as project conventions.** Both are places where
   we must invent a rule the paper does not give. Filing them makes the paper revisable, which is the stated
   goal; not filing them makes this document the only record.

Stage D writes no Lean until this design is approved — stages B and C each had a reviewed design first, and
both were better for it. On approval the order is: widen `LF/GeneralSyntax.lean`, then
`LF/GeneralWellFormed.lean`, then `LF/GeneralCppPrinter.lean`, then `Translation/GeneralBasic.lean`, then the
bridge test main and the two gate scripts — syntax before its printer, printer before its translation, gates
last — and the landing sequence is again commit, then push, then remote-verify, as three separate steps.
