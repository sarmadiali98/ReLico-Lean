import Relico.LF.StoreSyntax

set_option autoImplicit false

namespace Relico
namespace LF

/-!
The general generated-LF syntax: ports, connections, and a main reactor holding
several instances.

Every earlier LF family in this development has exactly one reactor and exactly
one instance, so nothing in it can express the two structures Table III's
`knownrebecs ↦ "port declarations and connections in main"` row requires. This
family adds them, and stage D widens its value domain. It still does not add
control flow, and it still does not touch `Relico.Payload`, which is load-bearing
for the proofs the earlier families already carry.

The widening was forced by evidence rather than chosen for symmetry. The LF half of
this family was assembled from an earlier integer-only, single-payload,
parameterless family, so "general" described its ports and connections and never
its data: there was no type at all, the printer hardwired the string `": int"` in
three places, payload arity above one was refused, and Fig. 5's `ParamList?` was
missing. Meanwhile `frontend/fixtures/general/expressions.rebeca` is a committed
*positive* fixture of this very family using every arithmetic and boolean operator
and a `boolean` state variable, the elaborator really constructs those nodes, and
DTR well-formedness restricts expressions not at all. Restricting the translation's
domain instead would have refused this repository's own frontend on this
repository's own fixture. The reasoning is recorded in `docs/STAGE_D_DESIGN.md` §3.

The shape difference worth naming is that a `GeneralProgram` holds a *list* of
reactors and a separate *list* of instances, rather than one reactor paired with
one instance. That is not a convenience. Several instances of one reactive class
must share a single reactor declaration, because that is what LF does and what
the paper's Fig. 2b prints; and it means the port set of a reactor is the union
over its instances rather than a per-instance thing. Making the program a pair of
lists is what stops that union from being expressible any other way.

Connections are named by *instance*, not by reactor. `sender0.out -> receiver0.in`
is a statement about two instances, and a connection between reactors would not
have a meaning in LF at all.

The `after` delay on a connection is a required field, not an `Option`. Fig. 5
spells it `(after delay)?`, but SS III-E states that a delay-free connection is
precisely what produces the causality loops `lfc` rejects, so the optional form is
one the translator must never emit. Recording that in the type makes it
unrepresentable rather than merely unused. The divergence is filed as P19.
-/

/--
A declared type in generated LF.

Two constructors, mirroring `DTR.GeneralType`. The mirror is deliberate and the
translation of types is therefore an identity-shaped map with no failure case; a
type the DTR side can write and this side cannot would be a refusal the translation
would have to carry a diagnostic for.

`int` and `boolean` are the Lean-side names, and they are *not* the emitted
spellings. LF writes `int` and `bool`, and the single place that knows this is
`renderGeneralType` in the printer. Keeping the emitted string out of the syntax
tree is what let stage D remove three hardwired `": int"` literals rather than add a
fourth.

Both spellings are measured, not assumed: `state flag: bool = false`, a `bool`-typed
port and a `bool`-typed action payload all compile and run under real `lfc 0.11.0`.
-/
inductive GeneralType where
  | int

  | boolean

deriving Repr, DecidableEq, BEq, Inhabited

/--
A value in generated LF.

Needed because an instance's constructor arguments are values rather than
expressions: `new Configured(bound=7, active=true)` carries `7` and `true`, and
nothing about an instance argument is an expression over state.
-/
inductive GeneralValue where
  | int :
      Int →
      GeneralValue

  | bool :
      Bool →
      GeneralValue

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralValue

/--
The type of a value.
-/
def typeOf :
    LF.GeneralValue →
    LF.GeneralType

  | .int _ =>
      .int

  | .bool _ =>
      .boolean

/--
A value has an expected type.

Defined as `typeOf` followed by decidable equality rather than as a second pattern
match over value and type together, which is how `DTR.GeneralValue.hasType` is
written. One pattern match means the two cannot drift: a definition that matched
independently could accept a pair `typeOf` disagrees with, and nothing would notice.

Unlike the DTR side, this exists because a caller needs it —
`GeneralProgram.instanceArgumentsMatch` — and not for symmetry. An earlier draft of
this file recorded that no `hasType` was wanted here precisely because it would have
no caller; writing the instance-argument check gave it one.
-/
def hasType
    (value : LF.GeneralValue)
    (expected : LF.GeneralType) :
    Bool :=
  value.typeOf == expected

end GeneralValue

namespace GeneralType

/--
The value a declaration of this type starts at.

This is why `GeneralStateVariableDecl` carries a type and no initial value. A stored
initial value could disagree with its own declared type — `boolean` beside `0` is
representable and printable — whereas deriving it makes the disagreement
unstateable. The DTR side already fixes these two choices, so the translation of a
state variable stays an identity-shaped map.

There is deliberately no separate initial-value field to disagree with this, and the
`hasType` predicate that sits beside `typeOf` above is here because the
instance-argument check consults it, not for symmetry with the DTR side.
-/
def initialValue :
    LF.GeneralType →
    LF.GeneralValue

  | .int =>
      .int 0

  | .boolean =>
      .bool false

end GeneralType

/--
The type of a type's own initial value is that type.

The mirror of `DTR.GeneralType.typeOf_initialValue`, and the reason it is worth
proving on this side too is that stage D's type-preservation lemma composes the two:
a DTR declaration and its translation must start at values of corresponding types,
and this is the LF half of that statement.
-/
@[simp]
theorem typeOf_initialValue
    (declaredType : LF.GeneralType) :
    (LF.GeneralType.initialValue declaredType).typeOf = declaredType := by

  cases declaredType

  · rfl

  · rfl

/--
A binary operator in generated LF.

Thirteen constructors, mirroring `DTR.GeneralBinaryOp` one for one, so
`compileGeneralBinaryOp` is total.

No precedence and no associativity is recorded here, and none is needed: the printer
fully parenthesizes every operator application, so the emitted C++ cannot depend on
a precedence claim this development has not verified. The fixture
`accumulator = left + right * 2 - 1;` is exactly the case that would punish a
printer that emitted bare infix.

The operator spellings themselves needed no probe and never will. Every reaction
body is emitted inside `{= … =}`, where the text is verbatim C++, so `+ - * / %`,
`== != < <= > >=` and `&& || !` are guaranteed by the target language rather than by
LF. The only LF-level risk was ever the *type* positions, and those are measured.
-/
inductive GeneralBinaryOp where
  | add

  | sub

  | mul

  | div

  | mod

  | eq

  | ne

  | lt

  | le

  | gt

  | ge

  | logicalAnd

  | logicalOr

deriving Repr, DecidableEq, BEq, Inhabited

/--
A unary operator in generated LF.

Mirroring `DTR.GeneralUnaryOp`. `negate` is arithmetic negation and `logicalNot` is
boolean negation; both appear in the committed fixture, as `-left` and as
`!(first && second) || true`.
-/
inductive GeneralUnaryOp where
  | negate

  | logicalNot

deriving Repr, DecidableEq, BEq, Inhabited

/--
A general expression in generated LF.

Six constructors: the three the payload family already carried, plus the boolean
literal and the two operator forms stage D added. There is
no port-read expression, and that is a measured omission rather than an
oversight: the paper never exhibits one, because every receiving reaction in both
of its figures has an empty body — Fig. 1b line 16 and Fig. 2b lines 28 and 31
are all `// Process received value`. Binding an arriving value to a formal
parameter is the same problem `renderParameterRead` already solves for actions,
and it belongs with the external-send translation, where there is a source
construct to bind.

There is no evaluator beside this type either, though
`MultiStorePayloadSyntax.lean` puts one beside its expressions. Nothing in this
family consults one: well-formedness is a name-resolution check and printing is
syntactic. Semantics for the general family is a later stage, and that is where an
evaluator acquires a caller. Shipping one now would be dead code, which is a thing
this project has already had to write findings about.

The asymmetry with `DTR.GeneralExpr` that this docstring used to record as an open
debt is **closed**, and closed the way the debt itself demanded: in the open, by
widening this type rather than by restricting the translation's domain. The old
argument for waiting was that no printer in this development could emit an operator,
so a widened expression would be a construct nothing could print. Stage D removes
that objection by teaching the printer operators in the same change, which is why
the two halves land together and neither is dead code. `docs/STAGE_D_DESIGN.md` §3
records the evidence that decided it, and §5.3 the shape.
-/
inductive GeneralExpr where
  | intLiteral :
      Int →
      GeneralExpr

  | boolLiteral :
      Bool →
      GeneralExpr

  | stateVar :
      VarName →
      GeneralExpr

  | parameterVar :
      VarName →
      GeneralExpr

  | binary :
      LF.GeneralBinaryOp →
      GeneralExpr →
      GeneralExpr →
      GeneralExpr

  | unary :
      LF.GeneralUnaryOp →
      GeneralExpr →
      GeneralExpr

deriving Repr, DecidableEq, BEq, Inhabited


/--
A general reaction statement.

`setPort` and `schedule` both take a list of expressions, and stage E is what made
them agree. Stage C and stage D gave `setPort` exactly one expression, following
Fig. 5's `LFStmt ::= outPort([Expr])?.set(Expr);`, which admits one value and no
more. That reading is faithful to the grammar and still wrong for this translation:
an external send to `msgsrv report(int identifier, boolean urgent)` carries two
values, the receiving reactor's input port must be able to hold them, and the
measured target accepts exactly that — probe `struct_as_port_type` compiled a
program-level `public preamble` struct used as a **port** type under real
`lfc 0.11.0` and delivered its fields. So the arity restriction was the paper's
grammar rather than the target's capability, and stage E lifts it on the port side
the same way stage D lifted it on the action side, per
`docs/STAGE_E_DESIGN.md` §5.1. The divergence from Fig. 5 is deliberate and filed
as a finding rather than absorbed silently.

A typed logical action's payload arity follows the parameter list of the
message server it was derived from. `schedule`'s argument list is unbounded, and as of stage D that is genuinely
supported rather than merely representable. This docstring used to say that a
multi-value payload was refused in the C++ printer, and the printer said the same in
three places — *"the current C++ printer foundation supports at most one integer
payload"*. That was **our** limitation and not the target's, which is a measured
correction rather than an opinion: a program-level `public preamble` struct carrying
three fields including a `bool`, and a code-block action type
`{= std::pair<int,int> =}`, were compiled separately by real `lfc 0.11.0` and both
ran and delivered their values. Stage D removes the refusal and emits a struct
derived from the action's own parameter list, per `docs/STAGE_D_DESIGN.md` §5.4. The
finding is filed as F23.

What is *not* fixed, and is recorded rather than hidden: nothing in this **type**
relates this argument list to the parameter list of the action it names. The
well-formedness layer does — `stmtWellFormed` requires
`declared.parameters.length == arguments.length` — so arity disagreement is caught for
any program that passed the predicate, and a printer may rely on it only for such
programs. The same now holds of `setPort` against its port's payload arity. What
remains genuinely open after stage D is *type* agreement: an argument
whose type differs from the declared parameter's is well-formed by that check, and
checking it would require typing a reaction's parameters, which this family
deliberately does not do. The corrected finding is F28.

The delay on `schedule` is a `Delay` rather than an optional one, matching the DTR
side: an absent `after` has already had the zero default applied by the time a
statement exists. `setPort` carries **no** delay, and that is not an omission: on the
DTR side a send's `after` is a property of the statement, and on the LF side it is a
property of the connection the value travels along. Stage E keys ports by send site
precisely so that each statement's delay has its own connection to sit on, which is
where the delay of a `setPort` is recorded — see `docs/STAGE_E_DESIGN.md` §6.

There is `if` but no `for`. Fig. 5's `LFStmt` has both. Stage H adds the conditional on
**both sides at once**, which is what the earlier note here required: an LF conditional alone
would have been a construct nothing can produce, and it is produced now because
`DTR.GeneralStmt.ifThenElse` exists and `Translation.compileGeneralStmt` compiles into it.
`for` stays absent; it unlocks no benchmark and is out of scope.

`localDecl` exists as of stage I and, for now, is a construct nothing can produce — which is
why it is added **before** the translation that will produce it, not after. Stage H's ordering
lesson was that a constructor whose producer does not exist yet is unambiguous, while a guard
admitting a construct the translator refuses is the shape that made
`exists_compileGeneralBody` false once already; so the LF side lands first, the DTR
constructor is already in place refusing at every guard, and S-I3 is the layer that connects
them. The declaration carries `LF.GeneralType` rather than the DTR side's type so that
`renderGeneralType` renders it directly. It is the first statement constructor on either side
whose meaning includes a **scoping** effect, and the LF side deliberately records none of it:
scope is the source elaborator's concern, by the stage I rulings, and the compiled artefact
expresses a local exactly the way C++ does — a block-scoped declaration in a reaction body.

That earlier note also recorded what flatness bought: *"with flat bodies one statement
performs at most one `set()` per firing, so no reaction can set one port twice at one tag."*
That is no longer automatic, and the replacement is **static and conservative**: a conditional
contributes the ports of *both* branches to the compiled body, so a port set in each arm counts
as appearing twice even though only one arm runs. `LF.setPortNamesOfBody` recurses into both
branches accordingly. Port uniqueness stays a property of the compiled **artifact** rather than
of an execution trace, which keeps `Nodup` decidable from the body alone and keeps F50's
guard-relative theorem meaningful. A path-dependent reading was considered and rejected: it
would make the property a statement about runs, which `setPortNamesOfBody` cannot express and
no guard could check.

`trace` carries the literal tag that the C++ printer writes as target output.
It has no effect-list entry and no runtime label in this milestone: the output
is deliberately owned by the generated reaction body.
-/
inductive GeneralStmt where
  | assign :
      VarName →
      LF.GeneralExpr →
      GeneralStmt

  | trace :
      String →
      GeneralStmt

  | schedule :
      ActionName →
      List LF.GeneralExpr →
      Delay →
      GeneralStmt

  | setPort :
      PortName →
      List LF.GeneralExpr →
      GeneralStmt

  | ifThenElse :
      LF.GeneralExpr →
      List GeneralStmt →
      List GeneralStmt →
      GeneralStmt

  | localDecl :
      VarName →
      LF.GeneralType →
      LF.GeneralExpr →
      GeneralStmt

deriving Repr, BEq, Inhabited

/--
A statement sequence.

The *container* stays `List`, exactly as on the DTR side; what stage H changed is the
element type, which is now recursive through `GeneralStmt.ifThenElse`. The earlier note
here predicted that the stage admitting branching *"has to change this type, and that
change is a build error at every function that walks a body rather than a silent default
branch"*, and that is what happened: every traversal of a body broke loudly.
-/
abbrev GeneralBody :=
  List LF.GeneralStmt

/-
Decidable equality for a target statement and for a target body is written by hand below.
The docstrings sit on the two definitions rather than on the `mutual` block, because a
`mutual` block does not accept one.
-/
mutual

/--
Decide equality of two target statements.

Hand-written for the same toolchain reason as `DTR.decEqGeneralStmt`:
`GeneralStmt.ifThenElse` carries `List GeneralStmt`, which makes the type a *nested*
inductive, and Lean 4.32's `DecidableEq` deriving handler does not apply to one. `Repr`,
`BEq` and `Inhabited` still derive, so only this instance is manual.

Mutually recursive with `decEqGeneralBody` because the type is, and exhaustive over both
arguments with no wildcard on the pair, so a later statement form breaks here loudly rather
than being decided `false`.
-/
def decEqGeneralStmt :
    (first second : LF.GeneralStmt) →
    Decidable (first = second)

  | .assign firstName firstValue, .assign secondName secondValue =>
      if hName : firstName = secondName then
        if hValue : firstValue = secondValue then
          .isTrue (by subst hName; subst hValue; rfl)
        else
          .isFalse (by simp [hValue])
      else
        .isFalse (by simp [hName])

  | .assign _ _, .trace _ => .isFalse (by simp)
  | .assign _ _, .schedule _ _ _ => .isFalse (by simp)
  | .assign _ _, .setPort _ _ => .isFalse (by simp)
  | .assign _ _, .ifThenElse _ _ _ => .isFalse (by simp)
  | .assign _ _, .localDecl _ _ _ => .isFalse (by simp)

  | .trace firstTag, .trace secondTag =>
      if hTag : firstTag = secondTag then
        .isTrue (by subst hTag; rfl)
      else
        .isFalse (by simp [hTag])

  | .trace _, .assign _ _ => .isFalse (by simp)
  | .trace _, .schedule _ _ _ => .isFalse (by simp)
  | .trace _, .setPort _ _ => .isFalse (by simp)
  | .trace _, .ifThenElse _ _ _ => .isFalse (by simp)
  | .trace _, .localDecl _ _ _ => .isFalse (by simp)

  | .schedule firstAction firstArguments firstDelay,
    .schedule secondAction secondArguments secondDelay =>
      if hAction : firstAction = secondAction then
        if hArguments : firstArguments = secondArguments then
          if hDelay : firstDelay = secondDelay then
            .isTrue
              (by
                subst hAction
                subst hArguments
                subst hDelay
                rfl)
          else
            .isFalse (by simp [hDelay])
        else
          .isFalse (by simp [hArguments])
      else
        .isFalse (by simp [hAction])

  | .schedule _ _ _, .assign _ _ => .isFalse (by simp)
  | .schedule _ _ _, .trace _ => .isFalse (by simp)
  | .schedule _ _ _, .setPort _ _ => .isFalse (by simp)
  | .schedule _ _ _, .ifThenElse _ _ _ => .isFalse (by simp)
  | .schedule _ _ _, .localDecl _ _ _ => .isFalse (by simp)

  | .setPort firstPort firstArguments, .setPort secondPort secondArguments =>
      if hPort : firstPort = secondPort then
        if hArguments : firstArguments = secondArguments then
          .isTrue (by subst hPort; subst hArguments; rfl)
        else
          .isFalse (by simp [hArguments])
      else
        .isFalse (by simp [hPort])

  | .setPort _ _, .assign _ _ => .isFalse (by simp)
  | .setPort _ _, .trace _ => .isFalse (by simp)
  | .setPort _ _, .schedule _ _ _ => .isFalse (by simp)
  | .setPort _ _, .ifThenElse _ _ _ => .isFalse (by simp)
  | .setPort _ _, .localDecl _ _ _ => .isFalse (by simp)

  | .ifThenElse firstCondition firstThen firstElse,
    .ifThenElse secondCondition secondThen secondElse =>
      if hCondition : firstCondition = secondCondition then
        match decEqGeneralBody firstThen secondThen,
              decEqGeneralBody firstElse secondElse with
        | .isTrue hThen, .isTrue hElse =>
            .isTrue
              (by
                subst hCondition
                subst hThen
                subst hElse
                rfl)
        | .isFalse hThen, _ => .isFalse (by simp [hThen])
        | _, .isFalse hElse => .isFalse (by simp [hElse])
      else
        .isFalse (by simp [hCondition])

  | .ifThenElse _ _ _, .assign _ _ => .isFalse (by simp)
  | .ifThenElse _ _ _, .trace _ => .isFalse (by simp)
  | .ifThenElse _ _ _, .schedule _ _ _ => .isFalse (by simp)
  | .ifThenElse _ _ _, .setPort _ _ => .isFalse (by simp)
  | .ifThenElse _ _ _, .localDecl _ _ _ => .isFalse (by simp)

  | .localDecl firstName firstType firstValue,
    .localDecl secondName secondType secondValue =>
      if hName : firstName = secondName then
        if hType : firstType = secondType then
          if hValue : firstValue = secondValue then
            .isTrue
              (by
                subst hName
                subst hType
                subst hValue
                rfl)
          else
            .isFalse (by simp [hValue])
        else
          .isFalse (by simp [hType])
      else
        .isFalse (by simp [hName])

  | .localDecl _ _ _, .assign _ _ => .isFalse (by simp)
  | .localDecl _ _ _, .trace _ => .isFalse (by simp)
  | .localDecl _ _ _, .schedule _ _ _ => .isFalse (by simp)
  | .localDecl _ _ _, .setPort _ _ => .isFalse (by simp)
  | .localDecl _ _ _, .ifThenElse _ _ _ => .isFalse (by simp)

/--
Decide equality of two target bodies.

A `List` decision procedure specialised to this element type rather than an appeal to the
generic `List` instance, because the generic one needs `DecidableEq LF.GeneralStmt` as an
instance argument, which is exactly what `decEqGeneralStmt` is defining.
-/
def decEqGeneralBody :
    (first second : LF.GeneralBody) →
    Decidable (first = second)

  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)

  | firstHead :: firstTail, secondHead :: secondTail =>
      match decEqGeneralStmt firstHead secondHead,
            decEqGeneralBody firstTail secondTail with
      | .isTrue hHead, .isTrue hTail =>
          .isTrue (by subst hHead; subst hTail; rfl)
      | .isFalse hHead, _ => .isFalse (by simp [hHead])
      | _, .isFalse hTail => .isFalse (by simp [hTail])

end

instance : DecidableEq LF.GeneralStmt := decEqGeneralStmt

/--
A typed parameter, used for both message-server payloads and reactor parameters.

One structure for both because both are the same thing on the DTR side —
`DTR.GeneralTypedParameter` serves a message server's formals and a constructor's
formals alike — and mirroring that keeps `Translation.compileGeneralTypedParameter` a
single identity-shaped map.

It is declared here, ahead of the port declaration, because a port's payload is a
parameter list whenever it carries more than one value. Stage D placed it after the
port declaration, when no port could reference it.
-/
structure GeneralTypedParameter where
  name :
    VarName

  declaredType :
    LF.GeneralType

deriving Repr, DecidableEq, BEq, Inhabited

/--
What a port carries.

Stage C and stage D gave a port a `declaredType : LF.GeneralType`, and since
`GeneralType` is `int | boolean` that field can name the type of exactly one value.
It is the same erasure stage D removed from the action layer, surviving one layer
further along: `msgsrv report(int identifier, boolean urgent)` reached by an external
send needs a port carrying two values of two types, and a single `GeneralType` has
nowhere to put the second. The finding is F36.

The two constructors are not two mechanisms, they are one mechanism with a printed
special case:

* `scalar t` — the port carries one value of type `t`, printed as `input p: int`.
* `struct reactor message parameters` — the port carries one value of a
  program-level `public preamble` struct whose fields are `parameters`, printed as
  `input p: <Reactor>_<message>_Args`. The struct's *name* is derived from the
  **receiving** reactor and the message, by the same
  `generalPayloadStructName` the action layer already uses, which is exactly what lets
  one struct declaration serve a message server that is both self-sent and externally
  received.

Naming the struct from the receiving reactor rather than the sending one is what makes
both ends of a connection agree without either end consulting the other. It is also a
weakening worth stating plainly: stage D *derived* this name at one site, and stage E
**stores** it at two and checks agreement, so a guarantee that used to hold by
construction now holds by predicate. The finding is F37.

There is no `void` constructor, so a port carrying nothing is unrepresentable and an
arity-zero external send is refused by the translation rather than mistranslated. That
refusal is provisional and says so: whether `lfc 0.11.0` accepts `input p: void` is
**unmeasured**, the probe and its prediction are written down in
`docs/STAGE_E_DESIGN.md` §11.2, and the day it runs this type gains a constructor or
the refusal becomes permanent. The project does not guess about the target.
-/
inductive GeneralPortPayload where
  | scalar :
      LF.GeneralType →
      GeneralPortPayload

  | struct :
      ReactorName →
      ActionName →
      List LF.GeneralTypedParameter →
      GeneralPortPayload

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralPortPayload

/--
How many values a port's payload carries.

One for a scalar, and the length of the parameter list for a struct. This is the
number a `setPort` statement's argument list is checked against, so it is defined here
rather than open-coded at the two places that need it.

A struct payload of length zero or one is *representable* and never *built*: the
translation emits `scalar` at arity one and refuses arity zero. Well-formedness does
not forbid it, because a predicate that ruled out a shape the translation cannot
produce would be checking the translation rather than the program.
-/
def arity :
    LF.GeneralPortPayload → Nat
  | .scalar _ => 1
  | .struct _ _ parameters => parameters.length

end GeneralPortPayload

/--
A declared port of a reactor.

Stage C carried ports as bare `PortName`s and let the printer supply `": int"`. That
made the *type* of every port a fact about the printer rather than about the program,
which is precisely the kind of claim a syntax tree exists to hold. Stage D gave it a
`GeneralType`; stage E replaces that with a `GeneralPortPayload`, for the reason that
type records.

There is still no width field. Fig. 5's `PortDecl` admits a multiport width
`([intLiteral])?`, but `lfc 0.11.0` rejects `reaction(in[0])` and a whole-multiport
trigger fires once per tag regardless of channel count, so multiports cannot
implement the paper's receiver-side fan-in. Omitting the field keeps the rejected
construct unrepresentable rather than merely unused.
-/
structure GeneralPortDecl where
  name :
    PortName

  payload :
    LF.GeneralPortPayload

deriving Repr, DecidableEq, BEq, Inhabited

/--
A declared state variable of a reactor.

A type and **no** initial value, which is the one place this family deliberately
departs from the shape of `LF.StateVariableDecl` it would otherwise have reused.
That inherited structure carries `initialValue : Int` and no type at all — it comes
from `Relico/LF/StoreSyntax.lean`, an integer-only family — so a `boolean` state
variable was not translatable at the level of its *declaration*, quite apart from any
expression: its initial value is `false`, which has no `Int` counterpart.

Carrying the type alone rather than both is what makes a declaration that disagrees
with itself unstateable. `boolean` beside `0` would be representable and printable,
and no well-formedness check would be looking. The initial value is instead derived
by `GeneralType.initialValue`, which also fixes the emitted `= 0` and `= false`
in one place.

`LF.StateVariableDecl` is left untouched for the earlier families that use it.
-/
structure GeneralStateVariableDecl where
  name :
    VarName

  declaredType :
    LF.GeneralType

deriving Repr, DecidableEq, BEq, Inhabited

/--
A generated typed logical-action declaration.

The ordered parameters mirror source formal-parameter order, and they are typed. The
docstring here used to say *"the value domain is integer-only, as in the payload
family this borrows its shape from"*, and that inheritance is exactly what stage D
had to undo: a `msgsrv logic(boolean first, boolean second)` had nowhere to record
that its parameters are booleans, so the printer could only ever have guessed.

The parameter *names* are load-bearing beyond declaration order. For an action of
arity two or more the printer emits a struct whose field names are these names, and
binds one C++ local per parameter, so a reaction body can refer to a payload
component by its source identifier and the translation of expressions needs no
renaming pass.
-/
structure GeneralAction where
  name :
    ActionName

  parameters :
    List LF.GeneralTypedParameter

deriving Repr, DecidableEq, BEq, Inhabited

/--
What fires a reaction.

`inputPort` is the constructor this family exists to add. A reaction triggered by
an input port is the receiving half of every external send, and no earlier LF
family in this development could express one.
-/
inductive GeneralTrigger where
  | startup

  | logicalAction :
      ActionName →
      GeneralTrigger

  | inputPort :
      PortName →
      GeneralTrigger

deriving Repr, DecidableEq, BEq, Inhabited

/--
A generated reaction.

`priority` is carried, never consulted, and — since G3 — required to be absent.
The printer honours declaration *order* instead, because that is the only thing
Lingua Franca offers: `lfc 0.11.0` rejects a reaction attribute named `priority`
outright, measured as probe 16f of F77, so there is no target spelling for a
populated field to compile to. `LF.GeneralProgram.wellFormed`'s tenth conjunct,
`reactionPrioritiesAbsent`, therefore rejects a program whose reactions carry one.

That inverts the earlier note here, and the inversion is the point. This field was
originally left inert *"so that the later stage which makes priority observable has
somewhere to attach it"*, on the assumption that such a stage would arrive. Stage G
is that stage, and what it measured is that the attachment point cannot exist: the
field is a place where a value can be written and then silently dropped. It is kept
rather than deleted so that the refusal has something to name — a translator that
computes a priority and discards it is a defect the guard can report, whereas a
translator with nowhere to put one cannot be caught doing it.

Priority *distinctness* remains a theorem hypothesis rather than a well-formedness
conjunct; that separate decision is untouched. Absence and distinctness are
different properties, and only absence is checked here.

`name` identifies a reaction inside Lean and nothing else. LF reactions are
anonymous in concrete syntax: a printer emits `reaction(<trigger>)` and never the
name, so uniqueness of this field is deliberately not required anywhere. Requiring
it would constrain an identifier the target language never sees.

`parameters` stays a list of bare names while `GeneralAction.parameters` gained types,
and the asymmetry is deliberate rather than an omission stage D missed. A reaction's
parameters are the binders its emitted body opens over the arriving payload, and the
printer opens them with C++ `auto`, so their types are already determined by the
action the reaction is triggered by. Typing them here would create a second place for
the same fact to live, and two places that can disagree with nothing checking is the
shape of defect this development keeps finding.
-/
structure GeneralReaction where
  name :
    ReactionName

  trigger :
    LF.GeneralTrigger

  parameters :
    List VarName

  body :
    LF.GeneralBody

  priority :
    Option Nat :=
      none

deriving Repr, DecidableEq, BEq, Inhabited

/--
A generated reactor.

`parameters` restores a production the paper has and stage C dropped:
`Reactor ::= reactor R (ParamList?) {PortDecl* StateDecl* ActionDecl* ReactionDecl*}`.
Without it, `Configured configuredOn():(7, true)` and
`Configured configuredOff():(0, false)` — both in the committed fixture
`constructor-arguments.rebeca` — are indistinguishable once translated, because a
constructor's arguments have nowhere to land. A reactor parameter is the LF mechanism
for exactly this, and it is measured working in all three respects the design needed:
`reactor Configured(bound: int = 0, active: bool = false)` declares it,
`new Configured(bound=7, active=true)` supplies it per instance, and a parameter is
readable directly in a reaction body with no trigger and no further declaration.

Defaults are not stored. Every parameter's declared default is
`GeneralType.initialValue` of its type, so the declaration never needs to consult the
instance list, and a parameter without a default — which would make an argumentless
instantiation illegal — is unrepresentable.

The tempting alternative was to specialize one reactor per *instance* and inline its
arguments as constants, which would need no parameter list at all. It is rejected
because Table III maps a reactive **class** to a reactor and this family's whole shape
depends on instances of one class sharing one reactor declaration, whose port set is
the union over those instances — which is the object §III-F's cost bound ranges over.
Specializing per instance would quietly change what that bound is about.

Ports and state variables carry their declared types, and the reasons the port
structure has no width field, and carries a payload rather than a bare type, are
recorded on `GeneralPortDecl` and `GeneralPortPayload` themselves.

Input ports, output ports, state variables and logical actions are four lists but
**one** name scope. An LF reactor does not let `input v` and `state v` coexist, so
the uniqueness obligation over them is a single check over the union rather than
four per-list checks; four checks would accept a program no LF compiler will.

Stage D adds `parameters` as a fifth list in that same scope, on the same reasoning:
a parameter becomes a reactor member exactly as a state variable does — measured, in
that a parameter is readable in a reaction body with no trigger and no local
declaration — so `reactor R(x: int) { state x: int = 0 }` names one member twice.
Stage D wrote here that whether `lfc` rejects that spelling is **unverified**, and that
the union check was the conservative side of the uncertainty. It is measured as of
2026-08-20, by probe `param_state_name_collision` in
`tools/paper-measurements/lf_semantics_probe.sh`, and the answer is both halves at once:
the validator **accepts** the collision, and the generated C++ then fails to compile,
because the Cpp target emits a reactor parameter as a C++ *reference* member. So the
union check is stricter than `lfc`'s validator and exactly as strict as the toolchain
behind it. What that means for the predicate is recorded on
`LF.GeneralReactor.declaredNames`, and deliberately not restated here.

A declared port need not be connected, and that is load-bearing rather than a
tolerated gap. Because one reactor is shared by every instance of its class, its
input-port set is the union over those instances, so some instance of a shared
reactor will always carry ports nothing connects to. A model with an unconnected
input port compiles and runs; the reaction simply never fires.

`startupReaction` is mandatory, matching the mandatory constructor on the DTR side.
A source class with no constructor body is handled in the printer, not here, and
keeping the two sides shaped alike is what lets the translation be a total function
on a well-formed model.
-/
structure GeneralReactor where
  name :
    ReactorName

  parameters :
    List LF.GeneralTypedParameter

  inputPorts :
    List LF.GeneralPortDecl

  outputPorts :
    List LF.GeneralPortDecl

  stateVariables :
    List LF.GeneralStateVariableDecl

  logicalActions :
    List LF.GeneralAction

  startupReaction :
    LF.GeneralReaction

  messageReactions :
    List LF.GeneralReaction

deriving Repr, DecidableEq, BEq, Inhabited

/--
An instance declaration in the main reactor.

`LF.ReactorInstance`, which stage C used here, carries a name and a reactor name and
nothing else, so it cannot distinguish two instances of one class that were
constructed with different arguments. This structure adds the arguments, and
`LF.ReactorInstance` is left untouched for the earlier families.

`arguments` are **values**, not expressions: a constructor argument in Rebeca is a
literal, and there is no state to read at instantiation time. They are **positional**,
while the emitted LF is named. That direction is deliberate — positional is the shape
the source has, and the names are recovered at print time from the reactor's own
parameter list, so a *name* disagreement is unrepresentable rather than merely
unchecked. What remains checkable is the arity and, since a value carries its type and
a parameter declares one, the type of each argument; both are checked together by
`LF.GeneralProgram.instanceArgumentsMatch`. One list of names, authoritative, checked
once; two independently stored name lists could contradict each other and nothing would
notice.
-/
structure GeneralReactorInstance where
  name :
    ActorName

  reactorName :
    ReactorName

  arguments :
    List LF.GeneralValue

deriving Repr, DecidableEq, BEq, Inhabited

/--
A connection in the main reactor.

Endpoints are named by *instance*, not by reactor. A connection in LF lives in
`main reactor` and joins two instances; two instances of one reactor have distinct
connections through the same port names, and a connection between reactors would
have no meaning in the target language at all. Naming the reactor here would make
the illegal case representable.

Source and target may be the same instance. The tempting rule is to forbid that,
since §III-E sends a self-send to a logical action and only an external send to a
connection, but a DTR known rebec may be bound to the sending actor itself, and
§III-E maps `r.m()` by what the statement *is* rather than by who `r` turns out to
name.

`delay` is a `Delay` and not an `Option Delay`. Fig. 5 spells it `(after delay)?`,
but §III-E states that a delay-free connection is precisely what produces the
causality loops `lfc` rejects, so the optional form is one the translator must never
emit; recording that in the type makes it unrepresentable rather than merely unused,
and the divergence is filed as P19. `Delay` wrapping a `Nat` carries static and
non-negative along structurally. That the `after` really does break a cycle is
measured rather than assumed: a reaction whose output is connected back to its own
input compiles, runs, and prints at increasing microsteps.
-/
structure GeneralConnection where
  sourceInstance :
    ActorName

  sourcePort :
    PortName

  targetInstance :
    ActorName

  targetPort :
    PortName

  delay :
    Delay

deriving Repr, DecidableEq, BEq, Inhabited

/--
A complete general LF program.

A list of reactors and a *separate* list of instances, rather than one reactor
paired with one instance or one reactor per instance. That is not a convenience.
Table III maps a reactive **class** to a reactor, so several instances of one class
must share a single reactor declaration — which is what LF does and what Fig. 2b
prints — and it means the port set of a reactor is the union over its instances
rather than a per-instance thing. Making the program a pair of lists is what stops
that union from being expressible any other way, and it is the union the cost bound
of §III-F has to range over.

Both lists are non-empty in any well-formed program, and that is Fig. 5 rather than
taste: `LFProgram ::= target Cpp; Reactor+ MainReactor` and
`MainReactor ::= main reactor { InstDecl+ Connection* }` put a `+` on reactors and
on instances and a `*` only on connections. The obligation is stated in the
well-formedness predicate rather than in the type, because a plain `List` is what
the structural comparisons of the translation stage want on both sides.

No function in this family sorts any of these lists. Reaction order, connection
order, instance order and port order are the order they arrive in: two models
differing only in reaction declaration order print their effects in that order, so
declaration order is observable, and §III-D's whole mechanism is that *"the
`readingFromTemp` reaction is declared first, ensuring its message is processed
first."* A sort inserted anywhere here would be a silent semantic change.
-/
structure GeneralProgram where
  reactors :
    List LF.GeneralReactor

  instances :
    List LF.GeneralReactorInstance

  connections :
    List LF.GeneralConnection

deriving Repr, DecidableEq, BEq, Inhabited

/--
Find a reactor by name.

The two lookups below are explicit recursion over decidable equality rather than
`List.find?` over `BEq`, for the reason the DTR side records: deriving `DecidableEq`
and `BEq` independently does not produce a lawfulness bridge between them, and the
structural theorems of the translation stage compare a DTR list against an LF list,
so one notion of equality has to hold throughout.
-/
def findReactor? :
    List LF.GeneralReactor →
    ReactorName →
    Option LF.GeneralReactor

  | [], _ =>
      none

  | reactor :: remaining, reactorName =>
      if reactor.name = reactorName then
        some reactor
      else
        findReactor?
          remaining
          reactorName

/--
Find a reactor instance by name.
-/
def findInstance? :
    List LF.GeneralReactorInstance →
    ActorName →
    Option LF.GeneralReactorInstance

  | [], _ =>
      none

  | reactorInstance :: remaining, instanceName =>
      if reactorInstance.name = instanceName then
        some reactorInstance
      else
        findInstance?
          remaining
          instanceName

namespace GeneralProgram

/--
Find a reactor this program declares.
-/
def reactor?
    (program : LF.GeneralProgram)
    (reactorName : ReactorName) :
    Option LF.GeneralReactor :=
  LF.findReactor?
    program.reactors
    reactorName

/--
Find an instance this program's main reactor declares.
-/
def instance?
    (program : LF.GeneralProgram)
    (instanceName : ActorName) :
    Option LF.GeneralReactorInstance :=
  LF.findInstance?
    program.instances
    instanceName

/--
The reactor of a named instance, when both the instance and its reactor exist.

This composition is what a connection check needs. A connection names instances,
while ports are declared on reactors, so each endpoint resolves through the instance
list and then through the reactor list.
-/
def reactorOfInstance?
    (program : LF.GeneralProgram)
    (instanceName : ActorName) :
    Option LF.GeneralReactor :=
  match program.instance? instanceName with

  | none =>
      none

  | some reactorInstance =>
      program.reactor?
        reactorInstance.reactorName

end GeneralProgram

/- `setPortNamesOfStmt` and `setPortNamesOfBody` are mutually recursive because
`LF.GeneralStmt.ifThenElse` carries two nested bodies. A `mutual` block does not accept a
docstring, so each definition carries its own. -/
mutual

/--
The output ports one reaction body sets, in source order, **with repeats preserved**.

The repeats are the entire reason this function exists, so it is not a `filterMap` composed
with a dedup and it must never become one. `docs/STAGE_E_DESIGN.md` §10.2 owes a theorem
saying *"no reaction of an emitted reactor sets one output port twice"*; that sentence is a
claim about `Nodup` of exactly this list, and it cannot be stated without a list that would
show the repeat if there were one.

Explicit recursion over every `LF.GeneralStmt` constructor rather than
`List.filterMap` with a pattern-matching function, for the two reasons
`Translation.compileGeneralBody` gives for its own shape: every equation below then holds by
`rfl`, so the induction in `Translation.compileGeneralBody_setPortNames_nodup` rewrites with
`rfl` lemmas instead of unfolding a combinator; and this development depends on no library
function whose name has churned across Lean releases, which `List.filterMap`'s neighbours
`flatMap` and `flatten` both have. Writing the no-port arms out instead of
using a catch-all is deliberate too: another statement constructor should break this
function loudly rather than be silently classified as setting nothing.

**No clause of `LF.GeneralWellFormed` looks at this list, and that is the finding rather than
an oversight.** `LF.GeneralReactor.stmtWellFormed`'s `.setPort` arm asks that the port be
*declared* on the reactor with a matching payload arity — not that it be set once — which is
the same shape as `connectionsWellFormed` asking that an endpoint be declared rather than
declared once (F48). So `Nodup` of this list is a property the stage E guard does not check,
and finding F50 records that it is also not true in general.

**Stage H's `ifThenElse` arm concatenates both branches, and that is a semantic decision.**
A conditional contributes the ports of the then-branch followed by those of the else-branch,
so a port set in each arm appears twice in this list even though only one arm executes. The
alternative, counting along one execution path, was rejected: it would make the property a
statement about *runs* rather than about the compiled body, which this function cannot express
and no guard could check. Keeping it static keeps `Nodup` decidable from the body alone and
keeps F50's guard-relative theorem meaningful under branching. The cost is stated rather than
hidden: a program that sets one port in each arm is now reported as a repeat, which is
conservative and may name a program that would be safe at run time.

The `rfl` property the three arms above were written for is preserved, and preserving it took a
shape change. Stage H's first attempt recursed from the body-level function straight into the two
branch bodies, which Lean compiles by **well-founded** recursion, and a well-founded definition
does not reduce: `setPortNamesOfBody [] = []` stopped holding by `rfl`, and with it every pin that
evaluates a compilation, because the program guard calls this function. Splitting the traversal into
a statement-level function and a body-level one — the standard shape for a nested inductive — makes
it structurally recursive again, so the equations reduce and `decide` still evaluates the guard. The
measurement is in `Relico/Tests/GeneralInitialization.lean`, whose two compilation pins failed
against the single-function version while the library still built.
-/
def setPortNamesOfStmt :
    LF.GeneralStmt →
    List PortName

  | .assign _ _ =>
      []

  | .trace _ =>
      []

  | .schedule _ _ _ =>
      []

  | .setPort port _ =>
      [port]

  | .ifThenElse _ thenBody elseBody =>
      setPortNamesOfBody thenBody ++
        setPortNamesOfBody elseBody

  | .localDecl _ _ _ =>
      []

/--
The output ports a body sets, in order, counting a repeat twice.

The body-level half of the pair. Every head statement is handed to `setPortNamesOfStmt`, which is
what keeps the recursion structural; the values are unchanged from the single-function version
because a statement that sets nothing contributes `[]` and a `setPort` contributes a one-element
list.
-/
def setPortNamesOfBody :
    LF.GeneralBody →
    List PortName

  | [] =>
      []

  | statement :: remaining =>
      setPortNamesOfStmt statement ++
        setPortNamesOfBody remaining

end

/-!
### Set-port traversal equations

One directed equation per head constructor, `@[simp]`, so that a proof about a compiled body
rewrites into the arm it cares about instead of unfolding the pair. They exist because the pair
form is what keeps the traversal structurally recursive and therefore reducible, while the
*shape* every proof in `Relico/Translation/GeneralBasic.lean` wants is the one the
single-function version had: a `setPort` head contributing `port :: …` rather than
`[port] ++ …`, and a conditional head contributing the two branches ahead of the tail.

Stating them is not a convenience. Without them each proof would carry the append normalisation
of the pair, and the two site lemmas would read as facts about `setPortNamesOfStmt` rather than
about the body.
-/

@[simp]
theorem setPortNamesOfBody_assign
    (target : VarName)
    (value : LF.GeneralExpr)
    (remaining : LF.GeneralBody) :
    setPortNamesOfBody
        (
          .assign
              target
              value ::
            remaining
        ) =
      setPortNamesOfBody
        remaining := by
  simp [
    setPortNamesOfBody,
    setPortNamesOfStmt
  ]

@[simp]
theorem setPortNamesOfBody_trace
    (tag : String)
    (remaining : LF.GeneralBody) :
    setPortNamesOfBody
        (
          .trace
              tag ::
            remaining
        ) =
      setPortNamesOfBody
        remaining := by
  simp [
    setPortNamesOfBody,
    setPortNamesOfStmt
  ]

@[simp]
theorem setPortNamesOfBody_schedule
    (actionName : ActionName)
    (arguments : List LF.GeneralExpr)
    (delay : Delay)
    (remaining : LF.GeneralBody) :
    setPortNamesOfBody
        (
          .schedule
              actionName
              arguments
              delay ::
            remaining
        ) =
      setPortNamesOfBody
        remaining := by
  simp [
    setPortNamesOfBody,
    setPortNamesOfStmt
  ]

@[simp]
theorem setPortNamesOfBody_setPort
    (port : PortName)
    (arguments : List LF.GeneralExpr)
    (remaining : LF.GeneralBody) :
    setPortNamesOfBody
        (
          .setPort
              port
              arguments ::
            remaining
        ) =
      port ::
        setPortNamesOfBody
          remaining := by
  simp [
    setPortNamesOfBody,
    setPortNamesOfStmt
  ]

@[simp]
theorem setPortNamesOfBody_ifThenElse
    (condition : LF.GeneralExpr)
    (thenBody elseBody remaining : LF.GeneralBody) :
    setPortNamesOfBody
        (
          .ifThenElse
              condition
              thenBody
              elseBody ::
            remaining
        ) =
      setPortNamesOfBody
          thenBody ++
        setPortNamesOfBody
            elseBody ++
          setPortNamesOfBody
            remaining := by
  simp [
    setPortNamesOfBody,
    setPortNamesOfStmt,
    List.append_assoc
  ]

@[simp]
theorem setPortNamesOfBody_localDecl
    (name : VarName)
    (declaredType : LF.GeneralType)
    (value : LF.GeneralExpr)
    (remaining : LF.GeneralBody) :
    setPortNamesOfBody
        (
          .localDecl
              name
              declaredType
              value ::
            remaining
        ) =
      setPortNamesOfBody
        remaining := by
  simp [
    setPortNamesOfBody,
    setPortNamesOfStmt
  ]

end LF
end Relico
