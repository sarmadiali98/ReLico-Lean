import Relico.DTR.GeneralSyntax
import Relico.LF.GeneralSyntax
import Relico.Translation.NameGeneration

set_option autoImplicit false

namespace Relico
namespace Translation

/-!
# Stage D: translating the general DTR family into the general LF family

Everything a general DTR model contains except one statement form. A `.send` to a
*known rebec* is refused with a diagnostic that names stage E; a `.send` to `self`
becomes a `schedule` on a logical action, which is §III-E's own rule for a self-send.
Ports and connections are consequently empty here, and §9.1's three boundary theorems
state that as arithmetic rather than as prose: the stage that adds external sends has
to break `compileGeneralModel_connections` before it can compile.

Four things in this file differ from `docs/STAGE_D_DESIGN.md` §7, and each is recorded
here rather than left for a reader to discover by diffing.

**Every function carries `General`, including the four whose names the design's table
spells without it.** `Relico.Translation.compileStateVariableDecl` already exists, at
`Relico/Translation/StoreBasic.lean:14`, and `Relico.Translation` is one flat namespace
shared by every family in this development, so the design's `compileStateVariableDecl`
is not an available name. Renaming that one alone would leave a per-name exception
list; marking all nine uniformly leaves a rule.

**The error type is `String` and not `Translation.TranslationError`.** That type has a
single `unsupported : String` constructor, so it contributes a wrapper and no
information; the printer half of this family is already `Except String`; and the gate
asserts on the diagnostic's text, which a wrapper only lengthens the path to.

**`compileGeneralBody`'s `cons` equation is three lemmas split by outcome rather than
one.** The design asks for a single `cons` equation *"in terms of
`compileGeneralStmt`"*, which puts a `match` inside a theorem statement, and a `match`
written there elaborates to a *new* matcher constant whose definitional agreement with
the one inside the definition the proof then leans on silently. `_cons_ok`,
`_cons_error_head` and `_cons_error_tail` carry the same content with no matcher in any
statement, and each is separately usable in a rewrite.

**The reactions, reactors and program are built by total `assemble` helpers.** Each
partial function computes its sub-results and hands them to a total assembler, so
`inputPorts = []`, `outputPorts = []`, `connections = []` and `priority = none` become
`rfl` facts about a function that cannot fail, and every inversion lemma has exactly one
right-hand side to name.

Nothing here sorts anything, which is the difference worth stating against
`Relico/Translation/MultiStoreBasic.lean`: that family compiles message servers in
`priorityOrderedMessageServers` order. Reaction declaration order is observable in the
target — measured, not assumed — so the sort that would realize local message-server
priority is a semantic act, and it belongs to the stage that also proves what it
achieves. Stage D emits source order and drops `DTR.GeneralMessageServer.priority`.
`assembleGeneralMessageReaction_priority` records that drop as a theorem, so stage G
cannot wire the field without breaking a proof.

One obligation is discharged nowhere yet, and is filed as **F32**: nothing proves that a
program this file produces satisfies `LF.GeneralProgram.wellFormed`. The printer's
refusals are justified in the design by appeal to well-formedness — an unresolvable
instance, an argument list that disagrees with its parameter list — so until that
theorem exists, *"the printer never refuses a translated program"* is an argument and
not a fact. The `lfc` gate narrows it to one witness rather than closing it: the bridge
test main asserts `wellFormed` of the program this file produces from its widened model,
so the claim is checked for that model on every build and unproved for every other.
-/

/-!
## The total layer

Nine functions, no `Except`, no wildcard in any match. Every one of them is an
identity-shaped map, and that is the strongest evidence that §3's widening of the LF
side was the right call rather than a symmetry: after it the data half of the
translation has **no failure case at all**, so there is no diagnostic to word, no error
string to test and no unreachable branch to justify. Before it, five of the nine could
not be written.

Each is spelled out over all its constructors. The stage that adds a fourteenth binary
operator, a third type or a seventh expression form gets a build error at exactly the
functions that have to change, which a wildcard would convert into a silently wrong
translation.
-/

/--
Translate a declared type.

Total and injective in the only sense that matters here: the two DTR constructors map
to the two LF constructors of the same name, and neither side has a type the other
cannot express. The emitted spellings differ — LF writes `bool` where this writes
`boolean` — and the single place that knows this is `renderGeneralType` in the printer.
-/
def compileGeneralType :
    DTR.GeneralType →
    LF.GeneralType

  | .int =>
      .int

  | .boolean =>
      .boolean

/--
Translate a value.

Values appear only as constructor arguments on an actor instance, which is why this is
needed at all: before stage D an instance carried no arguments, so no value ever crossed
the boundary.
-/
def compileGeneralValue :
    DTR.GeneralValue →
    LF.GeneralValue

  | .int value =>
      .int value

  | .bool value =>
      .bool value

/--
Translate a binary operator.

Thirteen arms, one per source operator, with the LF constructor of the same name. The
comparison and logical operators are exactly the ones the earlier integer-only families
could not carry, and `frontend/fixtures/general/expressions.rebeca` — a committed
*positive* fixture of this family — uses every one of them.
-/
def compileGeneralBinaryOp :
    DTR.GeneralBinaryOp →
    LF.GeneralBinaryOp

  | .add =>
      .add

  | .sub =>
      .sub

  | .mul =>
      .mul

  | .div =>
      .div

  | .mod =>
      .mod

  | .eq =>
      .eq

  | .ne =>
      .ne

  | .lt =>
      .lt

  | .le =>
      .le

  | .gt =>
      .gt

  | .ge =>
      .ge

  | .logicalAnd =>
      .logicalAnd

  | .logicalOr =>
      .logicalOr

/--
Translate a unary operator.
-/
def compileGeneralUnaryOp :
    DTR.GeneralUnaryOp →
    LF.GeneralUnaryOp

  | .negate =>
      .negate

  | .logicalNot =>
      .logicalNot

/--
Translate an expression.

Six arms, two of them recursive, and totality is by structural recursion with no
termination argument owed. Nothing is checked here: DTR well-formedness resolves the
names an expression mentions and places no restriction on the expression itself, and the
LF side's `exprWellFormed` is deliberately name-resolution only, so a type check
inserted here would refuse programs this repository's own frontend accepts. That is the
trap that ruled out restricting the translation's domain instead of widening the target,
recorded in `docs/STAGE_D_DESIGN.md` §3.
-/
def compileGeneralExpr :
    DTR.GeneralExpr →
    LF.GeneralExpr

  | .intLiteral value =>
      .intLiteral value

  | .boolLiteral value =>
      .boolLiteral value

  | .stateVar name =>
      .stateVar name

  | .parameterVar name =>
      .parameterVar name

  | .binary operator left right =>
      .binary
        (compileGeneralBinaryOp operator)
        (compileGeneralExpr left)
        (compileGeneralExpr right)

  | .unary operator operand =>
      .unary
        (compileGeneralUnaryOp operator)
        (compileGeneralExpr operand)

/--
Translate a state-variable declaration.

The declared type crosses and the initial value does not, because the LF side no longer
stores one: `LF.GeneralStateVariableDecl` carries a type and derives `= 0` or `= false`
from it through `GeneralType.initialValue`, so a declaration that disagrees with itself
is unstateable rather than merely unwritten. The earlier `LF.StateVariableDecl`, which
carries `initialValue : Int` and no type at all, is what made a `boolean` state variable
untranslatable at the level of its *declaration* — finding F21.
-/
def compileGeneralStateVariableDecl
    (declaration : DTR.GeneralStateVariableDecl) :
    LF.GeneralStateVariableDecl where

  name :=
    declaration.name

  declaredType :=
    compileGeneralType declaration.declaredType

/--
Translate a typed parameter.

One function for both uses, because one structure serves both on each side: a message
server's formals and a constructor's formals are the same shape in DTR, and stage D made
them the same shape in LF.
-/
def compileGeneralTypedParameter
    (parameter : DTR.GeneralTypedParameter) :
    LF.GeneralTypedParameter where

  name :=
    parameter.name

  declaredType :=
    compileGeneralType parameter.declaredType

/--
Derive the logical action that carries one message server's arrivals.

Total rather than an arity check, which is precisely what §5's widening bought: a
`GeneralAction` now carries typed parameters, so `msgsrv logic(boolean first, boolean
second)` has somewhere to record that its parameters are booleans. The parameter *names*
are load-bearing beyond their order — for arity two and above the printer emits a struct
whose field names are these names and binds one C++ local per parameter, so a reaction
body refers to a payload component by its source identifier and the translation of
expressions needs no renaming pass.
-/
def compileGeneralMessageServerAction
    (server : DTR.GeneralMessageServer) :
    LF.GeneralAction where

  name :=
    actionNameFor server.name

  parameters :=
    server.parameters.map
      compileGeneralTypedParameter

/--
Translate an actor instance.

`bindings` is read by nothing here. A known-rebec binding becomes a connection only when
something sends on it, and stage D has no external sends, so the binding contributes
nothing to the program — which is the same boundary the two empty port lists and the
empty connection list state from their own sides. `priority` is likewise dropped: actor
priority has no LF observable in this repository at all, which is the subject of the
actor-priority audit rather than of this stage.

`arguments` are values and positional, and they cross in source order.
`LF.GeneralProgram.instanceArgumentsMatch` is what later checks them against the
parameters of the reactor being instantiated; nothing is checked here.
-/
def compileGeneralActorInstance
    (actor : DTR.GeneralActorInstance) :
    LF.GeneralReactorInstance where

  name :=
    actor.name

  reactorName :=
    reactorNameFor actor.className

  arguments :=
    actor.arguments.map
      compileGeneralValue

/-!
### The total layer's equations

Field projections through an identity-shaped map, `rfl` throughout, `@[simp]` so that the
proofs further down never unfold a definition to read a field.
-/

/--
Translation preserves the type of a value.

The mirror of the DTR side's `@[simp] typeOf_initialValue`, and the reason
`LF.GeneralValue.typeOf` was defined at all. Without it, `instanceArgumentsMatch` on the
LF side and `argumentsMatchConstructor` on the DTR side would be two independent
computations over the same argument list, and a translation that permuted or retyped an
argument would satisfy one while violating the other.
-/
@[simp]
theorem typeOf_compileGeneralValue
    (value : DTR.GeneralValue) :
    (compileGeneralValue value).typeOf =
      compileGeneralType value.typeOf := by
  cases value <;> rfl

@[simp]
theorem compileGeneralStateVariableDecl_name
    (declaration : DTR.GeneralStateVariableDecl) :
    (compileGeneralStateVariableDecl declaration).name =
      declaration.name := by
  rfl

@[simp]
theorem compileGeneralStateVariableDecl_declaredType
    (declaration : DTR.GeneralStateVariableDecl) :
    (compileGeneralStateVariableDecl declaration).declaredType =
      compileGeneralType declaration.declaredType := by
  rfl

@[simp]
theorem compileGeneralTypedParameter_name
    (parameter : DTR.GeneralTypedParameter) :
    (compileGeneralTypedParameter parameter).name =
      parameter.name := by
  rfl

@[simp]
theorem compileGeneralTypedParameter_declaredType
    (parameter : DTR.GeneralTypedParameter) :
    (compileGeneralTypedParameter parameter).declaredType =
      compileGeneralType parameter.declaredType := by
  rfl

@[simp]
theorem compileGeneralMessageServerAction_name
    (server : DTR.GeneralMessageServer) :
    (compileGeneralMessageServerAction server).name =
      actionNameFor server.name := by
  rfl

@[simp]
theorem compileGeneralMessageServerAction_parameters
    (server : DTR.GeneralMessageServer) :
    (compileGeneralMessageServerAction server).parameters =
      server.parameters.map
        compileGeneralTypedParameter := by
  rfl

@[simp]
theorem compileGeneralActorInstance_name
    (actor : DTR.GeneralActorInstance) :
    (compileGeneralActorInstance actor).name =
      actor.name := by
  rfl

@[simp]
theorem compileGeneralActorInstance_reactorName
    (actor : DTR.GeneralActorInstance) :
    (compileGeneralActorInstance actor).reactorName =
      reactorNameFor actor.className := by
  rfl

/--
Instance arguments cross in source order.

Order, not merely count: instance arguments are positional on both sides, so a
translation that reversed them would still satisfy an arity theorem.
-/
@[simp]
theorem compileGeneralActorInstance_arguments
    (actor : DTR.GeneralActorInstance) :
    (compileGeneralActorInstance actor).arguments =
      actor.arguments.map
        compileGeneralValue := by
  rfl

/--
Instance arguments cross in the same number.

A corollary of the order lemma, stated separately because the argument-count agreement
that `instanceArgumentsMatch` checks is about lengths and the proof of it should not have
to reason through a `map`.
-/
theorem compileGeneralActorInstance_arguments_length
    (actor : DTR.GeneralActorInstance) :
    (compileGeneralActorInstance actor).arguments.length =
      actor.arguments.length := by
  simp

/-!
## The refusal surface, as an executable predicate

§9.3 pins the refusal surface with an `iff`, and this family of `Bool` predicates is its
right-hand side. Three properties of that choice are deliberate.

**It is `Bool` and not `Prop`.** The predicate is then executable, so the bridge test main
can assert it on a fixture and the gate can watch the two halves of the `iff` agree on
real input rather than only in the abstract.

**It is phrased positively.** `SelfSendOnly` rather than `¬ isExternalSend` means every
proof below needs `Bool.and_eq_true`, which this repository already uses in
`Relico/LF/GeneralWellFormed.lean`, and never needs `Bool.and_eq_false`,
`Bool.not_eq_true` or any other name from the `false` side of Bool algebra. The content is
identical; the tactic risk is not.

**It recurses explicitly instead of using `List.all`.** The `nil` and `cons` equations then
hold by `rfl`, and the induction in §9.3 walks the same shape the compilation walks, so
the two sides of the `iff` are structurally aligned at every level rather than related
through a combinator.

The DTR side is asked no questions here beyond this one. A body may assign anything to
anything, nest operators arbitrarily and delay a self-send; none of that is a refusal, and
§8.1 lists the seven such non-refusals that the `iff` proves all at once.
-/

/--
A statement is not an external send.

Written over `GeneralSendTarget` rather than over a `isExternalSend` helper on the DTR
side, because the refusal belongs to *this translation stage* and not to the source
language: an external send is a perfectly well-formed DTR statement, and a predicate
living on the DTR side would suggest otherwise.
-/
def generalStmtSelfSendOnly :
    DTR.GeneralStmt →
    Bool

  | .assign _ _ =>
      true

  | .send .selfTarget _ _ _ =>
      true

  | .send (.knownRebec _) _ _ _ =>
      false

/--
No statement in a body is an external send.
-/
def generalBodySelfSendOnly :
    DTR.GeneralBody →
    Bool

  | [] =>
      true

  | statement :: remaining =>
      generalStmtSelfSendOnly statement &&
        generalBodySelfSendOnly remaining

@[simp]
theorem generalBodySelfSendOnly_nil :
    generalBodySelfSendOnly [] =
      true := by
  rfl

@[simp]
theorem generalBodySelfSendOnly_cons
    (statement : DTR.GeneralStmt)
    (remaining : DTR.GeneralBody) :
    generalBodySelfSendOnly
        (statement :: remaining) =
      (generalStmtSelfSendOnly statement &&
        generalBodySelfSendOnly remaining) := by
  rfl

/--
No message server's body contains an external send.
-/
def generalMessageServersSelfSendOnly :
    List DTR.GeneralMessageServer →
    Bool

  | [] =>
      true

  | server :: remaining =>
      generalBodySelfSendOnly server.body &&
        generalMessageServersSelfSendOnly remaining

@[simp]
theorem generalMessageServersSelfSendOnly_nil :
    generalMessageServersSelfSendOnly [] =
      true := by
  rfl

@[simp]
theorem generalMessageServersSelfSendOnly_cons
    (server : DTR.GeneralMessageServer)
    (remaining : List DTR.GeneralMessageServer) :
    generalMessageServersSelfSendOnly
        (server :: remaining) =
      (generalBodySelfSendOnly server.body &&
        generalMessageServersSelfSendOnly remaining) := by
  rfl

/--
Neither a class's constructor nor any of its message servers sends externally.

`knownRebecs` is not consulted. A class may *declare* known rebecs and remain
translatable in stage D, and that is not an oversight: a known rebec becomes a port only
when something sends on it. Several committed fixtures declare known rebecs they never
use, and §8.1 requires that they pass rather than fail.
-/
def generalClassSelfSendOnly
    (reactiveClass : DTR.GeneralReactiveClass) :
    Bool :=
  generalBodySelfSendOnly
      reactiveClass.constructor.body &&
    generalMessageServersSelfSendOnly
      reactiveClass.messageServers

/--
No class sends externally.
-/
def generalClassesSelfSendOnly :
    List DTR.GeneralReactiveClass →
    Bool

  | [] =>
      true

  | reactiveClass :: remaining =>
      generalClassSelfSendOnly reactiveClass &&
        generalClassesSelfSendOnly remaining

@[simp]
theorem generalClassesSelfSendOnly_nil :
    generalClassesSelfSendOnly [] =
      true := by
  rfl

@[simp]
theorem generalClassesSelfSendOnly_cons
    (reactiveClass : DTR.GeneralReactiveClass)
    (remaining : List DTR.GeneralReactiveClass) :
    generalClassesSelfSendOnly
        (reactiveClass :: remaining) =
      (generalClassSelfSendOnly reactiveClass &&
        generalClassesSelfSendOnly remaining) := by
  rfl

/--
A model lies inside stage D's fragment.

Only the classes are examined. The instance list cannot contain a statement, so a model
with any number of instances, any arguments and any bindings is inside the fragment
exactly when its classes are — which is what makes the empty connection list a
consequence of the fragment rather than an additional restriction on it.
-/
def generalModelSelfSendOnly
    (model : DTR.GeneralModel) :
    Bool :=
  generalClassesSelfSendOnly
    model.classes

/-!
## The partial layer

`Except String` from here down, and exactly one function introduces a failure. Everything
below `compileGeneralStmt` only propagates one, which §10 states as theorems rather than
leaving as a reading of the code.
-/

/--
Translate a statement.

A self-send becomes a `schedule` on the logical action derived from the message name,
which is §III-E's rule and not a choice: a self-send has to arrive at a later tag in the
same reactor, and a logical action is the only construct that does that without a
connection.

The `.knownRebec` arm is the entire refusal surface of stage D. Its message names the stage
that will implement the construct rather than merely reporting that this one will not,
following stage B's diagnostic style, and the gate asserts on that text so the naming
cannot decay into a bare `.error` later.

The delay crosses unchanged in the self-send case. A `Delay` wraps a `Nat`, so static and
non-negative travel along structurally, and `after 0` is representable on both sides
because a zero-delay self-send is a microstep and not a causality loop.
-/
def compileGeneralStmt :
    DTR.GeneralStmt →
    Except String LF.GeneralStmt

  | .assign target value =>
      .ok
        (.assign
          target
          (compileGeneralExpr value))

  | .send .selfTarget message arguments delay =>
      .ok
        (.schedule
          (actionNameFor message)
          (arguments.map
            compileGeneralExpr)
          delay)

  | .send (.knownRebec rebec) message _ _ =>
      .error
        ("send to known rebec `" ++
          rebec.value ++
          "`.`" ++
          message.value ++
          "` is an external send; " ++
          "stage D translates self-sends only, and external sends are stage E")

/--
Translate a statement sequence, in order, stopping at the first refusal.

Explicit top-level recursion rather than `mapM`, matching the house pattern in
`Relico/Translation/GlobalMultiStorePayloadBasic.lean`. Two reasons, and neither is taste.
The `nil` and `cons` equations then hold by `rfl`, so the lemmas below are `rfl` proofs
rather than unfoldings of a monadic combinator; and order preservation is provable by an
induction that walks the same shape this walks, which is what §9.2's later stages need.

First refusal wins, and the diagnostic that survives is the earliest one in source order.
That is a deliberate property of a translator whose refusals name a future stage: the
message a user sees is about the first construct they wrote that this stage cannot carry.
-/
def compileGeneralBody :
    DTR.GeneralBody →
    Except String LF.GeneralBody

  | [] =>
      .ok []

  | statement :: remaining =>
      match compileGeneralStmt statement with

      | .error message =>
          .error message

      | .ok compiledStatement =>
          match compileGeneralBody remaining with

          | .error message =>
              .error message

          | .ok compiledRemaining =>
              .ok
                (compiledStatement ::
                  compiledRemaining)

@[simp]
theorem compileGeneralBody_nil :
    compileGeneralBody [] =
      .ok [] := by
  rfl

/-!
### The `cons` equation, split by outcome

`docs/STAGE_D_DESIGN.md` §9.1 asks for one `cons` equation stated in terms of
`compileGeneralStmt`. Stating it that way puts a `match` inside a theorem statement, and a
`match` written in a statement elaborates to a *fresh* matcher constant; the proof then
rests on that constant agreeing definitionally with the one inside the definition, which
is exactly the kind of dependency a build cannot report on when it breaks. These three
lemmas carry the same content with no matcher in any statement, and each is separately
usable as a rewrite — which is what the inversion lemmas of §10 actually need.
-/

theorem compileGeneralBody_cons_ok
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiledStatement : LF.GeneralStmt}
    {compiledRemaining : LF.GeneralBody}
    (hStatement :
      compileGeneralStmt statement =
        .ok compiledStatement)
    (hRemaining :
      compileGeneralBody remaining =
        .ok compiledRemaining) :
    compileGeneralBody
        (statement :: remaining) =
      .ok
        (compiledStatement ::
          compiledRemaining) := by
  simp [
    compileGeneralBody,
    hStatement,
    hRemaining
  ]

theorem compileGeneralBody_cons_error_head
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {message : String}
    (hStatement :
      compileGeneralStmt statement =
        .error message) :
    compileGeneralBody
        (statement :: remaining) =
      .error message := by
  simp [
    compileGeneralBody,
    hStatement
  ]

theorem compileGeneralBody_cons_error_tail
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiledStatement : LF.GeneralStmt}
    {message : String}
    (hStatement :
      compileGeneralStmt statement =
        .ok compiledStatement)
    (hRemaining :
      compileGeneralBody remaining =
        .error message) :
    compileGeneralBody
        (statement :: remaining) =
      .error message := by
  simp [
    compileGeneralBody,
    hStatement,
    hRemaining
  ]

/-!
## Reactions

Each reaction is built in two steps: a **total** assembler that takes an already-compiled
body and cannot fail, and a partial wrapper that compiles the body and hands it over. The
split is what makes `priority = none` a `rfl` fact about a total function rather than a
claim about one branch of a partial one, and it gives every inversion lemma in §10 a
single right-hand side to name.
-/

/--
Assemble the reaction that handles one message server's arrivals.

The trigger is the logical action derived from the same message name, so the two halves of
§III-E's self-send rule — `schedule` in a body, `reaction(m_action)` in the header — are
generated from one source name by one function each, and `actionNameFor_injective` is what
stops two message servers from sharing an action.

The reaction's parameters are the message server's parameter *names*, in source order.
Their types are not repeated here and that is not an omission: a payload's types are fixed
by the action that triggers the reaction, so recording them a second time would create two
places for one fact to live.

`priority := none` **deliberately**, even though `DTR.GeneralMessageServer.priority` may be
`some n` and this field exists to receive it. Local message-server priority is realized in
LF by reaction *declaration order* — the one ordering hook the target actually provides,
measured rather than assumed — and choosing that order is a sort over the message-server
list that stage G owns together with the actor-priority observable. A stage D that wrote
`priority := some n` would look finished and be unproved.
-/
def assembleGeneralMessageReaction
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    LF.GeneralReaction where

  name :=
    messageReactionNameFor server.name

  trigger :=
    .logicalAction
      (actionNameFor server.name)

  parameters :=
    server.parameters.map
      (fun parameter =>
        parameter.name)

  body :=
    compiledBody

  priority :=
    none

@[simp]
theorem assembleGeneralMessageReaction_name
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReaction
        server
        compiledBody).name =
      messageReactionNameFor server.name := by
  rfl

@[simp]
theorem assembleGeneralMessageReaction_trigger
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReaction
        server
        compiledBody).trigger =
      .logicalAction
        (actionNameFor server.name) := by
  rfl

@[simp]
theorem assembleGeneralMessageReaction_parameters
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReaction
        server
        compiledBody).parameters =
      server.parameters.map
        (fun parameter =>
          parameter.name) := by
  rfl

@[simp]
theorem assembleGeneralMessageReaction_body
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReaction
        server
        compiledBody).body =
      compiledBody := by
  rfl

/--
The dropped message-server priority, as a theorem.

Stage G cannot wire `DTR.GeneralMessageServer.priority` into the generated reaction without
breaking this proof, which is the cheapest possible alarm that the boundary has moved. It
is the same device §9.1 uses for `compileGeneralModel_connections`.
-/
@[simp]
theorem assembleGeneralMessageReaction_priority
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReaction
        server
        compiledBody).priority =
      none := by
  rfl

/--
Translate one message server into its reaction.

No new failure: the only thing that can go wrong is a refusal inside the body.
-/
def compileGeneralMessageServerReaction
    (server : DTR.GeneralMessageServer) :
    Except String LF.GeneralReaction :=
  match compileGeneralBody server.body with

  | .error message =>
      .error message

  | .ok compiledBody =>
      .ok
        (assembleGeneralMessageReaction
          server
          compiledBody)

theorem compileGeneralMessageServerReaction_ok
    {server : DTR.GeneralMessageServer}
    {compiledBody : LF.GeneralBody}
    (hBody :
      compileGeneralBody server.body =
        .ok compiledBody) :
    compileGeneralMessageServerReaction server =
      .ok
        (assembleGeneralMessageReaction
          server
          compiledBody) := by
  simp [
    compileGeneralMessageServerReaction,
    hBody
  ]

theorem compileGeneralMessageServerReaction_error
    {server : DTR.GeneralMessageServer}
    {message : String}
    (hBody :
      compileGeneralBody server.body =
        .error message) :
    compileGeneralMessageServerReaction server =
      .error message := by
  simp [
    compileGeneralMessageServerReaction,
    hBody
  ]

/--
Assemble the startup reaction from a constructor.

The constructor's parameter *names* become the reaction's parameters while the constructor's
typed parameters become the **reactor's** parameters, and the pair is what makes the
generated body legal: a reactor parameter is readable in a reaction body with no trigger
and no local declaration, measured, so a constructor formal mentioned in the constructor's
body resolves. `compileGeneralReactiveClass_startupParameters` states the agreement rather
than leaving it as a coincidence between two `map`s.

`priority := none` here is not a dropped field. A constructor has no priority to drop; LF
gives `startup` its own trigger, and nothing competes with it at the same tag.
-/
def assembleGeneralStartupReaction
    (classConstructor : DTR.GeneralConstructor)
    (compiledBody : LF.GeneralBody) :
    LF.GeneralReaction where

  name :=
    startupReactionName

  trigger :=
    .startup

  parameters :=
    classConstructor.parameters.map
      (fun parameter =>
        parameter.name)

  body :=
    compiledBody

  priority :=
    none

@[simp]
theorem assembleGeneralStartupReaction_name
    (classConstructor : DTR.GeneralConstructor)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralStartupReaction
        classConstructor
        compiledBody).name =
      startupReactionName := by
  rfl

@[simp]
theorem assembleGeneralStartupReaction_trigger
    (classConstructor : DTR.GeneralConstructor)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralStartupReaction
        classConstructor
        compiledBody).trigger =
      .startup := by
  rfl

@[simp]
theorem assembleGeneralStartupReaction_parameters
    (classConstructor : DTR.GeneralConstructor)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralStartupReaction
        classConstructor
        compiledBody).parameters =
      classConstructor.parameters.map
        (fun parameter =>
          parameter.name) := by
  rfl

@[simp]
theorem assembleGeneralStartupReaction_body
    (classConstructor : DTR.GeneralConstructor)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralStartupReaction
        classConstructor
        compiledBody).body =
      compiledBody := by
  rfl

@[simp]
theorem assembleGeneralStartupReaction_priority
    (classConstructor : DTR.GeneralConstructor)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralStartupReaction
        classConstructor
        compiledBody).priority =
      none := by
  rfl

/--
Translate a constructor into the startup reaction.
-/
def compileGeneralConstructor
    (classConstructor : DTR.GeneralConstructor) :
    Except String LF.GeneralReaction :=
  match compileGeneralBody classConstructor.body with

  | .error message =>
      .error message

  | .ok compiledBody =>
      .ok
        (assembleGeneralStartupReaction
          classConstructor
          compiledBody)

theorem compileGeneralConstructor_ok
    {classConstructor : DTR.GeneralConstructor}
    {compiledBody : LF.GeneralBody}
    (hBody :
      compileGeneralBody classConstructor.body =
        .ok compiledBody) :
    compileGeneralConstructor classConstructor =
      .ok
        (assembleGeneralStartupReaction
          classConstructor
          compiledBody) := by
  simp [
    compileGeneralConstructor,
    hBody
  ]

theorem compileGeneralConstructor_error
    {classConstructor : DTR.GeneralConstructor}
    {message : String}
    (hBody :
      compileGeneralBody classConstructor.body =
        .error message) :
    compileGeneralConstructor classConstructor =
      .error message := by
  simp [
    compileGeneralConstructor,
    hBody
  ]

/--
Translate every message server into its reaction, in source order.

Explicit recursion and no sort. `Relico/Translation/MultiStoreBasic.lean` compiles this
list in `priorityOrderedMessageServers` order; stage D deliberately does not, because
declaration order is observable in the target and the sort that realizes priority is stage
G's, together with the theorem that says what it achieves.
-/
def compileGeneralMessageServerReactions :
    List DTR.GeneralMessageServer →
    Except String (List LF.GeneralReaction)

  | [] =>
      .ok []

  | server :: remaining =>
      match compileGeneralMessageServerReaction server with

      | .error message =>
          .error message

      | .ok reaction =>
          match compileGeneralMessageServerReactions remaining with

          | .error message =>
              .error message

          | .ok compiledRemaining =>
              .ok
                (reaction ::
                  compiledRemaining)

@[simp]
theorem compileGeneralMessageServerReactions_nil :
    compileGeneralMessageServerReactions [] =
      .ok [] := by
  rfl

theorem compileGeneralMessageServerReactions_cons_ok
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {reaction : LF.GeneralReaction}
    {compiledRemaining : List LF.GeneralReaction}
    (hServer :
      compileGeneralMessageServerReaction server =
        .ok reaction)
    (hRemaining :
      compileGeneralMessageServerReactions remaining =
        .ok compiledRemaining) :
    compileGeneralMessageServerReactions
        (server :: remaining) =
      .ok
        (reaction ::
          compiledRemaining) := by
  simp [
    compileGeneralMessageServerReactions,
    hServer,
    hRemaining
  ]

theorem compileGeneralMessageServerReactions_cons_error_head
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {message : String}
    (hServer :
      compileGeneralMessageServerReaction server =
        .error message) :
    compileGeneralMessageServerReactions
        (server :: remaining) =
      .error message := by
  simp [
    compileGeneralMessageServerReactions,
    hServer
  ]

theorem compileGeneralMessageServerReactions_cons_error_tail
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {reaction : LF.GeneralReaction}
    {message : String}
    (hServer :
      compileGeneralMessageServerReaction server =
        .ok reaction)
    (hRemaining :
      compileGeneralMessageServerReactions remaining =
        .error message) :
    compileGeneralMessageServerReactions
        (server :: remaining) =
      .error message := by
  simp [
    compileGeneralMessageServerReactions,
    hServer,
    hRemaining
  ]

/-!
## Reactors and the program

The same two-step shape, and the place where stage D's boundary is written down: two empty
port lists on every reactor and one empty connection list on the program. §9.1 turns each
of the three into a theorem, so the stage that adds external sends has to break a proof
before it can compile.
-/

/--
Assemble one reactor from a class and its two already-compiled reaction groups.

The constructor's typed parameters become the **reactor's** parameters, which is Fig. 5's
`Reactor ::= reactor R (ParamList?)` production that stage C dropped — finding F22. Without
it, two instances of one class constructed with different arguments are indistinguishable
in the generated LF, so the paper's own class-to-reactor mapping loses information the
source had.

`inputPorts` and `outputPorts` are empty, and this is the single place stage D's boundary
lives. `knownRebecs` is read by nothing: a known rebec becomes a port only when something
sends on it, so a class that declares one and never uses it translates, which is what makes
the committed fixtures with unused known rebecs pass rather than fail.

One logical action per message server, in source order, and one reaction per message
server, in the same order. The two lists are generated by two functions from one list, and
§9.2 proves both orders are source order — the fixed starting point stage G's permutation
needs.
-/
def assembleGeneralReactor
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    LF.GeneralReactor where

  name :=
    reactorNameFor reactiveClass.name

  parameters :=
    reactiveClass.constructor.parameters.map
      compileGeneralTypedParameter

  inputPorts :=
    []

  outputPorts :=
    []

  stateVariables :=
    reactiveClass.stateVariables.map
      compileGeneralStateVariableDecl

  logicalActions :=
    reactiveClass.messageServers.map
      compileGeneralMessageServerAction

  startupReaction :=
    compiledStartupReaction

  messageReactions :=
    compiledMessageReactions

@[simp]
theorem assembleGeneralReactor_name
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        compiledStartupReaction
        compiledMessageReactions).name =
      reactorNameFor reactiveClass.name := by
  rfl

@[simp]
theorem assembleGeneralReactor_parameters
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        compiledStartupReaction
        compiledMessageReactions).parameters =
      reactiveClass.constructor.parameters.map
        compileGeneralTypedParameter := by
  rfl

@[simp]
theorem assembleGeneralReactor_inputPorts
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        compiledStartupReaction
        compiledMessageReactions).inputPorts =
      [] := by
  rfl

@[simp]
theorem assembleGeneralReactor_outputPorts
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        compiledStartupReaction
        compiledMessageReactions).outputPorts =
      [] := by
  rfl

@[simp]
theorem assembleGeneralReactor_stateVariables
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        compiledStartupReaction
        compiledMessageReactions).stateVariables =
      reactiveClass.stateVariables.map
        compileGeneralStateVariableDecl := by
  rfl

@[simp]
theorem assembleGeneralReactor_logicalActions
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        compiledStartupReaction
        compiledMessageReactions).logicalActions =
      reactiveClass.messageServers.map
        compileGeneralMessageServerAction := by
  rfl

@[simp]
theorem assembleGeneralReactor_startupReaction
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        compiledStartupReaction
        compiledMessageReactions).startupReaction =
      compiledStartupReaction := by
  rfl

@[simp]
theorem assembleGeneralReactor_messageReactions
    (reactiveClass : DTR.GeneralReactiveClass)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        compiledStartupReaction
        compiledMessageReactions).messageReactions =
      compiledMessageReactions := by
  rfl

/--
Translate one reactive class into one reactor.

The constructor is compiled before the message servers, so a class whose constructor and
whose first message server both send externally reports the constructor's refusal. Source
order again, and for the same reason as inside a body.
-/
def compileGeneralReactiveClass
    (reactiveClass : DTR.GeneralReactiveClass) :
    Except String LF.GeneralReactor :=
  match compileGeneralConstructor reactiveClass.constructor with

  | .error message =>
      .error message

  | .ok compiledStartupReaction =>
      match compileGeneralMessageServerReactions reactiveClass.messageServers with

      | .error message =>
          .error message

      | .ok compiledMessageReactions =>
          .ok
            (assembleGeneralReactor
              reactiveClass
              compiledStartupReaction
              compiledMessageReactions)

theorem compileGeneralReactiveClass_ok
    {reactiveClass : DTR.GeneralReactiveClass}
    {compiledStartupReaction : LF.GeneralReaction}
    {compiledMessageReactions : List LF.GeneralReaction}
    (hConstructor :
      compileGeneralConstructor reactiveClass.constructor =
        .ok compiledStartupReaction)
    (hMessageServers :
      compileGeneralMessageServerReactions reactiveClass.messageServers =
        .ok compiledMessageReactions) :
    compileGeneralReactiveClass reactiveClass =
      .ok
        (assembleGeneralReactor
          reactiveClass
          compiledStartupReaction
          compiledMessageReactions) := by
  simp [
    compileGeneralReactiveClass,
    hConstructor,
    hMessageServers
  ]

theorem compileGeneralReactiveClass_error_constructor
    {reactiveClass : DTR.GeneralReactiveClass}
    {message : String}
    (hConstructor :
      compileGeneralConstructor reactiveClass.constructor =
        .error message) :
    compileGeneralReactiveClass reactiveClass =
      .error message := by
  simp [
    compileGeneralReactiveClass,
    hConstructor
  ]

theorem compileGeneralReactiveClass_error_messageServers
    {reactiveClass : DTR.GeneralReactiveClass}
    {compiledStartupReaction : LF.GeneralReaction}
    {message : String}
    (hConstructor :
      compileGeneralConstructor reactiveClass.constructor =
        .ok compiledStartupReaction)
    (hMessageServers :
      compileGeneralMessageServerReactions reactiveClass.messageServers =
        .error message) :
    compileGeneralReactiveClass reactiveClass =
      .error message := by
  simp [
    compileGeneralReactiveClass,
    hConstructor,
    hMessageServers
  ]

/--
Translate every class into its reactor, in source order.
-/
def compileGeneralReactiveClasses :
    List DTR.GeneralReactiveClass →
    Except String (List LF.GeneralReactor)

  | [] =>
      .ok []

  | reactiveClass :: remaining =>
      match compileGeneralReactiveClass reactiveClass with

      | .error message =>
          .error message

      | .ok reactor =>
          match compileGeneralReactiveClasses remaining with

          | .error message =>
              .error message

          | .ok compiledRemaining =>
              .ok
                (reactor ::
                  compiledRemaining)

@[simp]
theorem compileGeneralReactiveClasses_nil :
    compileGeneralReactiveClasses [] =
      .ok [] := by
  rfl

theorem compileGeneralReactiveClasses_cons_ok
    {reactiveClass : DTR.GeneralReactiveClass}
    {remaining : List DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    {compiledRemaining : List LF.GeneralReactor}
    (hClass :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor)
    (hRemaining :
      compileGeneralReactiveClasses remaining =
        .ok compiledRemaining) :
    compileGeneralReactiveClasses
        (reactiveClass :: remaining) =
      .ok
        (reactor ::
          compiledRemaining) := by
  simp [
    compileGeneralReactiveClasses,
    hClass,
    hRemaining
  ]

theorem compileGeneralReactiveClasses_cons_error_head
    {reactiveClass : DTR.GeneralReactiveClass}
    {remaining : List DTR.GeneralReactiveClass}
    {message : String}
    (hClass :
      compileGeneralReactiveClass reactiveClass =
        .error message) :
    compileGeneralReactiveClasses
        (reactiveClass :: remaining) =
      .error message := by
  simp [
    compileGeneralReactiveClasses,
    hClass
  ]

theorem compileGeneralReactiveClasses_cons_error_tail
    {reactiveClass : DTR.GeneralReactiveClass}
    {remaining : List DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    {message : String}
    (hClass :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor)
    (hRemaining :
      compileGeneralReactiveClasses remaining =
        .error message) :
    compileGeneralReactiveClasses
        (reactiveClass :: remaining) =
      .error message := by
  simp [
    compileGeneralReactiveClasses,
    hClass,
    hRemaining
  ]

/--
Assemble the program from a model and its already-compiled reactors.

`connections := []` is the boundary from the other side: no external sends means no
connections, and stage C's connection layer sits unused and ready. The instances are total
— nothing about an actor instance can fail in stage D — so the only `Except` in reach of
this function is the one the reactors bring.
-/
def assembleGeneralProgram
    (model : DTR.GeneralModel)
    (compiledReactors : List LF.GeneralReactor) :
    LF.GeneralProgram where

  reactors :=
    compiledReactors

  instances :=
    model.instances.map
      compileGeneralActorInstance

  connections :=
    []

@[simp]
theorem assembleGeneralProgram_reactors
    (model : DTR.GeneralModel)
    (compiledReactors : List LF.GeneralReactor) :
    (assembleGeneralProgram
        model
        compiledReactors).reactors =
      compiledReactors := by
  rfl

@[simp]
theorem assembleGeneralProgram_instances
    (model : DTR.GeneralModel)
    (compiledReactors : List LF.GeneralReactor) :
    (assembleGeneralProgram
        model
        compiledReactors).instances =
      model.instances.map
        compileGeneralActorInstance := by
  rfl

@[simp]
theorem assembleGeneralProgram_connections
    (model : DTR.GeneralModel)
    (compiledReactors : List LF.GeneralReactor) :
    (assembleGeneralProgram
        model
        compiledReactors).connections =
      [] := by
  rfl

/--
Translate a model into a program.

The entry point of stage D.
-/
def compileGeneralModel
    (model : DTR.GeneralModel) :
    Except String LF.GeneralProgram :=
  match compileGeneralReactiveClasses model.classes with

  | .error message =>
      .error message

  | .ok compiledReactors =>
      .ok
        (assembleGeneralProgram
          model
          compiledReactors)

theorem compileGeneralModel_ok
    {model : DTR.GeneralModel}
    {compiledReactors : List LF.GeneralReactor}
    (hClasses :
      compileGeneralReactiveClasses model.classes =
        .ok compiledReactors) :
    compileGeneralModel model =
      .ok
        (assembleGeneralProgram
          model
          compiledReactors) := by
  simp [
    compileGeneralModel,
    hClasses
  ]

theorem compileGeneralModel_error
    {model : DTR.GeneralModel}
    {message : String}
    (hClasses :
      compileGeneralReactiveClasses model.classes =
        .error message) :
    compileGeneralModel model =
      .error message := by
  simp [
    compileGeneralModel,
    hClasses
  ]

/-!
## Inversion

Nothing in this repository inverts an `Except` before now — the existing inversion idiom,
in `Relico/Correctness/Inversion.lean`, builds an equation with `simpa` and takes it apart
with `injection`, and every compilation it applies to is total. So one idiom is invented
here and used without variation at all seven levels:

```
cases hStep : <the sub-computation> with
| error message => rw [<the error equation> hStep] at hCompiled; simp at hCompiled
| ok value     => rw [<the ok equation> hStep] at hCompiled; injection hCompiled with h
```

Each step is deterministic. `cases h : e` names the outcome, the forward equation rewrites
the *whole* compilation to a constructor application, `injection` — the repository's own
inversion tactic — takes the successful case apart, and the impossible case is closed by
`simp` on a constructor clash, which is how `Relico/Common/ActorTopology.lean` closes its
own impossible branches. No `Except.isOk`, which appears nowhere in this zero-dependency
development, and no reliance on how `simp` orients an equation: every result is stated with
an explicit `.symm` rather than left for normalization to arrange.

One measured correction to that idiom, because it cost a build. `cases h : e` does not only
name the outcome, it **generalizes `e` in the goal**. So in a theorem whose conclusion is
`∃ value, e = .ok value ∧ …`, the first conjunct reads `.ok value = .ok value` by the time
the branch is entered, and it is discharged by `rfl` — *not* by `h`, which no longer has the
goal's type. Twelve sites here were written the other way and every one failed with the same
application type mismatch, `h` offered where `Except.ok v = Except.ok v` was wanted. `h` is
still what the forward equation consumes; it is simply not what closes the goal.

These are `private`. They exist so §9's theorems can be proved by naming a sub-result, and
a later stage that needs one should extend this list deliberately rather than inherit it.
-/

private theorem exists_of_compileGeneralBody_cons_ok
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiled : LF.GeneralBody}
    (hCompiled :
      compileGeneralBody
          (statement :: remaining) =
        .ok compiled) :
    ∃ compiledStatement compiledRemaining,
      compileGeneralStmt statement =
          .ok compiledStatement ∧
        compileGeneralBody remaining =
            .ok compiledRemaining ∧
          compiled =
            compiledStatement ::
              compiledRemaining := by

  cases hStatement :
      compileGeneralStmt statement with

  | error message =>
      rw [
        compileGeneralBody_cons_error_head
          hStatement
      ] at hCompiled
      simp at hCompiled

  | ok compiledStatement =>
      cases hRemaining :
          compileGeneralBody remaining with

      | error message =>
          rw [
            compileGeneralBody_cons_error_tail
              hStatement
              hRemaining
          ] at hCompiled
          simp at hCompiled

      | ok compiledRemaining =>
          rw [
            compileGeneralBody_cons_ok
              hStatement
              hRemaining
          ] at hCompiled
          injection hCompiled with hResult
          exact
            ⟨
              compiledStatement,
              compiledRemaining,
              rfl,
              rfl,
              hResult.symm
            ⟩

private theorem exists_of_compileGeneralMessageServerReaction_ok
    {server : DTR.GeneralMessageServer}
    {reaction : LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReaction server =
        .ok reaction) :
    ∃ compiledBody,
      compileGeneralBody server.body =
          .ok compiledBody ∧
        reaction =
          assembleGeneralMessageReaction
            server
            compiledBody := by

  cases hBody :
      compileGeneralBody server.body with

  | error message =>
      rw [
        compileGeneralMessageServerReaction_error
          hBody
      ] at hCompiled
      simp at hCompiled

  | ok compiledBody =>
      rw [
        compileGeneralMessageServerReaction_ok
          hBody
      ] at hCompiled
      injection hCompiled with hResult
      exact
        ⟨
          compiledBody,
          rfl,
          hResult.symm
        ⟩

private theorem exists_of_compileGeneralConstructor_ok
    {classConstructor : DTR.GeneralConstructor}
    {reaction : LF.GeneralReaction}
    (hCompiled :
      compileGeneralConstructor classConstructor =
        .ok reaction) :
    ∃ compiledBody,
      compileGeneralBody classConstructor.body =
          .ok compiledBody ∧
        reaction =
          assembleGeneralStartupReaction
            classConstructor
            compiledBody := by

  cases hBody :
      compileGeneralBody classConstructor.body with

  | error message =>
      rw [
        compileGeneralConstructor_error
          hBody
      ] at hCompiled
      simp at hCompiled

  | ok compiledBody =>
      rw [
        compileGeneralConstructor_ok
          hBody
      ] at hCompiled
      injection hCompiled with hResult
      exact
        ⟨
          compiledBody,
          rfl,
          hResult.symm
        ⟩

private theorem eq_nil_of_compileGeneralMessageServerReactions_nil_ok
    {compiled : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactions [] =
        .ok compiled) :
    compiled = [] := by
  rw [
    compileGeneralMessageServerReactions_nil
  ] at hCompiled
  injection hCompiled with hResult
  exact hResult.symm

private theorem exists_of_compileGeneralMessageServerReactions_cons_ok
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {compiled : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactions
          (server :: remaining) =
        .ok compiled) :
    ∃ reaction compiledRemaining,
      compileGeneralMessageServerReaction server =
          .ok reaction ∧
        compileGeneralMessageServerReactions remaining =
            .ok compiledRemaining ∧
          compiled =
            reaction ::
              compiledRemaining := by

  cases hServer :
      compileGeneralMessageServerReaction server with

  | error message =>
      rw [
        compileGeneralMessageServerReactions_cons_error_head
          hServer
      ] at hCompiled
      simp at hCompiled

  | ok reaction =>
      cases hRemaining :
          compileGeneralMessageServerReactions remaining with

      | error message =>
          rw [
            compileGeneralMessageServerReactions_cons_error_tail
              hServer
              hRemaining
          ] at hCompiled
          simp at hCompiled

      | ok compiledRemaining =>
          rw [
            compileGeneralMessageServerReactions_cons_ok
              hServer
              hRemaining
          ] at hCompiled
          injection hCompiled with hResult
          exact
            ⟨
              reaction,
              compiledRemaining,
              rfl,
              rfl,
              hResult.symm
            ⟩

private theorem exists_of_compileGeneralReactiveClass_ok
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor) :
    ∃ compiledStartupReaction compiledMessageReactions,
      compileGeneralConstructor reactiveClass.constructor =
          .ok compiledStartupReaction ∧
        compileGeneralMessageServerReactions reactiveClass.messageServers =
            .ok compiledMessageReactions ∧
          reactor =
            assembleGeneralReactor
              reactiveClass
              compiledStartupReaction
              compiledMessageReactions := by

  cases hConstructor :
      compileGeneralConstructor reactiveClass.constructor with

  | error message =>
      rw [
        compileGeneralReactiveClass_error_constructor
          hConstructor
      ] at hCompiled
      simp at hCompiled

  | ok compiledStartupReaction =>
      cases hMessageServers :
          compileGeneralMessageServerReactions reactiveClass.messageServers with

      | error message =>
          rw [
            compileGeneralReactiveClass_error_messageServers
              hConstructor
              hMessageServers
          ] at hCompiled
          simp at hCompiled

      | ok compiledMessageReactions =>
          rw [
            compileGeneralReactiveClass_ok
              hConstructor
              hMessageServers
          ] at hCompiled
          injection hCompiled with hResult
          exact
            ⟨
              compiledStartupReaction,
              compiledMessageReactions,
              rfl,
              rfl,
              hResult.symm
            ⟩

private theorem eq_nil_of_compileGeneralReactiveClasses_nil_ok
    {compiled : List LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClasses [] =
        .ok compiled) :
    compiled = [] := by
  rw [
    compileGeneralReactiveClasses_nil
  ] at hCompiled
  injection hCompiled with hResult
  exact hResult.symm

private theorem exists_of_compileGeneralReactiveClasses_cons_ok
    {reactiveClass : DTR.GeneralReactiveClass}
    {remaining : List DTR.GeneralReactiveClass}
    {compiled : List LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClasses
          (reactiveClass :: remaining) =
        .ok compiled) :
    ∃ reactor compiledRemaining,
      compileGeneralReactiveClass reactiveClass =
          .ok reactor ∧
        compileGeneralReactiveClasses remaining =
            .ok compiledRemaining ∧
          compiled =
            reactor ::
              compiledRemaining := by

  cases hClass :
      compileGeneralReactiveClass reactiveClass with

  | error message =>
      rw [
        compileGeneralReactiveClasses_cons_error_head
          hClass
      ] at hCompiled
      simp at hCompiled

  | ok reactor =>
      cases hRemaining :
          compileGeneralReactiveClasses remaining with

      | error message =>
          rw [
            compileGeneralReactiveClasses_cons_error_tail
              hClass
              hRemaining
          ] at hCompiled
          simp at hCompiled

      | ok compiledRemaining =>
          rw [
            compileGeneralReactiveClasses_cons_ok
              hClass
              hRemaining
          ] at hCompiled
          injection hCompiled with hResult
          exact
            ⟨
              reactor,
              compiledRemaining,
              rfl,
              rfl,
              hResult.symm
            ⟩

private theorem exists_of_compileGeneralModel_ok
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    ∃ compiledReactors,
      compileGeneralReactiveClasses model.classes =
          .ok compiledReactors ∧
        program =
          assembleGeneralProgram
            model
            compiledReactors := by

  cases hClasses :
      compileGeneralReactiveClasses model.classes with

  | error message =>
      rw [
        compileGeneralModel_error
          hClasses
      ] at hCompiled
      simp at hCompiled

  | ok compiledReactors =>
      rw [
        compileGeneralModel_ok
          hClasses
      ] at hCompiled
      injection hCompiled with hResult
      exact
        ⟨
          compiledReactors,
          rfl,
          hResult.symm
        ⟩

/-!
## The boundary, as arithmetic

Three facts about stage D's output that this document would otherwise only assert: reactors
have no ports, programs have no connections, and the reactor list is the class list. When
stage E arrives, the first two are the theorems that must *change*, which is the cheapest
possible alarm that the boundary has moved — cheaper than a review, and it fires at build
time.
-/

/--
A compiled reactor declares no ports.
-/
theorem compileGeneralReactiveClass_ports
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor) :
    reactor.inputPorts =
        [] ∧
      reactor.outputPorts =
        [] := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      _,
      _,
      _,
      _,
      hReactor
    ⟩

  subst hReactor

  constructor <;>
    simp

/--
A compiled reactor is named after its class.
-/
theorem compileGeneralReactiveClass_name
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor) :
    reactor.name =
      reactorNameFor reactiveClass.name := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      _,
      _,
      _,
      _,
      hReactor
    ⟩

  subst hReactor
  simp

/--
No reactor of a compiled program declares a port.

The class-level statement is what the design asks for; this is the one the design's §8
argument actually uses, since the printer's refusals are justified by what a *program*
looks like. Membership rather than a list equality, because the property has to hold of an
arbitrary reactor a later proof picks out of the list.
-/
theorem compileGeneralReactiveClasses_ports :
    ∀ (classes : List DTR.GeneralReactiveClass)
      (compiled : List LF.GeneralReactor),
      compileGeneralReactiveClasses classes =
          .ok compiled →
        ∀ (reactor : LF.GeneralReactor),
          reactor ∈ compiled →
            reactor.inputPorts =
                [] ∧
              reactor.outputPorts =
                [] := by

  intro classes
  induction classes with

  | nil =>
      intro compiled hCompiled reactor hMember

      rw [
        eq_nil_of_compileGeneralReactiveClasses_nil_ok
          hCompiled
      ] at hMember

      cases hMember

  | cons reactiveClass remaining inductionHypothesis =>
      intro compiled hCompiled reactor hMember

      rcases
          exists_of_compileGeneralReactiveClasses_cons_ok
            hCompiled with
        ⟨
          compiledReactor,
          compiledRemaining,
          hClass,
          hRemaining,
          hCompiledEq
        ⟩

      subst hCompiledEq

      cases List.mem_cons.mp hMember with

      | inl hHead =>
          subst hHead

          exact
            compileGeneralReactiveClass_ports
              hClass

      | inr hTail =>
          exact
            inductionHypothesis
              compiledRemaining
              hRemaining
              reactor
              hTail

/--
A compiled program has no connections.

The theorem stage E has to break. It is `rfl` under the assembler, and that is the point of
routing the program through a total assembler in the first place: the empty connection list
is a property of a function with no failure case, so no branch of the partial layer can be
the one that quietly adds a connection.
-/
theorem compileGeneralModel_connections
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    program.connections =
      [] := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      _,
      _,
      hProgram
    ⟩

  subst hProgram
  simp

/--
A compiled program instantiates exactly the model's actors, in source order.
-/
theorem compileGeneralModel_instances
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    program.instances =
      model.instances.map
        compileGeneralActorInstance := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      _,
      _,
      hProgram
    ⟩

  subst hProgram
  simp

/--
No reactor of a compiled program declares a port.
-/
theorem compileGeneralModel_ports
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    ∀ (reactor : LF.GeneralReactor),
      reactor ∈ program.reactors →
        reactor.inputPorts =
            [] ∧
          reactor.outputPorts =
            [] := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      compiledReactors,
      hClasses,
      hProgram
    ⟩

  subst hProgram

  intro reactor hMember

  rw [
    assembleGeneralProgram_reactors
  ] at hMember

  exact
    compileGeneralReactiveClasses_ports
      model.classes
      compiledReactors
      hClasses
      reactor
      hMember

/--
The reactor names of a compiled class list are the class names, in source order.
-/
theorem compileGeneralReactiveClasses_reactorNames :
    ∀ (classes : List DTR.GeneralReactiveClass)
      (compiled : List LF.GeneralReactor),
      compileGeneralReactiveClasses classes =
          .ok compiled →
        compiled.map
            (fun reactor =>
              reactor.name) =
          classes.map
            (fun reactiveClass =>
              reactorNameFor reactiveClass.name) := by

  intro classes
  induction classes with

  | nil =>
      intro compiled hCompiled

      simp [
        eq_nil_of_compileGeneralReactiveClasses_nil_ok
          hCompiled
      ]

  | cons reactiveClass remaining inductionHypothesis =>
      intro compiled hCompiled

      rcases
          exists_of_compileGeneralReactiveClasses_cons_ok
            hCompiled with
        ⟨
          reactor,
          compiledRemaining,
          hClass,
          hRemaining,
          hCompiledEq
        ⟩

      subst hCompiledEq

      simp [
        compileGeneralReactiveClass_name
          hClass,
        inductionHypothesis
          compiledRemaining
          hRemaining
      ]

/--
A compiled program declares one reactor per class, named after that class, in source order.

Not merely the same *set* of names: the equality is between two `map`s over the same list,
so it fixes the order too. Stage F's fan-in work has to name a reactor by position in
several places at once, and this is what makes that reference stable.
-/
theorem compileGeneralModel_reactorNames
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    program.reactors.map
        (fun reactor =>
          reactor.name) =
      model.classes.map
        (fun reactiveClass =>
          reactorNameFor reactiveClass.name) := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      compiledReactors,
      hClasses,
      hProgram
    ⟩

  subst hProgram

  rw [
    assembleGeneralProgram_reactors
  ]

  exact
    compileGeneralReactiveClasses_reactorNames
      model.classes
      compiledReactors
      hClasses

/-!
## Order preservation

These look like bookkeeping and are not. Reaction *declaration order* is the only
deterministic ordering hook the target gives us — measured: swapping two reaction
declarations swaps their same-tag execution order — so stage G's priority work will be a
permutation of `messageReactions`. Proving now that stage D's order **is** source order
gives stage G a fixed starting point to permute away from, and turns any accidental
reordering in between into a failing proof rather than a silent behavioural change.

Each is proved by induction with `change` and `congrArg`, the pattern of
`Store.keys_mapValuesWithKey`, rather than by `simp [List.map_map]`. Both work; the
induction does not depend on how the simp set normalizes a composition under a binder,
and this file cannot be elaborated where it is written.
-/

/--
Deriving the actions of a message-server list preserves names and order.
-/
theorem compileGeneralMessageServerAction_names :
    ∀ (servers : List DTR.GeneralMessageServer),
      (servers.map
          compileGeneralMessageServerAction).map
          (fun action =>
            action.name) =
        servers.map
          (fun server =>
            actionNameFor server.name) := by

  intro servers
  induction servers with

  | nil =>
      rfl

  | cons server remaining inductionHypothesis =>
      change
        actionNameFor server.name ::
            (remaining.map
                compileGeneralMessageServerAction).map
                (fun action =>
                  action.name) =
          actionNameFor server.name ::
            remaining.map
              (fun candidate =>
                actionNameFor candidate.name)

      exact
        congrArg
          (List.cons
            (actionNameFor server.name))
          inductionHypothesis

/--
Translating typed parameters preserves names and order.
-/
theorem compileGeneralTypedParameter_names :
    ∀ (parameters : List DTR.GeneralTypedParameter),
      (parameters.map
          compileGeneralTypedParameter).map
          (fun parameter =>
            parameter.name) =
        parameters.map
          (fun parameter =>
            parameter.name) := by

  intro parameters
  induction parameters with

  | nil =>
      rfl

  | cons parameter remaining inductionHypothesis =>
      change
        parameter.name ::
            (remaining.map
                compileGeneralTypedParameter).map
                (fun candidate =>
                  candidate.name) =
          parameter.name ::
            remaining.map
              (fun candidate =>
                candidate.name)

      exact
        congrArg
          (List.cons parameter.name)
          inductionHypothesis

/--
Translating state-variable declarations preserves names and order.
-/
theorem compileGeneralStateVariableDecl_names :
    ∀ (declarations : List DTR.GeneralStateVariableDecl),
      (declarations.map
          compileGeneralStateVariableDecl).map
          (fun declaration =>
            declaration.name) =
        declarations.map
          (fun declaration =>
            declaration.name) := by

  intro declarations
  induction declarations with

  | nil =>
      rfl

  | cons declaration remaining inductionHypothesis =>
      change
        declaration.name ::
            (remaining.map
                compileGeneralStateVariableDecl).map
                (fun candidate =>
                  candidate.name) =
          declaration.name ::
            remaining.map
              (fun candidate =>
                candidate.name)

      exact
        congrArg
          (List.cons declaration.name)
          inductionHypothesis

/--
Compiled reactions carry the message-reaction names of their message servers, in source
order.

The `Except` counterpart of the three lemmas above: the reaction list is not a `map` of the
server list, because compilation of a body can fail, so the induction has to invert a
successful compilation at each step. That is what the private inversion lemmas are for.
-/
theorem compileGeneralMessageServerReactions_names :
    ∀ (servers : List DTR.GeneralMessageServer)
      (compiled : List LF.GeneralReaction),
      compileGeneralMessageServerReactions servers =
          .ok compiled →
        compiled.map
            (fun reaction =>
              reaction.name) =
          servers.map
            (fun server =>
              messageReactionNameFor server.name) := by

  intro servers
  induction servers with

  | nil =>
      intro compiled hCompiled

      simp [
        eq_nil_of_compileGeneralMessageServerReactions_nil_ok
          hCompiled
      ]

  | cons server remaining inductionHypothesis =>
      intro compiled hCompiled

      rcases
          exists_of_compileGeneralMessageServerReactions_cons_ok
            hCompiled with
        ⟨
          reaction,
          compiledRemaining,
          hServer,
          hRemaining,
          hCompiledEq
        ⟩

      rcases
          exists_of_compileGeneralMessageServerReaction_ok
            hServer with
        ⟨
          compiledBody,
          _,
          hReaction
        ⟩

      subst hCompiledEq
      subst hReaction

      change
        messageReactionNameFor server.name ::
            compiledRemaining.map
              (fun candidate =>
                candidate.name) =
          messageReactionNameFor server.name ::
            remaining.map
              (fun candidate =>
                messageReactionNameFor candidate.name)

      exact
        congrArg
          (List.cons
            (messageReactionNameFor server.name))
          (inductionHypothesis
            compiledRemaining
            hRemaining)

/--
A compiled reactor declares one logical action per message server, named after it, in
source order.
-/
theorem compileGeneralReactiveClass_actionNames
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor) :
    reactor.logicalActions.map
        (fun action =>
          action.name) =
      reactiveClass.messageServers.map
        (fun server =>
          actionNameFor server.name) := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      _,
      _,
      _,
      _,
      hReactor
    ⟩

  subst hReactor

  rw [
    assembleGeneralReactor_logicalActions
  ]

  exact
    compileGeneralMessageServerAction_names
      reactiveClass.messageServers

/--
A compiled reactor declares one message reaction per message server, named after it, in
source order.

This is the theorem stage G permutes. Nothing here sorts, so the order on the right is the
order the source was written in.
-/
theorem compileGeneralReactiveClass_reactionNames
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor) :
    reactor.messageReactions.map
        (fun reaction =>
          reaction.name) =
      reactiveClass.messageServers.map
        (fun server =>
          messageReactionNameFor server.name) := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      _,
      compiledMessageReactions,
      _,
      hMessageServers,
      hReactor
    ⟩

  subst hReactor

  rw [
    assembleGeneralReactor_messageReactions
  ]

  exact
    compileGeneralMessageServerReactions_names
      reactiveClass.messageServers
      compiledMessageReactions
      hMessageServers

/--
A compiled reactor's state variables are the class's, by name and in order.

The types are not compared here, and `compileGeneralStateVariableDecl_declaredType` is the
lemma that does that; separating them is what lets a later well-formedness proof reason
about the reactor's *name scope* without dragging types through it.
-/
theorem compileGeneralReactiveClass_stateVariableNames
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor) :
    reactor.stateVariables.map
        (fun declaration =>
          declaration.name) =
      reactiveClass.stateVariables.map
        (fun declaration =>
          declaration.name) := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      _,
      _,
      _,
      _,
      hReactor
    ⟩

  subst hReactor

  rw [
    assembleGeneralReactor_stateVariables
  ]

  exact
    compileGeneralStateVariableDecl_names
      reactiveClass.stateVariables

/--
The startup reaction's parameters are exactly the reactor's parameter names.

The agreement that makes a generated startup body legal. A Rebeca constructor's formals are
in scope in the constructor body, and their LF counterparts are reactor *members* — a
reactor parameter is readable in a reaction body with no trigger and no local declaration,
measured — so `exprWellFormed`'s `.parameterVar` clause, which resolves against the
reaction's own parameter list, succeeds precisely because these two lists agree. Stated as a
theorem because it is otherwise a coincidence between two `map`s in one structure
assembler.
-/
theorem compileGeneralReactiveClass_startupParameters
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor) :
    reactor.startupReaction.parameters =
      reactor.parameters.map
        (fun parameter =>
          parameter.name) := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      compiledStartupReaction,
      _,
      hConstructor,
      _,
      hReactor
    ⟩

  rcases
      exists_of_compileGeneralConstructor_ok
        hConstructor with
    ⟨
      compiledBody,
      _,
      hStartupReaction
    ⟩

  subst hReactor
  subst hStartupReaction

  rw [
    assembleGeneralReactor_startupReaction,
    assembleGeneralReactor_parameters,
    assembleGeneralStartupReaction_parameters
  ]

  exact
    (compileGeneralTypedParameter_names
      reactiveClass.constructor.parameters).symm

/-!
## The refusal surface, exactly

`docs/STAGE_D_DESIGN.md` §9.3 asks for an iff: a model translates if and only if it contains
no external send. Both directions are proved here in full, so the fallback the design allows
— *"prove right-to-left in full and state left-to-right for the shapes the gate exercises"*
— was not needed and is not taken.

The right-hand side is the executable `Bool` predicate rather than `Except.isOk`, which
appears nowhere in this development, and the left-hand side is `∃ program, … = .ok program`
rather than a negation, so no proof below has to reason about the `false` side of `Bool`
algebra. Each level gets a pair: `exists_of_…SelfSendOnly` builds a successful compilation
out of the predicate, and `…SelfSendOnly_of_ok` reads the predicate back off a successful
compilation. The second direction is the load-bearing one — it is what makes the refusal
*complete*, i.e. rules out a construct this stage silently mistranslates instead of
refusing.

Why this is worth proving rather than reading off `compileGeneralStmt`: the claim is about
the whole pipeline, and the six intermediate levels each have three outcome equations. A
reader checking by eye has to confirm that no other arm anywhere returns `.error` *and* that
no arm returns `.ok` on an external send. The induction does both at once, and stage E will
find out from a build failure rather than a review when it moves the boundary.
-/

/--
A statement outside the refusal surface compiles.
-/
theorem exists_of_generalStmtSelfSendOnly
    {statement : DTR.GeneralStmt}
    (hSelfSendOnly :
      generalStmtSelfSendOnly statement =
        true) :
    ∃ compiled,
      compileGeneralStmt statement =
        .ok compiled := by

  cases statement with

  | assign _ _ =>
      exact ⟨_, rfl⟩

  | send target _ _ _ =>

      cases target with

      | selfTarget =>
          exact ⟨_, rfl⟩

      | knownRebec _ =>
          simp [
            generalStmtSelfSendOnly
          ] at hSelfSendOnly

/--
A statement that compiles is outside the refusal surface.
-/
theorem generalStmtSelfSendOnly_of_ok
    {statement : DTR.GeneralStmt}
    {compiled : LF.GeneralStmt}
    (hCompiled :
      compileGeneralStmt statement =
        .ok compiled) :
    generalStmtSelfSendOnly statement =
      true := by

  cases statement with

  | assign _ _ =>
      rfl

  | send target _ _ _ =>

      cases target with

      | selfTarget =>
          rfl

      | knownRebec _ =>
          simp [
            compileGeneralStmt
          ] at hCompiled

/--
A body containing no external send compiles.
-/
theorem exists_of_generalBodySelfSendOnly :
    ∀ (body : DTR.GeneralBody),
      generalBodySelfSendOnly body =
        true →
      ∃ compiled,
        compileGeneralBody body =
          .ok compiled := by

  intro body
  induction body with

  | nil =>
      intro _
      exact ⟨[], rfl⟩

  | cons statement remaining inductionHypothesis =>
      intro hSelfSendOnly

      simp only [
        generalBodySelfSendOnly_cons,
        Bool.and_eq_true
      ] at hSelfSendOnly

      rcases
          exists_of_generalStmtSelfSendOnly
            hSelfSendOnly.left with
        ⟨
          compiledStatement,
          hStatement
        ⟩

      rcases
          inductionHypothesis
            hSelfSendOnly.right with
        ⟨
          compiledRemaining,
          hRemaining
        ⟩

      exact
        ⟨
          compiledStatement ::
            compiledRemaining,
          compileGeneralBody_cons_ok
            hStatement
            hRemaining
        ⟩

/--
A body that compiles contains no external send.
-/
theorem generalBodySelfSendOnly_of_ok :
    ∀ (body : DTR.GeneralBody)
      (compiled : LF.GeneralBody),
      compileGeneralBody body =
        .ok compiled →
      generalBodySelfSendOnly body =
        true := by

  intro body
  induction body with

  | nil =>
      intro _ _
      rfl

  | cons statement remaining inductionHypothesis =>
      intro _ hCompiled

      rcases
          exists_of_compileGeneralBody_cons_ok
            hCompiled with
        ⟨
          compiledStatement,
          compiledRemaining,
          hStatement,
          hRemaining,
          _
        ⟩

      simp [
        generalStmtSelfSendOnly_of_ok
          hStatement,
        inductionHypothesis
          compiledRemaining
          hRemaining
      ]

/--
A message-server list containing no external send compiles.
-/
theorem exists_of_generalMessageServersSelfSendOnly :
    ∀ (servers : List DTR.GeneralMessageServer),
      generalMessageServersSelfSendOnly servers =
        true →
      ∃ compiled,
        compileGeneralMessageServerReactions servers =
          .ok compiled := by

  intro servers
  induction servers with

  | nil =>
      intro _
      exact ⟨[], rfl⟩

  | cons server remaining inductionHypothesis =>
      intro hSelfSendOnly

      simp only [
        generalMessageServersSelfSendOnly_cons,
        Bool.and_eq_true
      ] at hSelfSendOnly

      rcases
          exists_of_generalBodySelfSendOnly
            server.body
            hSelfSendOnly.left with
        ⟨
          compiledBody,
          hBody
        ⟩

      rcases
          inductionHypothesis
            hSelfSendOnly.right with
        ⟨
          compiledRemaining,
          hRemaining
        ⟩

      exact
        ⟨
          _,
          compileGeneralMessageServerReactions_cons_ok
            (compileGeneralMessageServerReaction_ok
              hBody)
            hRemaining
        ⟩

/--
A message-server list that compiles contains no external send.
-/
theorem generalMessageServersSelfSendOnly_of_ok :
    ∀ (servers : List DTR.GeneralMessageServer)
      (compiled : List LF.GeneralReaction),
      compileGeneralMessageServerReactions servers =
        .ok compiled →
      generalMessageServersSelfSendOnly servers =
        true := by

  intro servers
  induction servers with

  | nil =>
      intro _ _
      rfl

  | cons server remaining inductionHypothesis =>
      intro _ hCompiled

      rcases
          exists_of_compileGeneralMessageServerReactions_cons_ok
            hCompiled with
        ⟨
          reaction,
          compiledRemaining,
          hServer,
          hRemaining,
          _
        ⟩

      rcases
          exists_of_compileGeneralMessageServerReaction_ok
            hServer with
        ⟨
          compiledBody,
          hBody,
          _
        ⟩

      simp [
        generalBodySelfSendOnly_of_ok
          server.body
          compiledBody
          hBody,
        inductionHypothesis
          compiledRemaining
          hRemaining
      ]

/--
A class containing no external send compiles.
-/
theorem exists_of_generalClassSelfSendOnly
    {reactiveClass : DTR.GeneralReactiveClass}
    (hSelfSendOnly :
      generalClassSelfSendOnly reactiveClass =
        true) :
    ∃ reactor,
      compileGeneralReactiveClass reactiveClass =
        .ok reactor := by

  simp only [
    generalClassSelfSendOnly,
    Bool.and_eq_true
  ] at hSelfSendOnly

  rcases
      exists_of_generalBodySelfSendOnly
        reactiveClass.constructor.body
        hSelfSendOnly.left with
    ⟨
      compiledBody,
      hBody
    ⟩

  rcases
      exists_of_generalMessageServersSelfSendOnly
        reactiveClass.messageServers
        hSelfSendOnly.right with
    ⟨
      compiledMessageReactions,
      hMessageServers
    ⟩

  exact
    ⟨
      _,
      compileGeneralReactiveClass_ok
        (compileGeneralConstructor_ok
          hBody)
        hMessageServers
    ⟩

/--
A class that compiles contains no external send.
-/
theorem generalClassSelfSendOnly_of_ok
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass reactiveClass =
        .ok reactor) :
    generalClassSelfSendOnly reactiveClass =
      true := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      _,
      compiledMessageReactions,
      hConstructor,
      hMessageServers,
      _
    ⟩

  rcases
      exists_of_compileGeneralConstructor_ok
        hConstructor with
    ⟨
      compiledBody,
      hBody,
      _
    ⟩

  simp [
    generalClassSelfSendOnly,
    generalBodySelfSendOnly_of_ok
      reactiveClass.constructor.body
      compiledBody
      hBody,
    generalMessageServersSelfSendOnly_of_ok
      reactiveClass.messageServers
      compiledMessageReactions
      hMessageServers
  ]

/--
A class list containing no external send compiles.
-/
theorem exists_of_generalClassesSelfSendOnly :
    ∀ (classes : List DTR.GeneralReactiveClass),
      generalClassesSelfSendOnly classes =
        true →
      ∃ compiled,
        compileGeneralReactiveClasses classes =
          .ok compiled := by

  intro classes
  induction classes with

  | nil =>
      intro _
      exact ⟨[], rfl⟩

  | cons reactiveClass remaining inductionHypothesis =>
      intro hSelfSendOnly

      simp only [
        generalClassesSelfSendOnly_cons,
        Bool.and_eq_true
      ] at hSelfSendOnly

      rcases
          exists_of_generalClassSelfSendOnly
            hSelfSendOnly.left with
        ⟨
          reactor,
          hClass
        ⟩

      rcases
          inductionHypothesis
            hSelfSendOnly.right with
        ⟨
          compiledRemaining,
          hRemaining
        ⟩

      exact
        ⟨
          reactor ::
            compiledRemaining,
          compileGeneralReactiveClasses_cons_ok
            hClass
            hRemaining
        ⟩

/--
A class list that compiles contains no external send.
-/
theorem generalClassesSelfSendOnly_of_ok :
    ∀ (classes : List DTR.GeneralReactiveClass)
      (compiled : List LF.GeneralReactor),
      compileGeneralReactiveClasses classes =
        .ok compiled →
      generalClassesSelfSendOnly classes =
        true := by

  intro classes
  induction classes with

  | nil =>
      intro _ _
      rfl

  | cons reactiveClass remaining inductionHypothesis =>
      intro _ hCompiled

      rcases
          exists_of_compileGeneralReactiveClasses_cons_ok
            hCompiled with
        ⟨
          reactor,
          compiledRemaining,
          hClass,
          hRemaining,
          _
        ⟩

      simp [
        generalClassSelfSendOnly_of_ok
          hClass,
        inductionHypothesis
          compiledRemaining
          hRemaining
      ]

/--
A model inside stage D's fragment compiles.
-/
theorem exists_of_generalModelSelfSendOnly
    {model : DTR.GeneralModel}
    (hSelfSendOnly :
      generalModelSelfSendOnly model =
        true) :
    ∃ program,
      compileGeneralModel model =
        .ok program := by

  unfold generalModelSelfSendOnly at hSelfSendOnly

  rcases
      exists_of_generalClassesSelfSendOnly
        model.classes
        hSelfSendOnly with
    ⟨
      compiledReactors,
      hClasses
    ⟩

  exact
    ⟨
      _,
      compileGeneralModel_ok
        hClasses
    ⟩

/--
A model that compiles is inside stage D's fragment.
-/
theorem generalModelSelfSendOnly_of_ok
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    generalModelSelfSendOnly model =
      true := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      compiledReactors,
      hClasses,
      _
    ⟩

  unfold generalModelSelfSendOnly

  exact
    generalClassesSelfSendOnly_of_ok
      model.classes
      compiledReactors
      hClasses

/--
Stage D's fragment, characterized exactly: a model translates precisely when no body in it
sends to a known rebec.

The theorem `docs/STAGE_D_DESIGN.md` §9.3 asks for, and the one that makes *"stage D
translates self-sends only"* a fact rather than a description of the code. Read left to
right it says the refusal is complete — there is no external send this stage quietly
mistranslates. Read right to left it says the refusal is minimal — nothing else is refused,
so a class declaring unused known rebecs, an instance with any arguments, and any binding
list all still translate.

Stage E will have to *delete* this theorem rather than generalize it, since external sends
will then translate. That is the intended alarm: the fragment boundary is a proof
obligation, not a comment.
-/
theorem compileGeneralModel_ok_iff_selfSendOnly
    (model : DTR.GeneralModel) :
    (∃ program,
        compileGeneralModel model =
          .ok program) ↔
      generalModelSelfSendOnly model =
        true :=
  Iff.intro
    (fun ⟨_, hCompiled⟩ =>
      generalModelSelfSendOnly_of_ok
        hCompiled)
    (fun hSelfSendOnly =>
      exists_of_generalModelSelfSendOnly
        hSelfSendOnly)

/--
A model outside the fragment gets a diagnostic.

The other half of totality, and the shape the gate's negative assertion mirrors: refusal is
reported, never a partial program. Stated separately from the iff because a `¬ ∃` reading of
that theorem would leave the `.error` case as an inference about `Except` having two
constructors, which is exactly the kind of step this file makes explicit everywhere else.
-/
theorem exists_error_of_not_generalModelSelfSendOnly
    {model : DTR.GeneralModel}
    (hSelfSendOnly :
      generalModelSelfSendOnly model =
        false) :
    ∃ message,
      compileGeneralModel model =
        .error message := by

  cases hCompiled :
      compileGeneralModel model with

  | error message =>
      exact ⟨message, rfl⟩

  | ok _ =>
      rw [
        generalModelSelfSendOnly_of_ok
          hCompiled
      ] at hSelfSendOnly
      simp at hSelfSendOnly

end Translation
end Relico
