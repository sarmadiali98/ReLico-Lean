import Relico.DTR.GeneralSyntax
import Relico.LF.GeneralSyntax
import Relico.LF.GeneralWellFormed
import Relico.Translation.GeneralRouting
import Relico.Translation.NameGeneration

set_option autoImplicit false

namespace Relico
namespace Translation

/-!
# Stage E: translating the general DTR family into the general LF family

Everything a general DTR model contains, with no statement form left refused. A `.send` to
`self` becomes a `schedule` on a logical action, which is §III-E's own rule for a self-send; a
`.send` to a *known rebec* becomes a `setPort` on the output port that belongs to that
individual **send site**, and the arrow that carries it is a row in the routing table
`Relico/Translation/GeneralRouting.lean` builds.

Stage D wrote of its three boundary theorems that *"the stage that adds external sends has to
break `compileGeneralModel_connections` before it can compile"*. It did, on schedule. All three
are restated below as the projections they have become; the empty-list forms are **gone** rather
than weakened, because a theorem saying that ports may be empty would be worth nothing.

## What stage D put here that stage E leaves alone

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
partial function computes its sub-results and hands them to a total assembler, so every
structural field becomes an `rfl` fact about a function that cannot fail and every
inversion lemma has exactly one right-hand side to name. Stage E gains from this twice
over: the fields that used to be `rfl`-empty are now `rfl`-equal to a routing projection,
and no inversion lemma changed shape to say so.

Nothing here sorts anything, which is the difference worth stating against
`Relico/Translation/MultiStoreBasic.lean`: that family compiles message servers in
`priorityOrderedMessageServers` order. Reaction declaration order is observable in the
target — measured, not assumed — so the sort that would realize local message-server
priority is a semantic act, and it belongs to the stage that also proves what it
achieves. Source order is emitted and `DTR.GeneralMessageServer.priority` is dropped.
`assembleGeneralMessageReaction_priority` records that drop as a theorem, so stage G
cannot wire the field without breaking a proof.

## What stage E changed, and why each choice was forced

**Statement compilation is parameterized by a resolution rather than performing a lookup.**
§7.1: *"resolve once per class, then compile against the resolution"*. `compileGeneralStmt`
takes the sending class's `GeneralOutputPortEnv` and the **address** of the statement it is
compiling, and reads the port out of the environment. Resolving inside the `.send` arm would
make every statement-level lemma quantify over a whole class, and would recompute the port
name at each of the four sites that have to agree on it.

The address is `GeneralBodyKey` plus the statement's 0-based position in its body's statement
list — a position, *not* a count of the sends before it, so the indices that name send sites
are sparse and no `cons` lemma acquires an arithmetic side condition.
`docs/STAGE_E_DESIGN.md` §4.1 says instead that the index *"counts external sends only"*;
§7.1, which is the section that fixes the interface, says position; the code follows §7.1 and
the divergence is recorded here because §4.1 is the more quotable of the two. Both readings
agree on every body with at most one external send, which is every fixture inherited from
stage D, so no committed port name moves.

**A receiving class gets one reaction per incoming arrow** (§7.3), named after the input port
that triggers it, in route order, grouped immediately behind the action reaction of the same
message server. This is not an optimization or a convenience: without these reactions the
input ports this file now declares would have no consumer, every external send would set a
port nothing reads, and the translation would deliver nothing while passing every check.

Two stage D theorems are **false** as a consequence, and they are replaced rather than
weakened. `compileGeneralMessageServerReactions_names` and
`compileGeneralReactiveClass_reactionNames` both said that a class's reaction names are
`messageServers.map messageReactionNameFor`. The replacements are stated per *group* — the
names of one message server's reactions, and route order within them — because the
class-level statement now needs a flattening combinator, and `List.flatMap` is exactly the
kind of core name this development has twice paid for trusting: see the notes on
`String.capitalize` in `Relico/Translation/NameGeneration.lean` and on `List.enum` in the
routing module. The concatenation lemma that composes the groups is the existing
`_cons_ok`-shaped one, which needs no combinator at all.

**The translation decides `LF.GeneralProgram.wellFormed` on its own output and refuses.**
F32's third road, chosen by the user from the three the design set out. `guardGeneralProgram`
is the last step of `compileGeneralModel`, so preservation becomes a theorem with no extra
hypothesis and no cross-layer import: this file still imports DTR **syntax** only. It costs
one new import, `Relico.LF.GeneralWellFormed`, which imports LF syntax alone and therefore
cannot cycle.

Two details of that guard are deliberate. The decision is written `match program.wellFormed
with` rather than `if program.wellFormed then`, so the discriminant stays a `Bool` with no
`Bool → Prop` coercion and each branch gives an inversion lemma one equation to name. And the
*explanation* is a separate total function, `generalProgramExplanation`, which walks a list
mirroring `wellFormed`'s nine conjuncts and returns the first that fails: §9 requires a
message that says which conjunct failed, and the decision on its own yields one bit. The
mirror can drift from what it mirrors, and rather than leave that as a silence it has a
fallback string that names its own drift, so a tenth conjunct added upstream and not here
reports itself in the gate log instead of producing an empty complaint. What the mirror
cannot do is make the guard unsound, because the guard does not consult it.

**The self-send characterization chain is deleted, not weakened.** Some twenty-two
declarations, ending in `compileGeneralModel_ok_iff_selfSendOnly`, said that this file accepts
a model exactly when every send in it targets `self`. The left-to-right direction is now false
in the intended direction, and there is no honest weakening of it, because the predicate it
was stated about has stopped being a property this file has any interest in. §10.1 lists the
whole chain. What takes its place is §8's sufficient condition for acceptance, a statement
about the guard rather than about send targets.

**Two theorems the design asks for are deliberately not in this commit**, and the reason is
diagnosability rather than difficulty. §10.2's headline invariant — no reaction sets one
output port twice — and §8's sufficient condition both rest on a single induction: every
external send site of a class has an entry in that class's environment, so
`compileGeneralStmt`'s defensive refusal is unreachable. That induction is long, and landing
it beside the definitions it is about would mean debugging it against a module that has never
elaborated, where a gate failure cannot be attributed. Definitions and cheap theorems land
first, the module goes green, and the induction lands against something that compiles. The
defensive arm's own refusal text says as much, by name.

`compileGeneralModel_targetEndpointsUnique` is therefore present in its guard-corollary form:
true, but *checked* rather than earned by construction. That is the F37 weakening turning up
in a new place, and it is worth naming as a weakening each time it does.
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

/-!
### Two of the nine are defined in `Relico/Translation/GeneralRouting.lean`

`compileGeneralType` and `compileGeneralTypedParameter` are not in this file. Stage E moved
them, because a port's payload is built from a message server's formals and the routing
layer cannot import this one. The namespace is the same, so every call below still reads
`compileGeneralType` and `compileGeneralTypedParameter` unqualified, and the simp lemmas
about them are still stated here. This note stands where the first of the two used to be,
so that a reader following the count above finds out where they went.
-/
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
## Where the fragment predicate used to be

Stage D kept a family of six executable `Bool` predicates here — `generalStmtSelfSendOnly`,
`generalBodySelfSendOnly`, `generalMessageServersSelfSendOnly`, `generalClassSelfSendOnly`,
`generalClassesSelfSendOnly` and `generalModelSelfSendOnly` — and §9.3 of its design pinned
the refusal surface with an `iff` between the last of them and acceptance by this file. Stage
E deletes all six, along with the proof chain at the end of this file that related them to
compilation. `docs/STAGE_E_DESIGN.md` §10.1 lists every deleted name.

The deletion gets a paragraph because weakening was available and would have been worse. The
predicates remain definable and one direction of the `iff` remains provable, so a reader may
fairly ask why they were not simply kept in a weaker form. Because the property they name —
every send in the model targets `self` — has stopped describing anything about this
translation. It *was* the refusal surface. The refusal surface is now a guard on the
translated program's own well-formedness: a different predicate, about a different object, at
a different layer. A weakened implication left behind here would be a definition whose purpose
a later reader would have to reconstruct out of a proof, and reconstructing purpose from
proofs is precisely how a stale handoff sends a session chasing work that has already landed.

Three things those predicates carried are not lost with them. That a class may *declare*
known rebecs and send on none of them stays true, stays deliberate, and stays exercised by
committed fixtures — a known rebec becomes a port only when something sends on it. That the
DTR side is asked no questions here beyond the ones this file can answer from syntax stays
true and is now visible in the import list rather than argued in a docstring. And the reason
those predicates were `Bool` rather than `Prop` — so that the bridge test main could assert
the two halves of an `iff` on real input instead of only in the abstract — is inherited
wholesale by `LF.GeneralProgram.wellFormed`, which the guard below decides and the bridge main
already evaluates on every build.
-/

/-!
## The partial layer

`Except String` from here down, and exactly one function introduces a failure. Everything
below `compileGeneralStmt` only propagates one, which §10 states as theorems rather than
leaving as a reading of the code.

Stage E keeps that shape exactly and changes what the one failure *is*. Stage D's failure was
the external send itself, reachable from any model with an `r.m()` anywhere in it. Stage E's is
a send site with no entry in its own class's resolved environment, which §7.2's construction
makes unreachable and which #47 proves unreachable. Not one propagation theorem had to change
to accommodate that swap, and that is the payoff of stage D having stated propagation
separately from the thing being propagated.
-/

/--
Translate a statement, at the address it occupies in its body.

A self-send becomes a `schedule` on the logical action derived from the message name,
which is §III-E's rule and not a choice: a self-send has to arrive at a later tag in the
same reactor, and a logical action is the only construct that does that without a
connection.

An external send becomes a `setPort` on the port belonging to **this send site**, read out of
the sending class's already-resolved environment. §7.1 fixes that interface — *"resolve once
per class, then compile against the resolution"* — and the two arguments carrying the address
are what let this stay a total function of local data. Resolving inside this arm instead would
make every statement-level lemma quantify over an entire class, and would recompute the port
name at one of the four sites that have to agree on it letter for letter.

The delay crosses unchanged in the self-send case. A `Delay` wraps a `Nat`, so static and
non-negative travel along structurally, and `after 0` is representable on both sides because a
zero-delay self-send is a microstep and not a causality loop.

The delay is **deliberately dropped in the external case**, which is the one place in this
file where discarding source information is correct rather than suspicious. DTR delays a
statement; LF delays a connection — finding F35. This site's delay is already carried by the
row `routesOf` built for it and lands as that connection's `after`. LF cannot delay a `set` at
all, so a second copy here would have nowhere to go and could only invite the two to disagree.

The `none` arm is a defensive refusal rather than a language limitation, and its text says so
in as many words. `outputPortEnvOf` walks the very send sites `externalSendsOf` produces, so
an external send whose site is missing from its own class's environment is a defect in this
translator and not something a user wrote. #47 discharges it by induction; until then the arm
is reachable in principle, and its message is written for whoever reaches it.

It names the address by building a `SendSite` and handing it to `renderGeneralSendSite`, the
function the routing refusals already use, rather than by a renderer private to this file.
An earlier draft had the private one, and it rendered the same address as *"message server
`settle` at statement 0"* where routing renders it *"message server `settle`, statement at
index 0 counting from zero"*. Both are accurate; a reader comparing two diagnostics about one
send would have had to work out that they were about one send.
-/
def compileGeneralStmt
    (env : GeneralOutputPortEnv)
    (bodyKey : GeneralBodyKey)
    (index : Nat) :
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

  | .send (.knownRebec rebec) message arguments _ =>
      match
          generalEntryAtSite?
            env
            {
              body :=
                bodyKey

              index :=
                index
            } with

      | some entry =>
          .ok
            (.setPort
              entry.outputPort
              (arguments.map
                compileGeneralExpr))

      | none =>
          .error
            ("no output port was resolved for the send `" ++
              rebec.value ++
              "`.`" ++
              message.value ++
              "` in " ++
              renderGeneralSendSite
                {
                  body :=
                    bodyKey

                  index :=
                    index
                } ++
              "; every external send site is resolved by outputPortEnvOf, " ++
              "so this is a defect in the translator and not in the model")

/--
Translate a statement sequence, in order, stopping at the first refusal.

Explicit top-level recursion rather than `mapM`, matching the house pattern in
`Relico/Translation/GlobalMultiStorePayloadBasic.lean`. Two reasons, and neither is taste.
The `nil` and `cons` equations then hold by `rfl`, so the lemmas below are `rfl` proofs
rather than unfoldings of a monadic combinator; and order preservation is provable by an
induction that walks the same shape this walks, which is what §9.2's later stages need.

The index sits in the *matched* position, because it varies in the recursive call and a
parameter written before the colon may not. That is the same shape — and the same reason —
as `externalSendsFromIndex`, which is the traversal this one has to stay in step with: both
advance the index once per statement regardless of what the statement is, so a send's position
here and its position there are the same number. If one of them ever skips, ports are assigned
to the wrong sends and every downstream check still passes, so the alignment is worth stating
even though no theorem in this commit needs it.

First refusal wins, and the diagnostic that survives is the earliest one in source order.
That is a deliberate property of a translator whose refusals name a future stage: the
message a user sees is about the first construct they wrote that this stage cannot carry.
-/
def compileGeneralBody
    (env : GeneralOutputPortEnv)
    (bodyKey : GeneralBodyKey) :
    Nat →
    DTR.GeneralBody →
    Except String LF.GeneralBody

  | _, [] =>
      .ok []

  | index, statement :: remaining =>
      match
          compileGeneralStmt
            env
            bodyKey
            index
            statement with

      | .error message =>
          .error message

      | .ok compiledStatement =>
          match
              compileGeneralBody
                env
                bodyKey
                (index + 1)
                remaining with

          | .error message =>
              .error message

          | .ok compiledRemaining =>
              .ok
                (compiledStatement ::
                  compiledRemaining)

@[simp]
theorem compileGeneralBody_nil
    (env : GeneralOutputPortEnv)
    (bodyKey : GeneralBodyKey)
    (index : Nat) :
    compileGeneralBody
        env
        bodyKey
        index
        [] =
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

Stage E adds three explicit arguments to each and changes nothing else about them. In
particular the tail hypothesis is at `index + 1`, so the arithmetic that threads addresses
through a body appears in these three statements and nowhere else in the file.
-/

theorem compileGeneralBody_cons_ok
    {env : GeneralOutputPortEnv}
    {bodyKey : GeneralBodyKey}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiledStatement : LF.GeneralStmt}
    {compiledRemaining : LF.GeneralBody}
    (hStatement :
      compileGeneralStmt
          env
          bodyKey
          index
          statement =
        .ok compiledStatement)
    (hRemaining :
      compileGeneralBody
          env
          bodyKey
          (index + 1)
          remaining =
        .ok compiledRemaining) :
    compileGeneralBody
        env
        bodyKey
        index
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
    {env : GeneralOutputPortEnv}
    {bodyKey : GeneralBodyKey}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {message : String}
    (hStatement :
      compileGeneralStmt
          env
          bodyKey
          index
          statement =
        .error message) :
    compileGeneralBody
        env
        bodyKey
        index
        (statement :: remaining) =
      .error message := by
  simp [
    compileGeneralBody,
    hStatement
  ]

theorem compileGeneralBody_cons_error_tail
    {env : GeneralOutputPortEnv}
    {bodyKey : GeneralBodyKey}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiledStatement : LF.GeneralStmt}
    {message : String}
    (hStatement :
      compileGeneralStmt
          env
          bodyKey
          index
          statement =
        .ok compiledStatement)
    (hRemaining :
      compileGeneralBody
          env
          bodyKey
          (index + 1)
          remaining =
        .error message) :
    compileGeneralBody
        env
        bodyKey
        index
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

Stage E turns one reaction per message server into a **group**: the action reaction, kept
unconditionally, followed by one port reaction per route that lands on this class for this
message server, in route order (§7.3). Three consequences are worth stating here rather than
leaving them to be inferred from three separate definitions.

The compiled body is shared by every reaction in the group, and shared *literally* — one call
to `compileGeneralBody`, one `LF.GeneralBody`, handed to each assembler. A message server
reached by a self-send and by two external senders therefore has three reactions that cannot
drift apart, and the refusal a bad body would produce is emitted once rather than three times.

The group is contiguous. `compileGeneralMessageServerReactions` appends whole groups, so the
reaction list of a class is its message servers in declaration order with each server's own
arrivals kept together. Stage F has to argue about same-tag ordering, and that argument stays
compositional only if the unit it argues about is a group; interleaving groups would make the
ordering claim quantify over the whole class at once.

The action reaction is present even for a message server nothing self-sends. Its trigger is a
logical action that is declared regardless, `lfc` accepts a reaction on an action nothing ever
schedules, and the alternative — emitting it only when some body schedules it — is a
whole-model analysis in exchange for a few unused lines of C++.
-/

/--
Assemble the reaction that handles one message server's arrivals *on its logical action*.

The trigger is the logical action derived from the same message name, so the two halves of
§III-E's self-send rule — `schedule` in a body, `reaction(m_action)` in the header — are
generated from one source name by one function each, and `actionNameFor_injective` is what
stops two message servers from sharing an action.

Arrivals from *outside* the reactor do not come through this reaction. They come through a
port, and each one gets its own reaction below, with the same parameters and the same body.
Two delivery mechanisms with one behaviour is what §7.3's grouping is for.

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
Assemble the reaction that handles one message server's arrivals on one incoming port.

Triggered by the input port the route lands on, and named after that port (§7.3). The
parameters and the body are the action reaction's, verbatim: a message server does one thing,
and which mechanism delivered the message is not something its body can observe.

`priority := none`, for the same reason as on the action reaction and with a sharper
consequence. These are exactly the reactions §III-D's fan-in ordering is about — two senders
reaching one receiver's message server produce two of them — and which runs first at one tag is
decided by the order `assembleGeneralPortReactions` emits them in, because reaction declaration
order is the target's only ordering hook. Stage F has to prove that order realizes something.
This stage has only to make it deterministic, and to make it visible in one place.
-/
def assembleGeneralPortReaction
    (server : DTR.GeneralMessageServer)
    (route : GeneralRoute)
    (compiledBody : LF.GeneralBody) :
    LF.GeneralReaction where

  name :=
    portReactionNameFor
      (generalInputPortOfRoute route)

  trigger :=
    .inputPort
      (generalInputPortOfRoute route)

  parameters :=
    server.parameters.map
      (fun parameter =>
        parameter.name)

  body :=
    compiledBody

  priority :=
    none

@[simp]
theorem assembleGeneralPortReaction_name
    (server : DTR.GeneralMessageServer)
    (route : GeneralRoute)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralPortReaction
        server
        route
        compiledBody).name =
      portReactionNameFor
        (generalInputPortOfRoute route) := by
  rfl

@[simp]
theorem assembleGeneralPortReaction_trigger
    (server : DTR.GeneralMessageServer)
    (route : GeneralRoute)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralPortReaction
        server
        route
        compiledBody).trigger =
      .inputPort
        (generalInputPortOfRoute route) := by
  rfl

@[simp]
theorem assembleGeneralPortReaction_parameters
    (server : DTR.GeneralMessageServer)
    (route : GeneralRoute)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralPortReaction
        server
        route
        compiledBody).parameters =
      server.parameters.map
        (fun parameter =>
          parameter.name) := by
  rfl

@[simp]
theorem assembleGeneralPortReaction_body
    (server : DTR.GeneralMessageServer)
    (route : GeneralRoute)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralPortReaction
        server
        route
        compiledBody).body =
      compiledBody := by
  rfl

@[simp]
theorem assembleGeneralPortReaction_priority
    (server : DTR.GeneralMessageServer)
    (route : GeneralRoute)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralPortReaction
        server
        route
        compiledBody).priority =
      none := by
  rfl

/--
Assemble one message server's port reactions, in route order.

A `map` over `generalRoutesIntoMessageServer` rather than a recursion with the filter inlined,
and the reason is the same one that made the filter a named function: the reactions and the
input ports of a class must range over the same routes, and writing both as projections of one
filter makes that agreement structural instead of a coincidence between two conditions. It
also means the theorem below is an ordinary statement about `List.map` rather than an induction
over a bespoke recursion.

Route order is the order `routesOf` walked the main block in. Nothing sorts, and in particular
nothing sorts by the sender's actor priority, which is what stage G would need — recorded here
because a reader who knows §III-D will expect a sort and its absence should be a decision they
can find rather than an omission they discover.
-/
def assembleGeneralPortReactions
    (className : ClassName)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody)
    (routes : List GeneralRoute) :
    List LF.GeneralReaction :=
  (generalRoutesIntoMessageServer
    className
    server.name
    routes).map
      (fun route =>
        assembleGeneralPortReaction
          server
          route
          compiledBody)

private theorem mapNames_map_assembleGeneralPortReaction
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    ∀ (routes : List GeneralRoute),
      (routes.map
          (fun candidate =>
            assembleGeneralPortReaction
              server
              candidate
              compiledBody)).map
          (fun reaction =>
            reaction.name) =
        routes.map
          (fun candidate =>
            portReactionNameFor
              (generalInputPortOfRoute candidate)) := by

  intro routes
  induction routes with

  | nil =>
      rfl

  | cons route remaining inductionHypothesis =>
      change
        portReactionNameFor
              (generalInputPortOfRoute route) ::
            (remaining.map
                (fun candidate =>
                  assembleGeneralPortReaction
                    server
                    candidate
                    compiledBody)).map
                (fun reaction =>
                  reaction.name) =
          portReactionNameFor
              (generalInputPortOfRoute route) ::
            remaining.map
              (fun candidate =>
                portReactionNameFor
                  (generalInputPortOfRoute candidate))

      exact
        congrArg
          (List.cons
            (portReactionNameFor
              (generalInputPortOfRoute route)))
          inductionHypothesis

/--
One message server's port reactions are named after the ports that trigger them, in route
order.

This is one of the two theorems that replace stage D's `compileGeneralMessageServerReactions_names`,
which port reactions falsified. It is stated at the level of a single message server's group on
purpose: the class-level statement would need a flattening combinator over groups, and
`List.flatMap` is a core name this development has twice been burned by trusting. The
concatenation of groups is covered by `compileGeneralMessageServerReactions_cons_ok`, which
needs no combinator at all, so the two together say what the deleted theorem said and each half
is provable without one.
-/
theorem assembleGeneralPortReactions_names
    (className : ClassName)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody)
    (routes : List GeneralRoute) :
    (assembleGeneralPortReactions
        className
        server
        compiledBody
        routes).map
        (fun reaction =>
          reaction.name) =
      (generalRoutesIntoMessageServer
        className
        server.name
        routes).map
        (fun candidate =>
          portReactionNameFor
            (generalInputPortOfRoute candidate)) :=
  mapNames_map_assembleGeneralPortReaction
    server
    compiledBody
    (generalRoutesIntoMessageServer
      className
      server.name
      routes)

/--
Translate one message server into its group of reactions.

The action reaction first, then one port reaction per incoming route, which is §7.3's order and
also the only order that keeps a self-send's delivery ahead of an external one at the same tag
for a message server that has both. That last point is an observation and not a claim: nothing
in this stage proves anything about it, and stage F is where it becomes a statement.

The body is compiled **once**, at the address `(.messageServer server.name, 0)` — the message
server's own body key, starting from statement zero — and shared by every reaction in the
group. Compiling it per reaction would be the same result by determinism and a different
program by accident the first time a body compilation grew a dependency on its reaction.

No new failure: the only thing that can go wrong is a refusal inside the body.
-/
def compileGeneralMessageServerReactionGroup
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (className : ClassName)
    (server : DTR.GeneralMessageServer) :
    Except String (List LF.GeneralReaction) :=
  match
      compileGeneralBody
        env
        (.messageServer server.name)
        0
        server.body with

  | .error message =>
      .error message

  | .ok compiledBody =>
      .ok
        (assembleGeneralMessageReaction
            server
            compiledBody ::
          assembleGeneralPortReactions
            className
            server
            compiledBody
            routes)

theorem compileGeneralMessageServerReactionGroup_ok
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {compiledBody : LF.GeneralBody}
    (hBody :
      compileGeneralBody
          env
          (.messageServer server.name)
          0
          server.body =
        .ok compiledBody) :
    compileGeneralMessageServerReactionGroup
        env
        routes
        className
        server =
      .ok
        (assembleGeneralMessageReaction
            server
            compiledBody ::
          assembleGeneralPortReactions
            className
            server
            compiledBody
            routes) := by
  simp [
    compileGeneralMessageServerReactionGroup,
    hBody
  ]

theorem compileGeneralMessageServerReactionGroup_error
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {message : String}
    (hBody :
      compileGeneralBody
          env
          (.messageServer server.name)
          0
          server.body =
        .error message) :
    compileGeneralMessageServerReactionGroup
        env
        routes
        className
        server =
      .error message := by
  simp [
    compileGeneralMessageServerReactionGroup,
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

The body is compiled at the address `(.constructor, 0)`, which is the same body key
`externalSendsOfClass` walks first, so a constructor's sends own the same ports here as they
were given there.

A constructor *may* contain an external send, and stage E makes that translate rather than
refuse: it becomes a `setPort` inside `reaction(startup)`, and the printer derives the effect
clause from the body, so the emitted reaction is `reaction(startup) -> port`. Whether `lfc`
accepts setting an output port from a startup reaction is **not measured** by any committed
fixture. It is ordinary LF and expected to hold, but the distinction between expected and
measured is one this development keeps, so it is written here at the site rather than assumed
silently — and #45 is the place to close it, since a fixture that sends from a constructor costs
nothing beyond deciding to write one.
-/
def compileGeneralConstructor
    (env : GeneralOutputPortEnv)
    (classConstructor : DTR.GeneralConstructor) :
    Except String LF.GeneralReaction :=
  match
      compileGeneralBody
        env
        .constructor
        0
        classConstructor.body with

  | .error message =>
      .error message

  | .ok compiledBody =>
      .ok
        (assembleGeneralStartupReaction
          classConstructor
          compiledBody)

theorem compileGeneralConstructor_ok
    {env : GeneralOutputPortEnv}
    {classConstructor : DTR.GeneralConstructor}
    {compiledBody : LF.GeneralBody}
    (hBody :
      compileGeneralBody
          env
          .constructor
          0
          classConstructor.body =
        .ok compiledBody) :
    compileGeneralConstructor
        env
        classConstructor =
      .ok
        (assembleGeneralStartupReaction
          classConstructor
          compiledBody) := by
  simp [
    compileGeneralConstructor,
    hBody
  ]

theorem compileGeneralConstructor_error
    {env : GeneralOutputPortEnv}
    {classConstructor : DTR.GeneralConstructor}
    {message : String}
    (hBody :
      compileGeneralBody
          env
          .constructor
          0
          classConstructor.body =
        .error message) :
    compileGeneralConstructor
        env
        classConstructor =
      .error message := by
  simp [
    compileGeneralConstructor,
    hBody
  ]

/--
Translate every message server into its group of reactions, in source order.

Explicit recursion and no sort. `Relico/Translation/MultiStoreBasic.lean` compiles this
list in `priorityOrderedMessageServers` order; this family deliberately does not, because
declaration order is observable in the target and the sort that realizes priority is stage
G's, together with the theorem that says what it achieves.

Groups are **appended**, not consed, which is the one structural change stage E makes to this
function. A class's reaction list is therefore its message servers in declaration order with
each server's arrivals contiguous behind it, and `compileGeneralMessageServerReactions_cons_ok`
says exactly that in one `++`.
-/
def compileGeneralMessageServerReactions
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (className : ClassName) :
    List DTR.GeneralMessageServer →
    Except String (List LF.GeneralReaction)

  | [] =>
      .ok []

  | server :: remaining =>
      match
          compileGeneralMessageServerReactionGroup
            env
            routes
            className
            server with

      | .error message =>
          .error message

      | .ok group =>
          match
              compileGeneralMessageServerReactions
                env
                routes
                className
                remaining with

          | .error message =>
              .error message

          | .ok compiledRemaining =>
              .ok
                (group ++
                  compiledRemaining)

@[simp]
theorem compileGeneralMessageServerReactions_nil
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (className : ClassName) :
    compileGeneralMessageServerReactions
        env
        routes
        className
        [] =
      .ok [] := by
  rfl

theorem compileGeneralMessageServerReactions_cons_ok
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    {compiledRemaining : List LF.GeneralReaction}
    (hServer :
      compileGeneralMessageServerReactionGroup
          env
          routes
          className
          server =
        .ok group)
    (hRemaining :
      compileGeneralMessageServerReactions
          env
          routes
          className
          remaining =
        .ok compiledRemaining) :
    compileGeneralMessageServerReactions
        env
        routes
        className
        (server :: remaining) =
      .ok
        (group ++
          compiledRemaining) := by
  simp [
    compileGeneralMessageServerReactions,
    hServer,
    hRemaining
  ]

theorem compileGeneralMessageServerReactions_cons_error_head
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {message : String}
    (hServer :
      compileGeneralMessageServerReactionGroup
          env
          routes
          className
          server =
        .error message) :
    compileGeneralMessageServerReactions
        env
        routes
        className
        (server :: remaining) =
      .error message := by
  simp [
    compileGeneralMessageServerReactions,
    hServer
  ]

theorem compileGeneralMessageServerReactions_cons_error_tail
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    {message : String}
    (hServer :
      compileGeneralMessageServerReactionGroup
          env
          routes
          className
          server =
        .ok group)
    (hRemaining :
      compileGeneralMessageServerReactions
          env
          routes
          className
          remaining =
        .error message) :
    compileGeneralMessageServerReactions
        env
        routes
        className
        (server :: remaining) =
      .error message := by
  simp [
    compileGeneralMessageServerReactions,
    hServer,
    hRemaining
  ]

/-!
## Reactors and the program

The same two-step shape, and the place where stage D's boundary used to be written down: two
empty port lists on every reactor and one empty connection list on the program. All three are
now routing projections, and the three theorems that stated the empty forms are restated in
§9.1's section below rather than deleted, so the arithmetic still says what the shape of the
target is — it just no longer says zero.

Where the two port lists come from is asymmetric, and the asymmetry is forced rather than
chosen. Output ports come from the sending class's **environment**, so a class with no
instances still declares the ports its bodies set, which `stmtWellFormed` requires of every
`setPort`. Input ports come from the **model's** routes, because `lfc 0.11.0` rejects
many-to-one connections and so each sending instance needs its own port on the receiver — a
per-class question cannot answer that. The price is an input port that nothing connects to
whenever a class has more instances than senders, and that price is measured payable: an
unconnected input port compiles and runs.
-/

/--
Assemble one reactor from a class, its routing, and its two already-compiled reaction groups.

The constructor's typed parameters become the **reactor's** parameters, which is Fig. 5's
`Reactor ::= reactor R (ParamList?)` production that stage C dropped — finding F22. Without
it, two instances of one class constructed with different arguments are indistinguishable
in the generated LF, so the paper's own class-to-reactor mapping loses information the
source had.

`inputPorts` and `outputPorts` are the two routing projections, and this is the single place
they enter the translated program. `knownRebecs` is still read by nothing *here*: a known rebec
becomes a port only when something sends on it, and the deciding is done in
`Relico/Translation/GeneralRouting.lean` by walking send sites rather than declarations. A
class that declares a known rebec and never sends on it therefore still yields a reactor with
no ports, which is what keeps the committed fixtures with unused known rebecs passing.

One logical action per message server, in source order. The reaction list is no longer one per
message server — see §7.3 and the group above — so the two lists no longer have equal length,
and `compileGeneralReactiveClass_reactionNames` was retired rather than adjusted for exactly
that reason. `assembleGeneralReactor_logicalActions` still pins the action list to source
order, which is the fixed starting point stage G's permutation needs.
-/
def assembleGeneralReactor
    (reactiveClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    LF.GeneralReactor where

  name :=
    reactorNameFor reactiveClass.name

  parameters :=
    reactiveClass.constructor.parameters.map
      compileGeneralTypedParameter

  inputPorts :=
    generalInputPortsOf
      reactiveClass.name
      routes

  outputPorts :=
    generalOutputPortsOf
      env

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
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        env
        routes
        compiledStartupReaction
        compiledMessageReactions).name =
      reactorNameFor reactiveClass.name := by
  rfl

@[simp]
theorem assembleGeneralReactor_parameters
    (reactiveClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        env
        routes
        compiledStartupReaction
        compiledMessageReactions).parameters =
      reactiveClass.constructor.parameters.map
        compileGeneralTypedParameter := by
  rfl

@[simp]
theorem assembleGeneralReactor_inputPorts
    (reactiveClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        env
        routes
        compiledStartupReaction
        compiledMessageReactions).inputPorts =
      generalInputPortsOf
        reactiveClass.name
        routes := by
  rfl

@[simp]
theorem assembleGeneralReactor_outputPorts
    (reactiveClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        env
        routes
        compiledStartupReaction
        compiledMessageReactions).outputPorts =
      generalOutputPortsOf
        env := by
  rfl

@[simp]
theorem assembleGeneralReactor_stateVariables
    (reactiveClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        env
        routes
        compiledStartupReaction
        compiledMessageReactions).stateVariables =
      reactiveClass.stateVariables.map
        compileGeneralStateVariableDecl := by
  rfl

@[simp]
theorem assembleGeneralReactor_logicalActions
    (reactiveClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        env
        routes
        compiledStartupReaction
        compiledMessageReactions).logicalActions =
      reactiveClass.messageServers.map
        compileGeneralMessageServerAction := by
  rfl

@[simp]
theorem assembleGeneralReactor_startupReaction
    (reactiveClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        env
        routes
        compiledStartupReaction
        compiledMessageReactions).startupReaction =
      compiledStartupReaction := by
  rfl

@[simp]
theorem assembleGeneralReactor_messageReactions
    (reactiveClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (compiledStartupReaction : LF.GeneralReaction)
    (compiledMessageReactions : List LF.GeneralReaction) :
    (assembleGeneralReactor
        reactiveClass
        env
        routes
        compiledStartupReaction
        compiledMessageReactions).messageReactions =
      compiledMessageReactions := by
  rfl

/--
Translate one reactive class into one reactor.

Three failure sources now, in this order: resolving the class's output ports, the constructor,
then the message servers. The environment is resolved **first and once**, which is §7.1's
*"resolve once per class, then compile against the resolution"*, and the order of the other two
is stage D's — a class whose constructor and whose first message server both fail reports the
constructor's diagnostic, because source order is what a reader can act on.

`classes` is the whole class list rather than this class, and it is not this function's business
to know why: `outputPortEnvOf` needs the *receiving* class's message servers to type a payload,
so the argument threads through. `routes` is the whole model's, for the reason
`assembleGeneralReactor`'s docstring gives.
-/
def compileGeneralReactiveClass
    (classes : List DTR.GeneralReactiveClass)
    (routes : List GeneralRoute)
    (reactiveClass : DTR.GeneralReactiveClass) :
    Except String LF.GeneralReactor :=
  match
      outputPortEnvOf
        classes
        reactiveClass with

  | .error message =>
      .error message

  | .ok env =>
      match
          compileGeneralConstructor
            env
            reactiveClass.constructor with

      | .error message =>
          .error message

      | .ok compiledStartupReaction =>
          match
              compileGeneralMessageServerReactions
                env
                routes
                reactiveClass.name
                reactiveClass.messageServers with

          | .error message =>
              .error message

          | .ok compiledMessageReactions =>
              .ok
                (assembleGeneralReactor
                  reactiveClass
                  env
                  routes
                  compiledStartupReaction
                  compiledMessageReactions)

theorem compileGeneralReactiveClass_ok
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    {compiledStartupReaction : LF.GeneralReaction}
    {compiledMessageReactions : List LF.GeneralReaction}
    (hEnv :
      outputPortEnvOf
          classes
          reactiveClass =
        .ok env)
    (hConstructor :
      compileGeneralConstructor
          env
          reactiveClass.constructor =
        .ok compiledStartupReaction)
    (hMessageServers :
      compileGeneralMessageServerReactions
          env
          routes
          reactiveClass.name
          reactiveClass.messageServers =
        .ok compiledMessageReactions) :
    compileGeneralReactiveClass
        classes
        routes
        reactiveClass =
      .ok
        (assembleGeneralReactor
          reactiveClass
          env
          routes
          compiledStartupReaction
          compiledMessageReactions) := by
  simp [
    compileGeneralReactiveClass,
    hEnv,
    hConstructor,
    hMessageServers
  ]

/--
The failure stage E adds to this function, and the only one that is not about a body.

Stated separately from the other two rather than folded into a single error lemma, because the
failures have different causes and §10's inversion lemma has to be able to say which one it
ruled out. `outputPortEnvOf` has **four** such causes, none of them raised in its own body: all
four come from `generalOutputPortEntryFor`, the callee it maps over every numbered send. Measured
by reading the branch that *decides* each one, at `Relico/Translation/GeneralRouting.lean:686`,
`:699`, `:712` and `:730`. Those are the discriminating `match`es, not the `.error` expressions,
which sit three lines below the first three; the fourth is a call, and its refusal text is built
at `:507` in `generalPortPayloadFor`. In order: a send names a known rebec the sending class never
declared; a declared known rebec's class is not a class the model declares; the receiving class
has no message server of the sent name; or the receiving message server's parameters admit no
port payload.

**An earlier version of this docstring said three, omitted the second, and credited all of them
to "the two new `lean-reject` fixtures".** That last part cannot be true of any document. A
`lean-reject` fixture is one the *frontend refuses*, so it never reaches a translation function
at all; what those two fixtures establish is that `sendTargetsDeclared` and
`sendsResolveToMessageServers` reject such a document upstream, which is the reason the first
and third causes here are unreachable from frontend output — not evidence that these branches
were taken. The distinction is the whole point of the paragraph in §8 that calls these branches
defensive. Recorded as finding F47 in `docs/STAGE_E_FINDINGS.md`, together with the measurement
that of the eight refusal causes reachable through `routesOf`, exactly two had their text
asserted anywhere when the finding was written. All eight are asserted now, in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean` and only there, because a hand-built model
is the only way a translation refusal can be reached. The four causes this lemma covers are
`KNOWN_REBEC_UNDECLARED_REFUSED`, `KNOWN_REBEC_CLASS_UNDECLARED_REFUSED`,
`UNDECLARED_MESSAGE_SERVER_SEND_REFUSED` and `PARAMETERLESS_EXTERNAL_SEND_REFUSED`, in the order
listed above; those are literal `PASS_` labels, so this sentence is falsifiable by `grep`, which
is the property the sentence it replaced did not have.
-/
theorem compileGeneralReactiveClass_error_env
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {message : String}
    (hEnv :
      outputPortEnvOf
          classes
          reactiveClass =
        .error message) :
    compileGeneralReactiveClass
        classes
        routes
        reactiveClass =
      .error message := by
  simp [
    compileGeneralReactiveClass,
    hEnv
  ]

theorem compileGeneralReactiveClass_error_constructor
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    {message : String}
    (hEnv :
      outputPortEnvOf
          classes
          reactiveClass =
        .ok env)
    (hConstructor :
      compileGeneralConstructor
          env
          reactiveClass.constructor =
        .error message) :
    compileGeneralReactiveClass
        classes
        routes
        reactiveClass =
      .error message := by
  simp [
    compileGeneralReactiveClass,
    hEnv,
    hConstructor
  ]

theorem compileGeneralReactiveClass_error_messageServers
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    {compiledStartupReaction : LF.GeneralReaction}
    {message : String}
    (hEnv :
      outputPortEnvOf
          classes
          reactiveClass =
        .ok env)
    (hConstructor :
      compileGeneralConstructor
          env
          reactiveClass.constructor =
        .ok compiledStartupReaction)
    (hMessageServers :
      compileGeneralMessageServerReactions
          env
          routes
          reactiveClass.name
          reactiveClass.messageServers =
        .error message) :
    compileGeneralReactiveClass
        classes
        routes
        reactiveClass =
      .error message := by
  simp [
    compileGeneralReactiveClass,
    hEnv,
    hConstructor,
    hMessageServers
  ]

/--
Translate every class into its reactor, in source order.

`allClasses` is threaded unchanged past every recursive call and is **not** the list being
walked. Two lists of the same type in one signature is a readability cost paid deliberately:
`outputPortEnvOf` types a payload from the *receiving* class's message server, so compiling
the last class in the list can need the first one, and a fold that consumed the list would
have nothing left to look the receiver up in.

`routes` is threaded for the same reason and is a model-level object throughout — see
`assembleGeneralReactor`'s docstring for why a per-class routing table cannot exist.
-/
def compileGeneralReactiveClasses
    (allClasses : List DTR.GeneralReactiveClass)
    (routes : List GeneralRoute) :
    List DTR.GeneralReactiveClass →
    Except String (List LF.GeneralReactor)

  | [] =>
      .ok []

  | reactiveClass :: remaining =>
      match
          compileGeneralReactiveClass
            allClasses
            routes
            reactiveClass with

      | .error message =>
          .error message

      | .ok reactor =>
          match
              compileGeneralReactiveClasses
                allClasses
                routes
                remaining with

          | .error message =>
              .error message

          | .ok compiledRemaining =>
              .ok
                (reactor ::
                  compiledRemaining)

@[simp]
theorem compileGeneralReactiveClasses_nil
    (allClasses : List DTR.GeneralReactiveClass)
    (routes : List GeneralRoute) :
    compileGeneralReactiveClasses
        allClasses
        routes
        [] =
      .ok [] := by
  rfl

theorem compileGeneralReactiveClasses_cons_ok
    {allClasses : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {remaining : List DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    {compiledRemaining : List LF.GeneralReactor}
    (hClass :
      compileGeneralReactiveClass
          allClasses
          routes
          reactiveClass =
        .ok reactor)
    (hRemaining :
      compileGeneralReactiveClasses
          allClasses
          routes
          remaining =
        .ok compiledRemaining) :
    compileGeneralReactiveClasses
        allClasses
        routes
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
    {allClasses : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {remaining : List DTR.GeneralReactiveClass}
    {message : String}
    (hClass :
      compileGeneralReactiveClass
          allClasses
          routes
          reactiveClass =
        .error message) :
    compileGeneralReactiveClasses
        allClasses
        routes
        (reactiveClass :: remaining) =
      .error message := by
  simp [
    compileGeneralReactiveClasses,
    hClass
  ]

theorem compileGeneralReactiveClasses_cons_error_tail
    {allClasses : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {remaining : List DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    {message : String}
    (hClass :
      compileGeneralReactiveClass
          allClasses
          routes
          reactiveClass =
        .ok reactor)
    (hRemaining :
      compileGeneralReactiveClasses
          allClasses
          routes
          remaining =
        .error message) :
    compileGeneralReactiveClasses
        allClasses
        routes
        (reactiveClass :: remaining) =
      .error message := by
  simp [
    compileGeneralReactiveClasses,
    hClass,
    hRemaining
  ]

/--
Assemble the program from a model, its routing, and its already-compiled reactors.

`connections := generalConnectionsOf routes` is the third routing projection and the last
piece of stage D's boundary to go. One connection per route, in the order `routesOf` produced
them, which is main-block instance-declaration order — so the generated `main reactor` reads
in the order the source's instances were declared, and `compileGeneralModel_connections` can
still state the connection list exactly rather than up to permutation.

The instances remain total: nothing about an actor instance can fail even now, because a
binding that names an instance of the wrong class is caught in `routesOf` and never reaches
here. So the only `Except` in reach of this function is still the one its callers bring.
-/
def assembleGeneralProgram
    (model : DTR.GeneralModel)
    (routes : List GeneralRoute)
    (compiledReactors : List LF.GeneralReactor) :
    LF.GeneralProgram where

  reactors :=
    compiledReactors

  instances :=
    model.instances.map
      compileGeneralActorInstance

  connections :=
    generalConnectionsOf
      routes

@[simp]
theorem assembleGeneralProgram_reactors
    (model : DTR.GeneralModel)
    (routes : List GeneralRoute)
    (compiledReactors : List LF.GeneralReactor) :
    (assembleGeneralProgram
        model
        routes
        compiledReactors).reactors =
      compiledReactors := by
  rfl

@[simp]
theorem assembleGeneralProgram_instances
    (model : DTR.GeneralModel)
    (routes : List GeneralRoute)
    (compiledReactors : List LF.GeneralReactor) :
    (assembleGeneralProgram
        model
        routes
        compiledReactors).instances =
      model.instances.map
        compileGeneralActorInstance := by
  rfl

@[simp]
theorem assembleGeneralProgram_connections
    (model : DTR.GeneralModel)
    (routes : List GeneralRoute)
    (compiledReactors : List LF.GeneralReactor) :
    (assembleGeneralProgram
        model
        routes
        compiledReactors).connections =
      generalConnectionsOf
        routes := by
  rfl

/-!
## The output guard

F32's third road, and the reason this section exists rather than a hypothesis on the
preservation theorem. `docs/STAGE_E_DESIGN.md` §9: the translation decides
`LF.GeneralProgram.wellFormed` **on its own output** and refuses when it is false. That makes
preservation true with no extra hypothesis and — this is the part that decided it — with no
DTR-side import, which matters because this module imports DTR *syntax* only and so cannot
mention `DTR.GeneralModel.wellFormed` at all.

The guard is the only place in this file where a refusal is not about a *source* construct.
Its message therefore has to name a property of the generated program, and there is a real
design tension in that: the nine clauses live in `Relico/LF/GeneralWellFormed.lean` and none
of them carries prose fit for a diagnostic. The resolution below is a **mirror** — a list
pairing each clause with a sentence — and the mirror is used for the refusal *text only*. The
decision itself is made on `LF.GeneralProgram.wellFormed`, never on the mirror.

That split is deliberate and was the second design considered, not the first. A guard that
decided on an `Option String` diagnostic built from the mirror would need
`diagnostic program = none ↔ program.wellFormed = true` as its anti-drift tripwire, and that
biconditional unfolds into a five-hundred-and-twelve-leaf case split over nine independent
booleans, on a module that has never elaborated. One unclosed leaf would surface as a gate
failure with no way to tell a real defect from a proof-engineering gap. Deciding on the real
predicate makes acceptance-implies-well-formedness a **two-case** proof, and pays for it with
a mirror that can drift. Drift is then a *visible runtime symptom* rather than a soundness
hole: the fallback string below names itself, so a program the guard rejects while every
mirrored clause holds prints a sentence that says the mirror is out of date, in the gate log,
where a reader is already looking.
-/

/--
One sentence per conjunct of `LF.GeneralProgram.wellFormed`, in the same order.

The order is not load-bearing for correctness — the refusal lists whatever is false — but it
is kept identical to `wellFormed`'s so that a reader comparing the two files can do it by
sight. Nine entries; if `Relico/LF/GeneralWellFormed.lean` gains a tenth conjunct, this list
does not, and `generalProgramExplanation`'s fallback is what says so.

Reaction names are **absent on purpose**, and the absence is the finding, not an omission.
`Relico/LF/GeneralWellFormed.lean:37` records that reaction names need not be unique because
LF reactions are anonymous in concrete syntax, and `portReactionNameFor`'s docstring records
that stage E's port reactions can therefore collide with a message reaction's name without
anything being wrong. There is nothing here for the guard to check.
-/
private def generalProgramClauses :
    List (String × (LF.GeneralProgram → Bool)) :=
  [
    (
      "no reactor is declared",
      LF.GeneralProgram.reactorsNonEmpty
    ),
    (
      "no instance is declared",
      LF.GeneralProgram.instancesNonEmpty
    ),
    (
      "some reactor is not well-formed, which for stage E most often means a generated name "
        ++ "collided with another name in the same reactor, or a port was set that the "
        ++ "reactor does not declare",
      LF.GeneralProgram.reactorsWellFormed
    ),
    (
      "two reactors share a name",
      LF.GeneralProgram.reactorNamesUnique
    ),
    (
      "two instances share a name",
      LF.GeneralProgram.instanceNamesUnique
    ),
    (
      "some instance has an empty name or instantiates a reactor that is not declared",
      LF.GeneralProgram.instancesResolve
    ),
    (
      "some instance passes the wrong number of arguments to its reactor",
      LF.GeneralProgram.instanceArgumentsMatch
    ),
    (
      "some connection names an endpoint that is not declared, or joins two ports whose "
        ++ "payloads differ",
      LF.GeneralProgram.connectionsWellFormed
    ),
    (
      "two connections target the same input port of the same instance, which the LF "
        ++ "compiler rejects as a many-to-one connection",
      LF.GeneralProgram.targetEndpointsUnique
    )
  ]

/--
The sentences of the mirrored clauses that are false of this program.

Explicit recursion with the varying list after the colon, which is the whole reason this is a
separate definition rather than a `List.filterMap` inside `generalProgramExplanation`: the
program does not vary and must stay before the colon.

The discriminant is matched rather than tested with `if`, for the reason given at the top of
this file: a `Bool` in a `match` needs no coercion and no `Decidable` instance, so nothing
about this definition depends on how core spells propositional truth this month.
-/
private def generalFailingClauses
    (program : LF.GeneralProgram) :
    List (String × (LF.GeneralProgram → Bool)) →
    List String

  | [] =>
      []

  | (sentence, clause) :: remaining =>
      match clause program with

      | true =>
          generalFailingClauses
            program
            remaining

      | false =>
          sentence ::
            generalFailingClauses
              program
              remaining

/--
Why the guard refused this program.

Total, like every other helper in the total layer, and it does not claim to be complete: the
`[]` case is reachable exactly when the mirror has drifted out of step with
`LF.GeneralProgram.wellFormed`, and it says so in the sentence it returns. Naming the two
definitions that disagree is what turns a mystifying gate failure into a one-line fix.
-/
def generalProgramExplanation
    (program : LF.GeneralProgram) :
    String :=
  match
      generalFailingClauses
        program
        generalProgramClauses with

  | [] =>
      "every clause mirrored in `generalProgramClauses` holds, so that mirror has drifted " ++
        "out of step with `LF.GeneralProgram.wellFormed` and is missing an entry for the " ++
        "clause that failed"

  | sentences =>
      String.intercalate
        "; "
        sentences

/--
Accept the translated program if it is a well-formed LF program, and refuse it otherwise.

The discriminant is `LF.GeneralProgram.wellFormed` itself, so `guardGeneralProgram_wellFormed`
below is a two-case proof and every guarantee this guard offers rests on the same predicate
`Relico/LF/GeneralCppPrinter.lean` and the target gate are written against.

A refusal here is a **translator defect, not a document defect**, in every case the design
anticipates: `Relico/Frontend/GeneralDecoder.lean` has already certified the model, so a
model that reaches this point and is refused says the naming rules collided or a projection
is wrong. That is why the message is phrased as a report about the generated program and not
as advice to whoever wrote the model — and why the generated-name collision refusal of §8
lands here rather than in `outputPortEnvOf`, where it would have to guess at names it has not
finished generating.
-/
def guardGeneralProgram
    (program : LF.GeneralProgram) :
    Except String LF.GeneralProgram :=
  match program.wellFormed with

  | true =>
      .ok program

  | false =>
      .error
        ("the translated LF program is not well-formed: " ++
          generalProgramExplanation program)

/--
The guard accepts a well-formed program unchanged.
-/
theorem guardGeneralProgram_of_wellFormed
    {program : LF.GeneralProgram}
    (hWellFormed :
      program.wellFormed = true) :
    guardGeneralProgram program =
      .ok program := by
  simp [
    guardGeneralProgram,
    hWellFormed
  ]

/--
What the guard returns, it returns unchanged.

Stated separately from the well-formedness half because the two are used in different places:
the inversion lemmas need this one to rewrite `assembleGeneralProgram …` into the accepted
program, and §9.1's boundary theorems need the other.
-/
theorem eq_of_guardGeneralProgram_ok
    {program accepted : LF.GeneralProgram}
    (hGuard :
      guardGeneralProgram program =
        .ok accepted) :
    program = accepted := by
  revert hGuard
  unfold guardGeneralProgram
  cases program.wellFormed <;>
    simp

/--
Anything the guard accepts is a well-formed LF program.

The two-case proof the design bought by deciding on the real predicate rather than on a
mirror. Everything §9.1 says about the *translation's* output — and, through
`compileGeneralModel_targetEndpointsUnique`, everything it says about many-to-one connections
— goes through this theorem.
-/
theorem guardGeneralProgram_wellFormed
    {program accepted : LF.GeneralProgram}
    (hGuard :
      guardGeneralProgram program =
        .ok accepted) :
    program.wellFormed = true := by
  revert hGuard
  unfold guardGeneralProgram
  cases program.wellFormed <;>
    simp

/--
Translate a model into a program.

The entry point of stage E, and three steps now rather than one. The routing table is built
**first**, from the whole model, because both port lists and the connection list are
projections of it and because a binding that cannot be resolved should be reported before any
class is compiled. Then every class is compiled against that table. Then the guard.

Ordering the routing first also fixes which diagnostic a doubly-broken model produces: a
model with an unresolvable binding *and* a class whose constructor cannot be compiled reports
the binding. That is a change from stage D — where no such choice existed — and it is the
right way round, because an unresolved binding usually explains the body failure downstream
of it.
-/
def compileGeneralModel
    (model : DTR.GeneralModel) :
    Except String LF.GeneralProgram :=
  match routesOf model with

  | .error message =>
      .error message

  | .ok routes =>
      match
          compileGeneralReactiveClasses
            model.classes
            routes
            model.classes with

      | .error message =>
          .error message

      | .ok compiledReactors =>
          guardGeneralProgram
            (assembleGeneralProgram
              model
              routes
              compiledReactors)

/--
What `compileGeneralModel` reduces to once routing and every class have succeeded.

Note the shape: the right-hand side is the **guard applied to** the assembled program, not
the assembled program. Stage D's version of this lemma ended in `.ok`, and every consumer of
it that assumed the assembled program *is* the result has to be re-read — which is precisely
what §9.1's boundary theorems do below, each one now going through
`eq_of_guardGeneralProgram_ok` first.
-/
theorem compileGeneralModel_ok
    {model : DTR.GeneralModel}
    {routes : List GeneralRoute}
    {compiledReactors : List LF.GeneralReactor}
    (hRoutes :
      routesOf model =
        .ok routes)
    (hClasses :
      compileGeneralReactiveClasses
          model.classes
          routes
          model.classes =
        .ok compiledReactors) :
    compileGeneralModel model =
      guardGeneralProgram
        (assembleGeneralProgram
          model
          routes
          compiledReactors) := by
  simp [
    compileGeneralModel,
    hRoutes,
    hClasses
  ]

/--
Routing failed, so the model does not translate.

The failure stage E adds at model level. `routesOf` composes the per-class port environment with
a per-instance row builder, so it inherits all four causes listed on
`compileGeneralReactiveClass_error_env` above and adds four of its own — three from
`generalRouteFor`, at `Relico/Translation/GeneralRouting.lean:931`, `:944` and `:957`, and one
from `routesOfInstances`, at `:1058`. As above these are the deciding branches rather than the
`.error` expressions; `:957`'s is the furthest from its refusal, whose `else` is at `:991`. In
order: an instance binds no known rebec of a name its class declares and sends to; a binding names
an instance the model does not instantiate; a binding names an instance whose class is not the
declared known rebec's class; or an instance instantiates a class the model does not declare.
Eight causes, one `Except String`, which is why the message text is the only thing that
distinguishes them and why §10's inversion has to go through the text rather than a constructor.
All eight texts are asserted, which was not true when finding F47 measured them: two were.
The four this lemma adds are `KNOWN_REBEC_UNBOUND_REFUSED`,
`BINDING_TARGET_NOT_INSTANTIATED_REFUSED`, `BINDING_TARGET_CLASS_MISMATCH_REFUSED` and
`INSTANCE_CLASS_UNDECLARED_REFUSED`, in the order listed above, in
`routedRefusalAssertions` in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`.

**An earlier version of this docstring said "the three the two new `lean-reject` documents
exercise", named the payload cause among the three, and omitted both the binding-lookup cause and
the undeclared-instantiated-class one.** The claim fails twice over, in two different ways worth
keeping apart. Two of the three it named are bindings-and-topology failures that
`bindingsMatchDeclarations` already refuses upstream, so no document reaches them because the
frontend stops it first. The third, the payload cause, is not a malformedness at all — it is this
translation's own limit on an arity-zero send — so a model carrying it is well formed, the
frontend *accepts* it, and the refusal happens here rather than there. Either way a `lean-reject`
document is the wrong instrument: the first group is unreachable because such documents are
refused earlier, and the third is unreachable because it is refused later. See finding F47.
-/
theorem compileGeneralModel_error_routes
    {model : DTR.GeneralModel}
    {message : String}
    (hRoutes :
      routesOf model =
        .error message) :
    compileGeneralModel model =
      .error message := by
  simp [
    compileGeneralModel,
    hRoutes
  ]

theorem compileGeneralModel_error_classes
    {model : DTR.GeneralModel}
    {routes : List GeneralRoute}
    {message : String}
    (hRoutes :
      routesOf model =
        .ok routes)
    (hClasses :
      compileGeneralReactiveClasses
          model.classes
          routes
          model.classes =
        .error message) :
    compileGeneralModel model =
      .error message := by
  simp [
    compileGeneralModel,
    hRoutes,
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
    {env : GeneralOutputPortEnv}
    {bodyKey : GeneralBodyKey}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiled : LF.GeneralBody}
    (hCompiled :
      compileGeneralBody
          env
          bodyKey
          index
          (statement :: remaining) =
        .ok compiled) :
    ∃ compiledStatement compiledRemaining,
      compileGeneralStmt
          env
          bodyKey
          index
          statement =
          .ok compiledStatement ∧
        compileGeneralBody
            env
            bodyKey
            (index + 1)
            remaining =
            .ok compiledRemaining ∧
          compiled =
            compiledStatement ::
              compiledRemaining := by

  cases hStatement :
      compileGeneralStmt
        env
        bodyKey
        index
        statement with

  | error message =>
      rw [
        compileGeneralBody_cons_error_head
          hStatement
      ] at hCompiled
      simp at hCompiled

  | ok compiledStatement =>
      cases hRemaining :
          compileGeneralBody
            env
            bodyKey
            (index + 1)
            remaining with

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

/--
Inverting the reaction **group**, which is where stage E's shape change reaches the inversion
layer.

The existential now produces a list rather than a reaction, and the equation it ends in names
both halves of the group explicitly — the action reaction consed onto the port reactions —
because that spelling is what §9.2's replacement order theorems consume. Nothing else about
the idiom changes.
-/
private theorem exists_of_compileGeneralMessageServerReactionGroup_ok
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactionGroup
          env
          routes
          className
          server =
        .ok group) :
    ∃ compiledBody,
      compileGeneralBody
          env
          (.messageServer server.name)
          0
          server.body =
          .ok compiledBody ∧
        group =
          assembleGeneralMessageReaction
              server
              compiledBody ::
            assembleGeneralPortReactions
              className
              server
              compiledBody
              routes := by

  cases hBody :
      compileGeneralBody
        env
        (.messageServer server.name)
        0
        server.body with

  | error message =>
      rw [
        compileGeneralMessageServerReactionGroup_error
          hBody
      ] at hCompiled
      simp at hCompiled

  | ok compiledBody =>
      rw [
        compileGeneralMessageServerReactionGroup_ok
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
    {env : GeneralOutputPortEnv}
    {classConstructor : DTR.GeneralConstructor}
    {reaction : LF.GeneralReaction}
    (hCompiled :
      compileGeneralConstructor
          env
          classConstructor =
        .ok reaction) :
    ∃ compiledBody,
      compileGeneralBody
          env
          .constructor
          0
          classConstructor.body =
          .ok compiledBody ∧
        reaction =
          assembleGeneralStartupReaction
            classConstructor
            compiledBody := by

  cases hBody :
      compileGeneralBody
        env
        .constructor
        0
        classConstructor.body with

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
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {compiled : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactions
          env
          routes
          className
          [] =
        .ok compiled) :
    compiled = [] := by
  rw [
    compileGeneralMessageServerReactions_nil
  ] at hCompiled
  injection hCompiled with hResult
  exact hResult.symm

private theorem exists_of_compileGeneralMessageServerReactions_cons_ok
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {compiled : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactions
          env
          routes
          className
          (server :: remaining) =
        .ok compiled) :
    ∃ group compiledRemaining,
      compileGeneralMessageServerReactionGroup
          env
          routes
          className
          server =
          .ok group ∧
        compileGeneralMessageServerReactions
            env
            routes
            className
            remaining =
            .ok compiledRemaining ∧
          compiled =
            group ++
              compiledRemaining := by

  cases hServer :
      compileGeneralMessageServerReactionGroup
        env
        routes
        className
        server with

  | error message =>
      rw [
        compileGeneralMessageServerReactions_cons_error_head
          hServer
      ] at hCompiled
      simp at hCompiled

  | ok group =>
      cases hRemaining :
          compileGeneralMessageServerReactions
            env
            routes
            className
            remaining with

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
              group,
              compiledRemaining,
              rfl,
              rfl,
              hResult.symm
            ⟩

/--
Inverting one class, which now has three sub-computations rather than two.

The environment is existentially quantified along with the two reaction groups, and it has to
be: `outputPortEnvOf` is a function of the class list and the class, so the env is *determined*
here, but the consumers of this lemma — every port theorem in §9.1 — need a name for it to
state what the reactor's `outputPorts` are.
-/
private theorem exists_of_compileGeneralReactiveClass_ok
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor) :
    ∃ env compiledStartupReaction compiledMessageReactions,
      outputPortEnvOf
          classes
          reactiveClass =
          .ok env ∧
        compileGeneralConstructor
            env
            reactiveClass.constructor =
            .ok compiledStartupReaction ∧
          compileGeneralMessageServerReactions
              env
              routes
              reactiveClass.name
              reactiveClass.messageServers =
              .ok compiledMessageReactions ∧
            reactor =
              assembleGeneralReactor
                reactiveClass
                env
                routes
                compiledStartupReaction
                compiledMessageReactions := by

  cases hEnv :
      outputPortEnvOf
        classes
        reactiveClass with

  | error message =>
      rw [
        compileGeneralReactiveClass_error_env
          hEnv
      ] at hCompiled
      simp at hCompiled

  | ok env =>
      cases hConstructor :
          compileGeneralConstructor
            env
            reactiveClass.constructor with

      | error message =>
          rw [
            compileGeneralReactiveClass_error_constructor
              hEnv
              hConstructor
          ] at hCompiled
          simp at hCompiled

      | ok compiledStartupReaction =>
          cases hMessageServers :
              compileGeneralMessageServerReactions
                env
                routes
                reactiveClass.name
                reactiveClass.messageServers with

          | error message =>
              rw [
                compileGeneralReactiveClass_error_messageServers
                  hEnv
                  hConstructor
                  hMessageServers
              ] at hCompiled
              simp at hCompiled

          | ok compiledMessageReactions =>
              rw [
                compileGeneralReactiveClass_ok
                  hEnv
                  hConstructor
                  hMessageServers
              ] at hCompiled
              injection hCompiled with hResult

              -- `rfl` closes the first conjunct and *only* the first, which is worth
              -- recording because guessing uniformly either way fails here. `cases h : e`
              -- rewrites `e` in the goal to the matched pattern, and
              -- `outputPortEnvOf classes reactiveClass` is a closed term, so conjunct one
              -- arrives already reduced to `.ok env = .ok env`. The next two are applied to
              -- the existential's own bound variables, which no such rewrite can reach, so
              -- they need the hypotheses the cases produced.
              exact
                ⟨
                  env,
                  compiledStartupReaction,
                  compiledMessageReactions,
                  rfl,
                  hConstructor,
                  hMessageServers,
                  hResult.symm
                ⟩

private theorem eq_nil_of_compileGeneralReactiveClasses_nil_ok
    {allClasses : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {compiled : List LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClasses
          allClasses
          routes
          [] =
        .ok compiled) :
    compiled = [] := by
  rw [
    compileGeneralReactiveClasses_nil
  ] at hCompiled
  injection hCompiled with hResult
  exact hResult.symm

private theorem exists_of_compileGeneralReactiveClasses_cons_ok
    {allClasses : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {remaining : List DTR.GeneralReactiveClass}
    {compiled : List LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClasses
          allClasses
          routes
          (reactiveClass :: remaining) =
        .ok compiled) :
    ∃ reactor compiledRemaining,
      compileGeneralReactiveClass
          allClasses
          routes
          reactiveClass =
          .ok reactor ∧
        compileGeneralReactiveClasses
            allClasses
            routes
            remaining =
            .ok compiledRemaining ∧
          compiled =
            reactor ::
              compiledRemaining := by

  cases hClass :
      compileGeneralReactiveClass
        allClasses
        routes
        reactiveClass with

  | error message =>
      rw [
        compileGeneralReactiveClasses_cons_error_head
          hClass
      ] at hCompiled
      simp at hCompiled

  | ok reactor =>
      cases hRemaining :
          compileGeneralReactiveClasses
            allClasses
            routes
            remaining with

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

/--
Inverting the model, and the one place in this section where the idiom's last step changes.

Stage D's version finished with `injection`, because `compileGeneralModel` finished with `.ok`.
Stage E's finishes with the guard, so the successful branch's equation is
`guardGeneralProgram (assembleGeneralProgram …) = .ok program` — not a constructor application
at all — and `injection` has nothing to take apart. `eq_of_guardGeneralProgram_ok` does that
work instead, which is the reason that lemma is stated separately from the well-formedness
half.

The consequence is worth writing down because every §9.1 theorem inherits it: the guard is
**transparent to shape**. What it accepts, it accepts unchanged, so every arithmetic fact about
the assembled program is a fact about the returned program, and the port and connection
theorems below need no new hypothesis to say so.
-/
private theorem exists_of_compileGeneralModel_ok
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    ∃ routes compiledReactors,
      routesOf model =
          .ok routes ∧
        compileGeneralReactiveClasses
            model.classes
            routes
            model.classes =
            .ok compiledReactors ∧
          program =
            assembleGeneralProgram
              model
              routes
              compiledReactors := by

  cases hRoutes :
      routesOf model with

  | error message =>
      rw [
        compileGeneralModel_error_routes
          hRoutes
      ] at hCompiled
      simp at hCompiled

  | ok routes =>
      cases hClasses :
          compileGeneralReactiveClasses
            model.classes
            routes
            model.classes with

      | error message =>
          rw [
            compileGeneralModel_error_classes
              hRoutes
              hClasses
          ] at hCompiled
          simp at hCompiled

      | ok compiledReactors =>
          rw [
            compileGeneralModel_ok
              hRoutes
              hClasses
          ] at hCompiled
          -- `rfl` for the first conjunct and the hypothesis for the second, for the reason
          -- given at `exists_of_compileGeneralReactiveClass_ok`: `routesOf model` is closed
          -- and was rewritten by the cases, `compileGeneralReactiveClasses model.classes
          -- routes model.classes` mentions the bound `routes` and was not.
          exact
            ⟨
              routes,
              compiledReactors,
              rfl,
              hClasses,
              (eq_of_guardGeneralProgram_ok
                hCompiled).symm
            ⟩

/-!
## The boundary, as arithmetic

Stage D wrote three facts here — reactors have no ports, programs have no connections, the
reactor list is the class list — and predicted that *"when stage E arrives, the first two are
the theorems that must change, which is the cheapest possible alarm that the boundary has
moved."* The prediction held exactly: both broke, at build time, and neither could be repaired
by editing a proof. What follows is their replacement.

The replacements are **not** weakenings. Each one states where the ports and the connections
come from, which is strictly more than the old ones said, and each is still an equation
between two lists rather than a claim about sets or lengths — so stage F can still name a
port by position.

Two shapes appear, and the difference between them is the port asymmetry showing up in the
proofs. Input ports are a projection of the *model's* routes and the class's name, so the
class-level theorem states them outright. Output ports are a projection of the class's
*environment*, and the environment is a computation that can fail, so every theorem that
mentions output ports has to produce the resolution alongside them. That is why
`compileGeneralReactiveClass_outputPorts` is an existential and its input-port twin is not.
-/

/--
A compiled reactor's input ports are the routing projection for its class.

Stage D's `compileGeneralReactiveClass_ports` in the half that survives without an
existential. The right-hand side does not mention the class list, the environment, or anything
this function computed: input ports are decided entirely by the model's routing table and the
receiving class's name, which is the whole content of the design's *"input ports are declared
on the receiving class as a union over every sending instance."*
-/
theorem compileGeneralReactiveClass_inputPorts
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor) :
    reactor.inputPorts =
      generalInputPortsOf
        reactiveClass.name
        routes := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      _,
      _,
      _,
      _,
      _,
      _,
      hReactor
    ⟩

  subst hReactor
  simp

/--
A compiled reactor's output ports are the projection of the environment that was resolved for
its class.

The existential is not slack: `outputPortEnvOf` is a function, so the environment is
determined by the two arguments, and this theorem's `∃` merely gives it a name. Stating it
that way rather than with `outputPortEnvOf classes reactiveClass` inlined on the right keeps
the conclusion an equation between two *port lists* — `generalOutputPortsOf` applied to an
`Except` would not typecheck, and pushing the resolution into the statement with a hypothesis
would force every caller to have resolved it first.
-/
theorem compileGeneralReactiveClass_outputPorts
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor) :
    ∃ env,
      outputPortEnvOf
          classes
          reactiveClass =
          .ok env ∧
        reactor.outputPorts =
          generalOutputPortsOf
            env := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      env,
      _,
      _,
      hEnv,
      _,
      _,
      hReactor
    ⟩

  subst hReactor

  exact
    ⟨
      env,
      hEnv,
      by
        simp
    ⟩

/--
A compiled reactor is named after its class.
-/
theorem compileGeneralReactiveClass_name
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
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
      _,
      _,
      hReactor
    ⟩

  subst hReactor
  simp

/--
Every reactor of a compiled class list has some class's ports, and both port lists are routing
projections of that class.

Stage D's membership-shaped theorem, with `[]` replaced by the two projections and the class
they belong to produced as a witness. The witness is what makes this usable: at program level
a reactor is picked out of a list, and nothing in the picking says which class it came from,
so a theorem that could not name the class would say nothing an argument about the *printer's*
output could consume.

`allClasses` and `classes` are both quantified and are *not* required to be equal. The
induction walks the second; the first is the lookup table, held fixed. `compileGeneralModel`
instantiates both to `model.classes`, and no theorem here needs them related — which is worth
noticing, because it means this induction stays valid if a later stage compiles a subset of
the classes.
-/
theorem compileGeneralReactiveClasses_ports :
    ∀ (allClasses : List DTR.GeneralReactiveClass)
      (routes : List GeneralRoute)
      (classes : List DTR.GeneralReactiveClass)
      (compiled : List LF.GeneralReactor),
      compileGeneralReactiveClasses
          allClasses
          routes
          classes =
          .ok compiled →
        ∀ (reactor : LF.GeneralReactor),
          reactor ∈ compiled →
            ∃ reactiveClass env,
              reactiveClass ∈ classes ∧
                outputPortEnvOf
                    allClasses
                    reactiveClass =
                    .ok env ∧
                  reactor.inputPorts =
                      generalInputPortsOf
                        reactiveClass.name
                        routes ∧
                    reactor.outputPorts =
                      generalOutputPortsOf
                        env := by

  intro allClasses routes classes
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

          rcases
              compileGeneralReactiveClass_outputPorts
                hClass with
            ⟨
              env,
              hEnv,
              hOutputPorts
            ⟩

          exact
            ⟨
              reactiveClass,
              env,
              List.mem_cons.mpr
                (Or.inl rfl),
              hEnv,
              compileGeneralReactiveClass_inputPorts
                hClass,
              hOutputPorts
            ⟩

      | inr hTail =>
          rcases
              inductionHypothesis
                compiledRemaining
                hRemaining
                reactor
                hTail with
            ⟨
              witnessClass,
              env,
              hWitnessMember,
              hEnv,
              hInputPorts,
              hOutputPorts
            ⟩

          exact
            ⟨
              witnessClass,
              env,
              List.mem_cons.mpr
                (Or.inr hWitnessMember),
              hEnv,
              hInputPorts,
              hOutputPorts
            ⟩

/--
A compiled program's connections are the routing projection of the model's routes.

The theorem stage E had to break, in its replacement form. It is still `rfl` under the
assembler and the guard, and that remains the point of routing the program through a total
assembler: the connection list is a property of a function with no failure case, so no branch
of the partial layer can quietly add or drop a connection, and the guard — which is the only
thing between the assembler and the caller — is transparent to shape.

One connection per route, in `routesOf`'s order, which is main-block declaration order. That
is a stronger statement than the empty list ever was, and it is what the target gate's *"three
connections on one `Gateway`"* assertion checks from the outside.
-/
theorem compileGeneralModel_connections
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    ∃ routes,
      routesOf model =
          .ok routes ∧
        program.connections =
          generalConnectionsOf
            routes := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      routes,
      _,
      hRoutes,
      _,
      hProgram
    ⟩

  subst hProgram

  exact
    ⟨
      routes,
      hRoutes,
      by
        simp
    ⟩

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
      _,
      _,
      hProgram
    ⟩

  subst hProgram
  simp

/--
Every reactor of a compiled program has some class's ports, and both port lists are routing
projections of that class.

The program-level form, and the one an argument about the printer's output uses. Stage D's
version of this theorem was the load-bearing half of its §8 argument — the printer's refusals
were justified by *"no reactor declares a port"* — and that justification is gone. What
replaces it is not another blanket claim about the printer but the guard: a program whose
generated port names collide, or whose connections name an endpoint no reactor declares, is
refused by `guardGeneralProgram` before any caller can print it.
-/
theorem compileGeneralModel_ports
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    ∃ routes,
      routesOf model =
          .ok routes ∧
        ∀ (reactor : LF.GeneralReactor),
          reactor ∈ program.reactors →
            ∃ reactiveClass env,
              reactiveClass ∈ model.classes ∧
                outputPortEnvOf
                    model.classes
                    reactiveClass =
                    .ok env ∧
                  reactor.inputPorts =
                      generalInputPortsOf
                        reactiveClass.name
                        routes ∧
                    reactor.outputPorts =
                      generalOutputPortsOf
                        env := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      routes,
      compiledReactors,
      hRoutes,
      hClasses,
      hProgram
    ⟩

  subst hProgram

  refine
    ⟨
      routes,
      hRoutes,
      ?_
    ⟩

  intro reactor hMember

  rw [
    assembleGeneralProgram_reactors
  ] at hMember

  exact
    compileGeneralReactiveClasses_ports
      model.classes
      routes
      model.classes
      compiledReactors
      hClasses
      reactor
      hMember

/--
The reactor names of a compiled class list are the class names, in source order.
-/
theorem compileGeneralReactiveClasses_reactorNames :
    ∀ (allClasses : List DTR.GeneralReactiveClass)
      (routes : List GeneralRoute)
      (classes : List DTR.GeneralReactiveClass)
      (compiled : List LF.GeneralReactor),
      compileGeneralReactiveClasses
          allClasses
          routes
          classes =
          .ok compiled →
        compiled.map
            (fun reactor =>
              reactor.name) =
          classes.map
            (fun reactiveClass =>
              reactorNameFor reactiveClass.name) := by

  intro allClasses routes classes
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

Untouched in substance by stage E, which is worth one line of comment: the reactor list is the
only part of the program that routing does not reshape, because a route changes what a reactor
*declares* and never how many reactors there are.
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
      routes,
      compiledReactors,
      _,
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
      routes
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

**Stage E falsified two of these theorems outright, and they are replaced rather than
weakened.** Stage D's `compileGeneralMessageServerReactions_names` and
`compileGeneralReactiveClass_reactionNames` both said a class's reaction names are
`messageServers.map messageReactionNameFor` — one reaction per message server. §7.3 makes that
false: a message server reached by two external senders gets its action reaction *and* two port
reactions, so the reaction list is longer than the server list and no substitution on the
right-hand side can fix a length mismatch.

The replacements are stated against a **specification function**, `generalReactionNamesOf`, and
that deserves a defence because a specification that mirrors the implementation can be vacuous.
This one is not, for a reason that is checkable by reading it: the specification is written
entirely in terms of *names* — `messageReactionNameFor`, `portReactionNameFor`, and the route
filter — while the implementation is written in terms of *reactions*, through
`assembleGeneralMessageReaction` and `assembleGeneralPortReactions`. The theorem therefore
pins three things a reordering would break: that the action reaction comes first in each group,
that a group's port reactions follow the route order, and that groups appear in message-server
source order. Those are exactly what stage G permutes and what stage F's fan-in ordering
argument reads.

`List.flatMap` was the obvious alternative spelling and is deliberately avoided: its core name
has churned in the same family as `List.enum` and `String.capitalize`, and this development
depends on no such function. An explicit recursive specification costs nine lines and cannot
churn.
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
The reaction names one message server contributes, in the order they are declared.

The specification the section note above defends. Total, and independent of both the
translation and the `Except` layer — a reader can compare it against the design's §7.3 table
without holding any of this file in their head.

`routes` and `className` are before the colon because neither varies in the recursion; the
server list is after it, which is the same discipline every recursive definition in this
development follows.
-/
def generalReactionNamesOf
    (routes : List GeneralRoute)
    (className : ClassName) :
    List DTR.GeneralMessageServer →
    List ReactionName

  | [] =>
      []

  | server :: remaining =>
      (messageReactionNameFor server.name ::
          (generalRoutesIntoMessageServer
            className
            server.name
            routes).map
            (fun route =>
              portReactionNameFor
                (generalInputPortOfRoute route))) ++
        generalReactionNamesOf
          routes
          className
          remaining

/--
One message server's reaction group carries its action reaction first, then one port reaction
per route into it, in route order.

The group-level half of the replacement, and the place the naming rule is pinned. Note what it
says about a message server nothing sends to from outside: the filtered route list is empty, so
the group is a one-element list and the reactor looks exactly as stage D left it. That is the
precise sense in which stage E is conservative on the inherited fixtures — not an appeal to
their contents, but a consequence of this equation.
-/
theorem compileGeneralMessageServerReactionGroup_names
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactionGroup
          env
          routes
          className
          server =
        .ok group) :
    group.map
        (fun reaction =>
          reaction.name) =
      messageReactionNameFor server.name ::
        (generalRoutesIntoMessageServer
          className
          server.name
          routes).map
          (fun route =>
            portReactionNameFor
              (generalInputPortOfRoute route)) := by

  rcases
      exists_of_compileGeneralMessageServerReactionGroup_ok
        hCompiled with
    ⟨
      compiledBody,
      _,
      hGroup
    ⟩

  subst hGroup

  change
    (assembleGeneralMessageReaction
          server
          compiledBody).name ::
        (assembleGeneralPortReactions
            className
            server
            compiledBody
            routes).map
            (fun reaction =>
              reaction.name) =
      messageReactionNameFor server.name ::
        (generalRoutesIntoMessageServer
          className
          server.name
          routes).map
          (fun route =>
            portReactionNameFor
              (generalInputPortOfRoute route))

  rw [
    assembleGeneralMessageReaction_name,
    assembleGeneralPortReactions_names
  ]

/--
Compiled reactions carry the reaction names of their message servers, groups in source order.

The `Except` counterpart of the three lemmas above: the reaction list is not a `map` of the
server list, because compilation of a body can fail, so the induction has to invert a
successful compilation at each step. That is what the private inversion lemmas are for.

Stage D's version of this theorem is the one §7.3 falsified. This is its replacement, and the
`++` in `generalReactionNamesOf` is where the shape change lives: groups are concatenated, not
consed, so the reaction list is longer than the server list exactly when some server is reached
from outside.
-/
theorem compileGeneralMessageServerReactions_names :
    ∀ (env : GeneralOutputPortEnv)
      (routes : List GeneralRoute)
      (className : ClassName)
      (servers : List DTR.GeneralMessageServer)
      (compiled : List LF.GeneralReaction),
      compileGeneralMessageServerReactions
          env
          routes
          className
          servers =
          .ok compiled →
        compiled.map
            (fun reaction =>
              reaction.name) =
          generalReactionNamesOf
            routes
            className
            servers := by

  intro env routes className servers
  induction servers with

  | nil =>
      intro compiled hCompiled

      simp [
        generalReactionNamesOf,
        eq_nil_of_compileGeneralMessageServerReactions_nil_ok
          hCompiled
      ]

  | cons server remaining inductionHypothesis =>
      intro compiled hCompiled

      rcases
          exists_of_compileGeneralMessageServerReactions_cons_ok
            hCompiled with
        ⟨
          group,
          compiledRemaining,
          hServer,
          hRemaining,
          hCompiledEq
        ⟩

      subst hCompiledEq

      simp [
        generalReactionNamesOf,
        compileGeneralMessageServerReactionGroup_names
          hServer,
        inductionHypothesis
          compiledRemaining
          hRemaining
      ]

/--
A compiled reactor declares one logical action per message server, named after it, in
source order.

Unaffected by stage E, and the contrast with the reaction list is the finding worth keeping:
one action per message server no matter how many senders reach it, because an action is the
*self*-delivery mechanism and self-sends were never routed. A message server reached by two
external senders has one action and three reactions.
-/
theorem compileGeneralReactiveClass_actionNames
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
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
A compiled reactor's message reactions are its message servers' reaction groups, in source
order.

This is the theorem stage G permutes, and the replacement for the version §7.3 falsified.
Nothing here sorts, so the order on the right is the order the source was written in — now
with each group's internal order fixed as well, which stage G has to respect: permuting whole
groups is a reordering of message servers, permuting *within* a group reorders the delivery
paths of one message server against each other, and those are different things with different
observable effects.
-/
theorem compileGeneralReactiveClass_reactionNames
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor) :
    reactor.messageReactions.map
        (fun reaction =>
          reaction.name) =
      generalReactionNamesOf
        routes
        reactiveClass.name
        reactiveClass.messageServers := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      env,
      _,
      compiledMessageReactions,
      _,
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
      env
      routes
      reactiveClass.name
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
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
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

Stage E makes this theorem carry more weight than it did, and the reason is F32-shaped. A
constructor that sends externally now emits a `setPort` inside the startup reaction, whose
arguments are compiled expressions over exactly these parameters, so a mismatch here would
produce a startup reaction that reads a name the reactor does not declare — and
`reactorsWellFormed` would refuse the whole program with a diagnostic pointing at the port
rather than at the parameter list.
-/
theorem compileGeneralReactiveClass_startupParameters
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor) :
    reactor.startupReaction.parameters =
      reactor.parameters.map
        (fun parameter =>
          parameter.name) := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      _,
      compiledStartupReaction,
      _,
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
## What acceptance guarantees

Stage D closed this file with an `iff`: a model translates exactly when every send in it
targets `self`. That theorem is deleted, for the reason the note at §4 gives — its right-hand
side stopped naming anything about this translation — and this section is what stands in its
place.

The replacement is not a weaker `iff`, and it is not the same claim with a wider fragment
substituted in. It is a claim of a different shape, about a different object. Stage D's
theorem characterised acceptance in terms of the *input*: read the model, decide the
predicate, and you know the answer. This section states what acceptance tells you about the
*output*: whatever comes back is a well-formed LF program. The two are not comparable, and
the trade was deliberate. An input-side characterisation is the more informative theorem when
the refusal surface is one syntactic construct; it becomes unwritable once the refusal surface
is the conjunction of nine structural conditions on a translated artefact, because the
predicate that characterises it would have to re-derive the whole translation.

What is *lost* is worth naming precisely, because a later reader will otherwise assume it was
overlooked. Nothing here says a model in the paper's DTR fragment is accepted. That is the
converse direction — a sufficient syntactic condition — and it is deferred whole to the task
this file's header records as the site-totality obligation. The reason for deferring is
recorded there and is about diagnosis, not difficulty: the sufficient condition rests on an
induction showing that every external send site of a class has an entry in that class's
resolved environment, and an induction of that size written against a module that has never
once elaborated turns a single gate failure into an undiagnosable one. The gate meanwhile
answers the same question empirically for every committed fixture, and answers it more
convincingly than a theorem would, since it runs the real `lfc`.

So the honest summary of the fragment boundary after stage E is: acceptance is *sound* by
proof, and *sufficiently wide* by measurement. Stage D had it the other way around.
-/

/--
Anything this translation accepts is a well-formed LF program.

The soundness half of §9.2, and the theorem that makes the guard worth having rather than
merely defensive. Every well-formedness clause the LF layer knows how to state — reactor names
distinct, instance names distinct, every instance resolving to a declared reactor, argument
counts agreeing, every connection's endpoints declared, no input port targeted twice — holds of
the returned program, because the guard decided the real predicate and the guard is transparent
to shape.

Note what this does *not* require: no hypothesis about the model, no side condition, no
appeal to a fixture. The reason it can be unconditional is that the guard is the last thing
`compileGeneralModel` does, which is a fact about the definition and is why §9's guard was put
at the boundary rather than inside `assembleGeneralProgram`.
-/
theorem compileGeneralModel_wellFormed
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    program.wellFormed = true := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      routes,
      compiledReactors,
      hRoutes,
      hClasses,
      hProgram
    ⟩

  rw [
    compileGeneralModel_ok
      hRoutes
      hClasses
  ] at hCompiled

  rw [
    hProgram
  ]

  exact
    guardGeneralProgram_wellFormed
      hCompiled

/--
Extract the last conjunct of well-formedness.

A local copy of a lemma `Relico/LF/GeneralWellFormed.lean` already proves, duplicated because
that copy is `private` and this file is not the module it is private to. Duplicated rather than
de-privatised on purpose: the LF module's copy exists to serve proofs *about* well-formedness,
and making it public would invite translation-side proofs to reach past the `wellFormed`
interface for the other eight conjuncts one at a time, which is the habit that turns a
nine-clause predicate into nine independent obligations.

The proof is the house pattern — revert, unfold, split the conjunct — and it works for the last
conjunct specifically because `&&` is strict on the right: the `false` branch makes the whole
chain `false`, which contradicts the hypothesis, and the `true` branch leaves the goal
trivially true.
-/
private theorem targetEndpointsUnique_of_wellFormed
    {program : LF.GeneralProgram}
    (hWellFormed :
      program.wellFormed =
        true) :
    program.targetEndpointsUnique =
      true := by

  revert hWellFormed
  unfold LF.GeneralProgram.wellFormed
  cases program.targetEndpointsUnique <;>
    simp

/--
No input port of an accepted program is the target of two connections.

The corollary §9.2 singles out, and the one clause of well-formedness that stage E's routing
could plausibly have violated. `lfc 0.11.0` rejects many-to-one connections — measured, and the
reason input ports are keyed by *route* rather than by receiving class — so this is the clause
that stands between a translated program and a target compiler error, and the only one whose
failure the Lean layer would otherwise discover second-hand from the `lfc` gate.

Stated as a consequence of the guard, which is not a weaker placeholder for a construction
proof but the strongest form available: **a construction proof does not exist.**

An earlier version of this docstring said such a proof "would say the routing *cannot* produce
a repeated target and would therefore let the guard's clause be retired as dead", and deferred
it behind the site-totality induction below. Finding **F48** in `docs/STAGE_E_FINDINGS.md`
refutes all three parts, by evaluation rather than by argument. Routing *can* produce a repeated
target from a model `DTR.GeneralModel.wellFormed` accepts: a class that sends `reportTo` to a
declared known rebec `hub` and `report` to a declared known rebec `toHub`, instantiated with
both rebecs bound to one actor, yields two connections onto
`hubActor.reportToToHubFromProbe`, because `outputPortNameFor` does not escape its separator
and the site suffix is empty when a pair has one site. Site totality is also the wrong
instrument — it governs send sites, output ports and the reachability of the defensive arm at
`compileGeneralStmt`, whereas a repeated endpoint is a fact about the *receiver's* input ports —
so the deferral was parked behind work that could never have discharged it. And the clause must
**not** be retired: it is what turns that collision into a refusal rather than emitted LF that
`lfc 0.11.0` rejects as a many-to-one connection.

The naming rule's own docstring at `Relico/Translation/NameGeneration.lean:107` had said the
right thing all along — that the function is not injective, and that uniqueness of generated
names is "decided on the program the translation builds". This docstring contradicted it. Two
prose paragraphs in one build closure disagreeing is not something any gate can catch, which is
why the standing preference is a label a `grep` can check.

So a repeated target is a refusal with a diagnostic naming the clause, permanently and by
design, and this theorem is what says so. That refusal is asserted under
`PASS_ALIASED_ENDPOINT_COLLISION_REFUSED` in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean`, so F48's witness is checked on every gate
run instead of being described here. What remains achievable is a strictly weaker *relative*
statement — `reactorsWellFormed` together with `instancesResolve` implies this clause, since
`generalInputPortsOf` maps over exactly the routes `generalConnectionsOf` does — carried as item
15 of that findings file's open list. It would derive one guard clause from another rather than
from the construction, so it licenses retiring nothing either.
-/
theorem compileGeneralModel_targetEndpointsUnique
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    program.targetEndpointsUnique =
      true :=
  targetEndpointsUnique_of_wellFormed
    (compileGeneralModel_wellFormed
      hCompiled)

/-!
## Site totality

The defensive arm at `compileGeneralStmt` — the one whose diagnostic says *"this is a defect in
the translator and not in the model"* — is unreachable whenever the environment it is given came
from `outputPortEnvOf`. This section proves that, and the proof buys more than the design asked
for.

`docs/STAGE_E_DESIGN.md` §8 asks for a sufficient condition for acceptance. What comes out is
*totality*: **given a resolved environment, compiling a reactive class cannot fail at all.** The
reason is a measurement rather than an argument. Every `.error` in this file below
`compileGeneralStmt` is a *propagation* — a `match` arm that returns a refusal its callee
produced — and the only place in the whole body-compilation path where a refusal is
**originated** is that one defensive arm. So removing its reachability removes the last way any
of `compileGeneralBody`, `compileGeneralConstructor`,
`compileGeneralMessageServerReactionGroup`, `compileGeneralMessageServerReactions` or
`compileGeneralReactiveClass` can refuse, once `outputPortEnvOf` has succeeded. Their `.error`
arms remain, because they are what carries a *routing* refusal outward, and routing can still
refuse for the four causes `compileGeneralReactiveClass_error_env` enumerates.

The arm itself is also kept. A proof that a branch is unreachable is a proof about a fixed
program, and stage F changes this program; deleting the arm would replace a refusal with a
`sorry`-shaped hole in the next stage that adds a statement form. §6.3's `for` loop is the
concrete case — it introduces statements whose sends this traversal does not yet index, and the
requirement recorded there is that such a statement must break *loudly*. It breaks loudly here:
`exists_compileGeneralBody` cases on the statement constructors exhaustively, so a new
constructor is a build error in this file and not a silently unproved obligation.

Nothing in this section is about port *names*. The naming rule is not injective (finding F34,
and §4.3's would-be injectivity lemma is refuted as F42), so no fact about ports follows from
site distinctness; §10.2's `Nodup` theorem needs the guard's `declaredNames.Nodup` and is proved
separately.
-/

/--
Compiling an assignment cannot fail.
-/
theorem compileGeneralStmt_assign
    (env : GeneralOutputPortEnv)
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (target : VarName)
    (value : DTR.GeneralExpr) :
    compileGeneralStmt
        env
        bodyKey
        index
        (
          .assign
            target
            value
        ) =
      .ok
        (.assign
          target
          (compileGeneralExpr
            value)) := by
  simp [
    compileGeneralStmt
  ]

/--
Compiling a self-send cannot fail: it needs no port, only the message's own action.
-/
theorem compileGeneralStmt_send_selfTarget
    (env : GeneralOutputPortEnv)
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (message : MsgName)
    (arguments : List DTR.GeneralExpr)
    (delay : Delay) :
    compileGeneralStmt
        env
        bodyKey
        index
        (
          .send
            .selfTarget
            message
            arguments
            delay
        ) =
      .ok
        (.schedule
          (actionNameFor
            message)
          (arguments.map
            compileGeneralExpr)
          delay) := by
  simp [
    compileGeneralStmt
  ]

/--
Compiling an external send succeeds exactly when the environment has an entry at its address.

The address is built here rather than taken as an argument, because it is the *statement's* own
position and a caller free to pass a different one could satisfy this lemma while compiling the
wrong send.
-/
theorem compileGeneralStmt_send_knownRebec_ok
    (env : GeneralOutputPortEnv)
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (rebec : KnownRebecName)
    (message : MsgName)
    (arguments : List DTR.GeneralExpr)
    (delay : Delay)
    {entry : GeneralOutputPortEntry}
    (hLookup :
      generalEntryAtSite?
          env
          {
            body :=
              bodyKey

            index :=
              index
          } =
        some entry) :
    compileGeneralStmt
        env
        bodyKey
        index
        (
          .send
            (.knownRebec
              rebec)
            message
            arguments
            delay
        ) =
      .ok
        (.setPort
          entry.outputPort
          (arguments.map
            compileGeneralExpr)) := by
  simp [
    compileGeneralStmt,
    hLookup
  ]

/--
A body whose every external send has an entry compiles.

The hypothesis is quantified over `externalSendsFromIndex bodyKey index body` — the sends of
*this* body from *this* index — and not over the class's whole send list, which is what makes
the induction go through: the tail's hypothesis is the head's hypothesis with one statement
removed, and that is exactly what the three arm equations in `Relico/Translation/GeneralRouting.lean`
say. The index advances in step with `externalSendsFromIndex` because both functions advance it
once per statement, which is the alignment the note on `compileGeneralBody` flags as worth
stating even though no earlier theorem needed it. This theorem needs it.
-/
theorem exists_compileGeneralBody
    (env : GeneralOutputPortEnv)
    (bodyKey : GeneralBodyKey)
    (body : DTR.GeneralBody) :
    ∀ index : Nat,
      (∀ send ∈
          externalSendsFromIndex
            bodyKey
            index
            body,
        ∃ entry,
          generalEntryAtSite?
              env
              send.site =
            some entry) →
      ∃ compiled,
        compileGeneralBody
            env
            bodyKey
            index
            body =
          .ok compiled := by

  induction body with

  | nil =>
      intro index _

      exact
        ⟨[],
         compileGeneralBody_nil
           env
           bodyKey
           index⟩

  | cons statement remaining inductionHypothesis =>
      intro index hSends

      cases statement with

      | assign target value =>

          have hStatement :
              compileGeneralStmt
                  env
                  bodyKey
                  index
                  (
                    .assign
                      target
                      value
                  ) =
                .ok
                  (.assign
                    target
                    (compileGeneralExpr
                      value)) :=
            compileGeneralStmt_assign
              env
              bodyKey
              index
              target
              value

          obtain ⟨compiledRemaining, hRemaining⟩ :=
            inductionHypothesis
              (index + 1)
              (by
                intro send hMember

                exact
                  hSends
                    send
                    (by
                      rw [
                        externalSendsFromIndex_assign
                      ]

                      exact hMember))

          exact
            ⟨_,
             compileGeneralBody_cons_ok
               hStatement
               hRemaining⟩

      | send target message arguments delay =>

          cases target with

          | selfTarget =>

              have hStatement :
                  compileGeneralStmt
                      env
                      bodyKey
                      index
                      (
                        .send
                          .selfTarget
                          message
                          arguments
                          delay
                      ) =
                    .ok
                      (.schedule
                        (actionNameFor
                          message)
                        (arguments.map
                          compileGeneralExpr)
                        delay) :=
                compileGeneralStmt_send_selfTarget
                  env
                  bodyKey
                  index
                  message
                  arguments
                  delay

              obtain ⟨compiledRemaining, hRemaining⟩ :=
                inductionHypothesis
                  (index + 1)
                  (by
                    intro send hMember

                    exact
                      hSends
                        send
                        (by
                          rw [
                            externalSendsFromIndex_send_selfTarget
                          ]

                          exact hMember))

              exact
                ⟨_,
                 compileGeneralBody_cons_ok
                   hStatement
                   hRemaining⟩

          | knownRebec rebec =>

              obtain ⟨entry, hEntry⟩ :=
                hSends
                  {
                    site :=
                      {
                        body :=
                          bodyKey

                        index :=
                          index
                      }

                    knownRebec :=
                      rebec

                    message :=
                      message

                    delay :=
                      delay
                  }
                  (by
                    rw [
                      externalSendsFromIndex_send_knownRebec,
                      List.mem_cons
                    ]

                    exact
                      Or.inl
                        rfl)

              have hLookup :
                  generalEntryAtSite?
                      env
                      {
                        body :=
                          bodyKey

                        index :=
                          index
                      } =
                    some entry :=
                hEntry

              have hStatement :
                  compileGeneralStmt
                      env
                      bodyKey
                      index
                      (
                        .send
                          (.knownRebec
                            rebec)
                          message
                          arguments
                          delay
                      ) =
                    .ok
                      (.setPort
                        entry.outputPort
                        (arguments.map
                          compileGeneralExpr)) :=
                compileGeneralStmt_send_knownRebec_ok
                  env
                  bodyKey
                  index
                  rebec
                  message
                  arguments
                  delay
                  hLookup

              obtain ⟨compiledRemaining, hRemaining⟩ :=
                inductionHypothesis
                  (index + 1)
                  (by
                    intro send hMember

                    exact
                      hSends
                        send
                        (by
                          rw [
                            externalSendsFromIndex_send_knownRebec,
                            List.mem_cons
                          ]

                          exact
                            Or.inr
                              hMember))

              exact
                ⟨_,
                 compileGeneralBody_cons_ok
                   hStatement
                   hRemaining⟩

/--
A constructor whose every external send has an entry compiles.
-/
theorem exists_compileGeneralConstructor
    (env : GeneralOutputPortEnv)
    (classConstructor : DTR.GeneralConstructor)
    (hSends :
      ∀ send ∈
          externalSendsOfBody
            .constructor
            classConstructor.body,
        ∃ entry,
          generalEntryAtSite?
              env
              send.site =
            some entry) :
    ∃ compiled,
      compileGeneralConstructor
          env
          classConstructor =
        .ok compiled := by

  obtain ⟨compiledBody, hBody⟩ :=
    exists_compileGeneralBody
      env
      .constructor
      classConstructor.body
      0
      hSends

  exact
    ⟨_,
     compileGeneralConstructor_ok
       hBody⟩

/--
A message server whose every external send has an entry compiles, together with its arrivals.

The arrival reactions are assembled, not compiled — `assembleGeneralPortReactions` is total —
so the group's only failure is the body's, which is the sentence the note on
`compileGeneralMessageServerReactionGroup` already claims and this theorem now supports.
-/
theorem exists_compileGeneralMessageServerReactionGroup
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (className : ClassName)
    (server : DTR.GeneralMessageServer)
    (hSends :
      ∀ send ∈
          externalSendsOfBody
            (.messageServer
              server.name)
            server.body,
        ∃ entry,
          generalEntryAtSite?
              env
              send.site =
            some entry) :
    ∃ compiled,
      compileGeneralMessageServerReactionGroup
          env
          routes
          className
          server =
        .ok compiled := by

  obtain ⟨compiledBody, hBody⟩ :=
    exists_compileGeneralBody
      env
      (.messageServer
        server.name)
      server.body
      0
      hSends

  exact
    ⟨_,
     compileGeneralMessageServerReactionGroup_ok
       hBody⟩

/--
A list of message servers, each of whose sends has an entry, compiles.
-/
theorem exists_compileGeneralMessageServerReactions
    (env : GeneralOutputPortEnv)
    (routes : List GeneralRoute)
    (className : ClassName)
    (servers : List DTR.GeneralMessageServer) :
    (∀ server ∈ servers,
      ∀ send ∈
          externalSendsOfBody
            (.messageServer
              server.name)
            server.body,
        ∃ entry,
          generalEntryAtSite?
              env
              send.site =
            some entry) →
    ∃ compiled,
      compileGeneralMessageServerReactions
          env
          routes
          className
          servers =
        .ok compiled := by

  induction servers with

  | nil =>
      intro _

      exact
        ⟨[],
         compileGeneralMessageServerReactions_nil
           env
           routes
           className⟩

  | cons server remaining inductionHypothesis =>
      intro hSends

      obtain ⟨group, hGroup⟩ :=
        exists_compileGeneralMessageServerReactionGroup
          env
          routes
          className
          server
          (hSends
            server
            (by
              simp))

      obtain ⟨compiledRemaining, hRemaining⟩ :=
        inductionHypothesis
          (by
            intro other hOther

            exact
              hSends
                other
                (by
                  rw [
                    List.mem_cons
                  ]

                  exact
                    Or.inr
                      hOther))

      exact
        ⟨_,
         compileGeneralMessageServerReactions_cons_ok
           hGroup
           hRemaining⟩

/--
**A class with a resolved environment compiles. There is no other way for it to fail.**

The theorem §8 asks for, in the strongest of the available forms. Its hypothesis is a success of
`outputPortEnvOf` and nothing else: no well-formedness, no guard, no property of the class's
statements. Everything about the class's *sends* is supplied by
`exists_generalEntryAtSite?_of_mem_sends`, which is a fact about the environment the same call
produced.

Read together with `compileGeneralReactiveClass_error_env` this is a decision procedure: a class
compiles if and only if its environment resolves, and its environment resolves unless one of the
four causes that lemma enumerates fires. Three of those four are closed upstream by
`DTR.GeneralModel.wellFormed`, measured conjunct by conjunct in that lemma's note; the fourth,
an arity-zero external send, is the residue of finding F36 and is a real restriction rather than
a defensive branch.
-/
theorem exists_compileGeneralReactiveClass
    {classes : List DTR.GeneralReactiveClass}
    {reactiveClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    (routes : List GeneralRoute)
    (hEnv :
      outputPortEnvOf
          classes
          reactiveClass =
        .ok env) :
    ∃ reactor,
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor := by

  obtain ⟨compiledStartupReaction, hConstructor⟩ :=
    exists_compileGeneralConstructor
      env
      reactiveClass.constructor
      (by
        intro send hMember

        exact
          exists_generalEntryAtSite?_of_mem_sends
            hEnv
            (mem_externalSendsOfClass_of_mem_constructor
              hMember))

  obtain ⟨compiledMessageReactions, hMessageServers⟩ :=
    exists_compileGeneralMessageServerReactions
      env
      routes
      reactiveClass.name
      reactiveClass.messageServers
      (by
        intro server hServer send hMember

        exact
          exists_generalEntryAtSite?_of_mem_sends
            hEnv
            (mem_externalSendsOfClass_of_mem_messageServer
              hServer
              hMember))

  exact
    ⟨_,
     compileGeneralReactiveClass_ok
       hEnv
       hConstructor
       hMessageServers⟩

/--
Every class of a list whose environments all resolve compiles.

The list is a separate parameter from the class *table*, as everywhere in this file, because
`outputPortEnvOf` resolves against the table while the traversal walks the list. `compileGeneralModel`
passes the same list twice; a theorem that assumed so would not survive the first caller that
compiles a subset.
-/
theorem exists_compileGeneralReactiveClasses
    (allClasses : List DTR.GeneralReactiveClass)
    (routes : List GeneralRoute)
    (classList : List DTR.GeneralReactiveClass) :
    (∀ reactiveClass ∈ classList,
      ∃ env,
        outputPortEnvOf
            allClasses
            reactiveClass =
          .ok env) →
    ∃ compiled,
      compileGeneralReactiveClasses
          allClasses
          routes
          classList =
        .ok compiled := by

  induction classList with

  | nil =>
      intro _

      exact
        ⟨[],
         compileGeneralReactiveClasses_nil
           allClasses
           routes⟩

  | cons reactiveClass remaining inductionHypothesis =>
      intro hEnvs

      obtain ⟨env, hEnv⟩ :=
        hEnvs
          reactiveClass
          (by
            simp)

      obtain ⟨reactor, hClass⟩ :=
        exists_compileGeneralReactiveClass
          routes
          hEnv

      obtain ⟨compiledRemaining, hRemaining⟩ :=
        inductionHypothesis
          (by
            intro other hOther

            exact
              hEnvs
                other
                (by
                  rw [
                    List.mem_cons
                  ]

                  exact
                    Or.inr
                      hOther))

      exact
        ⟨_,
         compileGeneralReactiveClasses_cons_ok
           hClass
           hRemaining⟩

end Translation
end Relico
