import Relico.DTR.GeneralSyntax
import Relico.DTR.GeneralPriority
import Relico.LF.GeneralSyntax
import Relico.LF.GeneralWellFormed
import Relico.Translation.GeneralRouting
import Relico.Translation.NameGeneration

set_option autoImplicit false

namespace Relico
namespace Translation

/-!
# Stage E: translating the general DTR family into the general LF family

Everything a general DTR model contains, with no statement form left refused — a sentence that has
been **earned three times**, and the earning is the point of recording it. The first crack was
stage H's `.ifThenElse`, refused by `compileGeneralStmt` from its layer 1 until the branch machinery
existed; re-earned when that refusal was lifted. The second was stage I's `.localDecl`, refused by
S-I1 for the same reason and with the same exit, and re-earned by S-I3, which is the state this
module is in: the arm compiles, the equation lemma `compileGeneralStmt_localDecl` names it, and the
refusal text is gone. Each period of refusal was deliberate and ordered, because admitting a
construct in the guards before the translator compiles it is the shape that once made
`exists_compileGeneralBody` false. A `.send` to
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

As of stage F both levels of §III-D are closed, and this file is where the second one enters.
The route list it consumes is already sorted: `routesOf` walks `priorityOrderedInstances`, so a
receiver's port reactions come out in sending-actor priority order with ties resolved by
main-block declaration order, and that is level 1 — nothing here has to know it happened.
Level 2 is the reaction *groups*, ordered by the priority of the receiving message server, and
it enters at exactly one place: `generalPriorityOrderedMessageServers`, applied once at
`compileGeneralReactiveClass`'s single call to `compileGeneralMessageServerReactions`. The walk
itself still does not sort, and must not — it recurses on the server list, so a sort inside it
would re-sort at every step.

One entry point per level is deliberate, and finding **F60** is why. Level 1's sort sits inside
`routesOf`, which every consumer calls, so an assertion comparing two values that both read
routes cannot fail on ordering. Level 2's sits on the constructor side only, at
`compileGeneralReactiveClass`, and `generalReactionNamesOf` takes its server list as a
*parameter* — it has no order of its own, so what it reports is decided by whoever calls it.
`compileGeneralReactiveClass_reactionNames` and the fan-in ordering assertion both hand it
`generalPriorityOrderedMessageServers reactiveClass`, which is what puts the sort into the
theorem statement rather than hiding it inside the specification. The routed-model drift check
still hands it `reactiveClass.messageServers`, which is harmless there because that model
carries no priority annotation and the sort is the identity on it — and finding **F60** records
why that makes it a drift check rather than a second ordering claim.

`assembleGeneralMessageReaction_priority` records `DTR.GeneralMessageServer.priority` as a field
the emitted reaction never carries, so no later stage can wire `LF.GeneralReaction.priority`
without breaking a proof — which is the intended outcome, and more load-bearing now than before.
The printer never reads that field, so **list order is the only mechanism the target offers**, and
it is the mechanism both levels use. Reaction declaration order is observable in the target —
measured under `lfc` 0.11.0, not assumed — which is what makes ordering this list a semantic act
rather than a cosmetic one, and why it ships with the theorems that say what it achieves.

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
mirroring `wellFormed`'s ten conjuncts and returns the first that fails: §9 requires a
message that says which conjunct failed, and the decision on its own yields one bit. The
mirror can drift from what it mirrors, and rather than leave that as a silence it has a
fallback string that names its own drift, so a conjunct added upstream and not here
reports itself in the gate log instead of producing an empty complaint. G3 walked that path
deliberately rather than accidentally: its tenth conjunct and the tenth mirrored sentence
landed in one commit, so the fallback stayed unreachable. What the mirror
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
The logical action that carries one self-send **site's** message.

The parameters are the message server's, because the payload a site schedules is that message
server's parameter list; only the name distinguishes one site's action from another's, and
`generalActionNameAtSite` is the single place that name is computed, so the schedule emitted in
a body and the declaration emitted here agree by construction rather than by two functions
happening to spell the same thing.
-/
def compileGeneralMessageServerActionAtSite
    (allSelfSends : List GeneralSelfSend)
    (site : SendSite)
    (server : DTR.GeneralMessageServer) :
    LF.GeneralAction where

  name :=
    generalActionNameAtSite
      allSelfSends
      site
      server.name

  parameters :=
    server.parameters.map
      compileGeneralTypedParameter

/--
Every logical action one message server contributes: one per self-send site that targets it,
and exactly one when nothing self-sends it at all.

**The empty branch is what keeps this repair local, not a special case bolted on.** A message
server reached only from outside has no site to name an action after. `lfc` accepts a reaction
on an action nothing ever schedules — `expressions.rebeca` ships three such actions through the
real compiler today, which is measured rather than assumed — so emitting the unsuffixed action
there keeps the action list at minimum one per message server, keeps
`compileGeneralMessageServerAction` and its two equations true, and holds nine of the ten
committed positive fixtures byte-identical. Only `keep-alive`, whose two sends share one
message, gains a sibling.

**Order within a message server is site order. Order across them is not body order.** A body
that sends to two *different* message servers gets their reactions in the order the class
declares those servers, not the order the body wrote the sends, because reaction assembly is
message-server-major. F56 measured only the same-message case, which lives entirely inside one
server's group and is therefore ordered correctly here — provably so, since
`assembleGeneralMessageReactions_triggers` states which action each position in that group listens
to. The cross-server case is **F57**, recorded rather than repaired: making reaction assembly
site-major would perturb the reaction-declaration-order theorem already landed for §10.2, and F56
supplies no measurement that would justify that.

F57 is now **demoted to a recorded choice**, and it is no divergence at all — settled 2026-08-23 by
reading the paper's DTR SOS take rule, which selects on minimum arrival time **alone** and says in
prose that the order among messages of equal earliest arrival time is non-deterministically chosen.
The source specifies no order here, so emitting one cannot diverge from an order that does not exist.
That is why this paragraph says *choice* where it once said *divergence* and then *case*: same-tag
ordering across message servers is settled by message-server priority, and that is stage F's
obligation rather than a loose end of stage E.
-/
def compileGeneralMessageServerActions
    (allSelfSends : List GeneralSelfSend)
    (server : DTR.GeneralMessageServer) :
    List LF.GeneralAction :=
  match
      generalSelfSendSitesOf
        server.name
        allSelfSends with

  | [] =>
      [compileGeneralMessageServerAction
        server]

  | sites =>
      sites.map
        (fun send =>
          compileGeneralMessageServerActionAtSite
            allSelfSends
            send.site
            server)

/--
The logical actions of a whole class, message server by message server.

Hand-rolled rather than a `flatMap` over `messageServers`, for `generalSelfSendSitesOf`'s
reason: no dependence on a library name that has churned across releases, and `nil`/`cons`
equations the `logicalActions` theorems can rewrite with directly.
-/
def compileGeneralMessageServerActionsOf
    (allSelfSends : List GeneralSelfSend) :
    List DTR.GeneralMessageServer →
    List LF.GeneralAction

  | [] =>
      []

  | server :: remaining =>
      compileGeneralMessageServerActions
          allSelfSends
          server ++
        compileGeneralMessageServerActionsOf
          allSelfSends
          remaining

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

/--
A state variable's translated default is the translation of its default.

Both `initialValue` functions are identity-shaped — zero for `int`, false for `boolean` —
and `compileGeneralValue` never changes a literal, so the square commutes by case analysis
on the type. Stated because the initial valuation correspondence is exactly this square
applied once per declared variable: the source initializer builds
`DTR.GeneralType.initialValue` and the target initializer builds
`LF.GeneralType.initialValue ∘ compileGeneralType`, and without this lemma the two are two
independent computations that happen to agree today.
-/
@[simp]
theorem compileGeneralValue_initialValue
    (declaredType : DTR.GeneralType) :
    compileGeneralValue
        (DTR.GeneralType.initialValue
          declaredType) =
    LF.GeneralType.initialValue
      (compileGeneralType declaredType) := by
  cases declaredType <;> rfl

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

/- `compileGeneralStmt` and `compileGeneralBody` are mutually recursive as of stage H, because
a conditional statement carries two bodies and compiling it means compiling them. Ruling 3 of
the stage H design predicted this pair and predicted it here. A `mutual` block does not accept a
docstring, so each definition carries its own. -/
mutual

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

**The conditional arm compiles both branches and refuses only if one of them refuses.** It is
the arm that makes this function mutually recursive with `compileGeneralBody`, and the two
contexts it builds are the whole content of stage H's addressing rule: the then-branch is
compiled at `context.levelPath ++ [index, 0]` and the else-branch at
`context.levelPath ++ [index, 1]`, each from index `0`. Both are written as full record
literals rather than with `{ context with … }`, matching every other record construction in this
development, and both must stay component-identical to `externalSendsFromIndex`'s and
`selfSendsFromIndex`'s conditional arms.

Nothing in this arm is conditional on the *condition*. A branch's sends own their ports whether
or not that branch runs, which is the conservative static reading `LF.setPortNamesOfBody` and
`LF.GeneralCppPrinter.generalEffectNames` also take, and it is what keeps a port a property of
the emitted program rather than of a run. The condition itself crosses through
`compileGeneralExpr` unchanged, so a divide-by-zero inside it is governed by
`docs/decisions/0045-divide-by-zero-restriction-only.md` exactly as one anywhere else is.
-/
def compileGeneralStmt
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext)
    (index : Nat) :
    DTR.GeneralStmt →
    Except String LF.GeneralStmt

  | .assign target value =>
      .ok
        (.assign
          target
          (compileGeneralExpr value))

  | .trace tag =>
      .ok
        (.trace tag)

  | .send .selfTarget message arguments delay =>
      .ok
        (.schedule
          (generalActionNameAtSite
            context.selfSends
            {
              body :=
                context.bodyKey

              index :=
                context.levelPath ++
                  [index]
            }
            message)
          (arguments.map
            compileGeneralExpr)
          delay)

  | .send (.knownRebec rebec) message arguments _ =>
      match
          generalEntryAtSite?
            env
            {
              body :=
                context.bodyKey

              index :=
                context.levelPath ++
                  [index]
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
                    context.bodyKey

                  index :=
                    context.levelPath ++
                      [index]
                } ++
              "; every external send site is resolved by outputPortEnvOf, " ++
              "so this is a defect in the translator and not in the model")

  | .ifThenElse condition thenBody elseBody =>
      match
          compileGeneralBody
            env
            {
              bodyKey :=
                context.bodyKey

              selfSends :=
                context.selfSends

              levelPath :=
                context.levelPath ++
                  [index, 0]
            }
            0
            thenBody with

      | .error message =>
          .error message

      | .ok compiledThen =>
          match
              compileGeneralBody
                env
                {
                  bodyKey :=
                    context.bodyKey

                  selfSends :=
                    context.selfSends

                  levelPath :=
                    context.levelPath ++
                      [index, 1]
                }
                0
                elseBody with

          | .error message =>
              .error message

          | .ok compiledElse =>
              .ok
                (.ifThenElse
                  (compileGeneralExpr
                    condition)
                  compiledThen
                  compiledElse)

  | .localDecl name declaredType value =>
      .ok
        (.localDecl
          name
          (compileGeneralType
            declaredType)
          (compileGeneralExpr
            value))

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

**Stage H made the lockstep a statement about two paths rather than two numbers, and both sides
moved together.** `context.levelPath` names the body being compiled, a statement's site is
`levelPath ++ [index]`, and `compileGeneralStmt`'s conditional arm compiles the then-branch at
`levelPath ++ [index, 0]` and the else-branch at `levelPath ++ [index, 1]`, each from index `0`,
which is component for component what `externalSendsFromIndex` and `selfSendsFromIndex` do. The
hazard above is unchanged and is now worth more, not less: three traversals have to agree, and a
disagreement inside a branch is invisible to every downstream check exactly as a disagreement at
the top level was.

First refusal wins, and the diagnostic that survives is the earliest one in source order.
That is a deliberate property of a translator whose refusals name a future stage: the
message a user sees is about the first construct they wrote that this stage cannot carry.
**Inside a conditional the earliest refusal is the then-branch's**, because that arm compiles
the then-branch first, so source order still decides.
-/
def compileGeneralBody
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext) :
    Nat →
    DTR.GeneralBody →
    Except String LF.GeneralBody

  | _, [] =>
      .ok []

  | index, statement :: remaining =>
      match
          compileGeneralStmt
            env
            context
            index
            statement with

      | .error message =>
          .error message

      | .ok compiledStatement =>
          match
              compileGeneralBody
                env
                context
                (index + 1)
                remaining with

          | .error message =>
              .error message

          | .ok compiledRemaining =>
              .ok
                (compiledStatement ::
                  compiledRemaining)

end

/-- Trace instrumentation is compiled literally and never refused. -/
theorem compileGeneralStmt_trace
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext)
    (index : Nat)
    (tag : String) :
    compileGeneralStmt env context index (.trace tag) =
      .ok (.trace tag) := by

  simp [
    compileGeneralStmt
  ]

@[simp]
theorem compileGeneralBody_nil
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext)
    (index : Nat) :
    compileGeneralBody
        env
        context
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
    {context : GeneralBodyContext}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiledStatement : LF.GeneralStmt}
    {compiledRemaining : LF.GeneralBody}
    (hStatement :
      compileGeneralStmt
          env
          context
          index
          statement =
        .ok compiledStatement)
    (hRemaining :
      compileGeneralBody
          env
          context
          (index + 1)
          remaining =
        .ok compiledRemaining) :
    compileGeneralBody
        env
        context
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
    {context : GeneralBodyContext}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {message : String}
    (hStatement :
      compileGeneralStmt
          env
          context
          index
          statement =
        .error message) :
    compileGeneralBody
        env
        context
        index
        (statement :: remaining) =
      .error message := by
  simp [
    compileGeneralBody,
    hStatement
  ]

theorem compileGeneralBody_cons_error_tail
    {env : GeneralOutputPortEnv}
    {context : GeneralBodyContext}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiledStatement : LF.GeneralStmt}
    {message : String}
    (hStatement :
      compileGeneralStmt
          env
          context
          index
          statement =
        .ok compiledStatement)
    (hRemaining :
      compileGeneralBody
          env
          context
          (index + 1)
          remaining =
        .error message) :
    compileGeneralBody
        env
        context
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

`priority := none` **deliberately, and permanently**. `DTR.GeneralMessageServer.priority` may
be `some n`, and this field looks like the place to put it, but `Relico/LF/GeneralCppPrinter.lean`
never reads `LF.GeneralReaction.priority` — nothing in the emitted Lingua Franca corresponds to
it, because the target has no reaction-priority attribute. Local message-server priority is
realized in LF by reaction *declaration order* instead, the one ordering hook the target
actually provides, measured rather than assumed. Choosing that order is a sort over the
message-server list, and it is stage F's level-2 obligation (`docs/STAGE_F_DESIGN.md` §9), not a
matter of populating this field. A stage that wrote `priority := some n` here would look
finished, prove nothing, and change no emitted character.
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

/--
The reaction that runs one message server's body when **one self-send site's** action fires.

Identical to `assembleGeneralMessageReaction` except in the trigger, which names this site's
action rather than the one action the message server used to have. That single difference is
the whole of finding F56's repair on the reaction side.

**Why a reaction per site and not one reaction listing every site's action.** Measured against
`lfc` 0.11.0, recorded as F56 §14a: a reaction's trigger list is a **disjunction**, so a
reaction triggered by two actions that are both present at one tag fires **once**, and one of
the two payloads is never observed. §14b measured the working shape — one reaction per action
fires both, in reaction *declaration* order. So the sibling count here is forced by the
target's semantics, not chosen for symmetry with the action side.

**The name is deliberately shared with every sibling, and that costs nothing.** Reaction names
are checked for uniqueness nowhere, and must not be: `Relico/LF/GeneralWellFormed.lean:37`
records that LF reactions are anonymous in concrete syntax, and `renderGeneralReaction` bears
that out by printing `reaction(<trigger>)` and dropping the name entirely. What distinguishes
these siblings in the emitted text is their *triggers*, which are distinct because
`generalActionNameAtSite` gives each site its own action. Reaction names are also therefore
absent from `LF.GeneralReactor.declaredNames`, so k siblings add nothing the §9 `Nodup` guard
has to accommodate.

**`priority := none` is preserved on purpose**, for the reason spelled out on
`assembleGeneralMessageReaction` above: message-server priority is realized by reaction declaration
order, which is stage F's level-2 obligation, and the field itself is never read by the printer. A
sibling that quietly wrote `some n` here would make that obligation look discharged while changing
nothing observable.
-/
def assembleGeneralMessageReactionAtSite
    (allSelfSends : List GeneralSelfSend)
    (site : SendSite)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    LF.GeneralReaction where

  name :=
    messageReactionNameFor server.name

  trigger :=
    .logicalAction
      (generalActionNameAtSite
        allSelfSends
        site
        server.name)

  parameters :=
    server.parameters.map
      (fun parameter =>
        parameter.name)

  body :=
    compiledBody

  priority :=
    none

/--
Every action reaction one message server contributes: one per self-send site that targets it,
or the single unsuffixed reaction when nothing self-sends to it.

**The empty branch delegates to `assembleGeneralMessageReaction` rather than reconstructing
it**, which keeps that definition live and keeps all five of its `@[simp]` equations true
statements about this function's output. It also keeps the trigger in that branch spelled with
`actionNameFor`, matching what `compileGeneralMessageServerAction` puts on the action side for
the same server — the two sides have to agree per branch or the emitted reaction triggers on an
action the reactor never declares.

**Order within the server is site order, and that is a correctness property rather than a
cosmetic one.** Probe **section 15** measured that two reactions whose actions are both present at
one tag fire in reaction *declaration* order, so the order this list is built in is the order the
target executes the two bodies in — and site order is the order the sends appear in the Rebeca
body. `generalSelfSendSitesOf` preserves `selfSendsOfClass`'s order for exactly this reason.
(This cited F56 §14b until **F58**: §14b schedules and declares in the same order, so it cannot
separate declaration order from schedule order. Section 15 swaps only the declarations.)

**Order *across* message servers is not body order, and that is an unforced *choice* rather than
a thing this function gets wrong.** Reaction assembly is message-server-major — this function
is called once per server, from a caller that walks the server list — so `self.b(); self.a();`
in one body emits `a`'s reaction first whenever `a`'s message server is declared first. F56's
same-message case is entirely inside one server's group and is repaired here; the cross-server
case is recorded as **F57** and deliberately left, because repairing it means site-major
assembly, which would perturb the reaction-declaration-order theorem already landed for §10.2.

It read *divergence* here until 2026-08-23, when the paper's SOS take rule was found to select on
minimum arrival time **alone**: the source specifies no order for two messages arriving at the same
time, so there is no source order to diverge from. F57 is demoted accordingly, and message-server
priority — stage F's obligation — is what settles the order.

This sentence and its counterpart on the action side both cited that record before it existed,
which turned out to be F57's own occasion: the case had been decided and left, and a case that
has been decided reads as though it has been written down.
-/
def assembleGeneralMessageReactions
    (allSelfSends : List GeneralSelfSend)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    List LF.GeneralReaction :=
  match
      generalSelfSendSitesOf
        server.name
        allSelfSends with

  | [] =>
      [assembleGeneralMessageReaction
        server
        compiledBody]

  | sites =>
      sites.map
        (fun send =>
          assembleGeneralMessageReactionAtSite
            allSelfSends
            send.site
            server
            compiledBody)

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

/--
The reaction built for one self-send site triggers on *that site's* action.

The site-branch counterpart of `assembleGeneralMessageReaction_trigger` directly above, and the
fact that carries F56's repair down at the level of a single reaction.

It has to be stated in **triggers** rather than in names, and that is forced rather than
stylistic. Sibling reactions of one message server deliberately share a name — see the note on
`assembleGeneralMessageReactionAtSite` — so `generalMessageReactionNamesOf` returns k copies of
one identical `ReactionName`, and *no* statement in names can say which sibling listens to
which action. A names-level theorem is not merely weaker here; it is blind to the property.
That is why this is a separate theorem instead of another conjunct of
`assembleGeneralMessageReactions_names`.
-/
@[simp]
theorem assembleGeneralMessageReactionAtSite_trigger
    (allSelfSends : List GeneralSelfSend)
    (site : SendSite)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReactionAtSite
        allSelfSends
        site
        server
        compiledBody).trigger =
      .logicalAction
        (generalActionNameAtSite
          allSelfSends
          site
          server.name) := by
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

**Re-attributed by G3.** Until G3 this was an *alarm*: `LF.GeneralReaction.priority` was inert,
nothing read it, and the cheapest available guard against a later stage quietly wiring
`DTR.GeneralMessageServer.priority` through was to make that wiring break a `rfl`. G3 added
`LF.GeneralProgram.reactionPrioritiesAbsent` as the tenth conjunct of well-formedness, so a
populated priority is now a **refusal** rather than a silent no-op, and this theorem's job
changed with it: it is the message-reaction half of what discharges that conjunct for our own
output. The alarm reading still holds, and it is no longer the only thing standing there.

The scope is honest about what "discharges" means here. This is a per-reaction equation; the
conjunct is a property of a whole `LF.GeneralProgram`. Composing this theorem and its two
siblings into the program-level theorem needed the reaction-list ladder, and **that ladder has
landed**: `compileGeneralReactiveClass_prioritiesAbsent` is the reactor-granularity rung,
`assembleGeneralProgram_reactionPrioritiesAbsent` says the pre-guard assembly satisfies the
clause, and `compileGeneralModel_reactionPrioritiesAbsent` is the program-level theorem —
proved by composition, not by reading the guard's decision back. F84 recorded the debt while
it was open; the section comment above the ladder has the epistemics.
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

/--
The port-reaction half of G3's tenth conjunct — see
`assembleGeneralMessageReaction_priority` for the attribution and for the scope of "half".

Stage E's port reactions are the reactions with no source-side priority to drop in the first
place: a route has no priority field, so `none` here is not a dropped value but the absence of
one. The equation is still needed, because `reactionPrioritiesAbsent` walks every reaction of
every reactor and does not care where each came from.
-/
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

Route order is the order `routesOf` walked the main block in, which since stage F is **sending-actor
priority order, ties broken by main-block declaration order** — the level-1 sort §III-D asks for,
introduced at `priorityOrderedInstances` in `Relico/Translation/GeneralRouting.lean` rather than here,
so that this function stays a pure `map` and its order-preservation lemma stays free of priority. A
reader who knows §III-D will expect a sort; it exists, one function upstream.
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

The action reactions first — one per self-send site, in site order — then one port reaction
per incoming route, which is §7.3's order and
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
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (className : ClassName)
    (server : DTR.GeneralMessageServer) :
    Except String (List LF.GeneralReaction) :=
  match
      compileGeneralBody
        env
        { bodyKey := .messageServer server.name, selfSends := selfSends }
        0
        server.body with

  | .error message =>
      .error message

  | .ok compiledBody =>
      .ok
        (assembleGeneralMessageReactions
            selfSends
            server
            compiledBody ++
          assembleGeneralPortReactions
            className
            server
            compiledBody
            routes)

theorem compileGeneralMessageServerReactionGroup_ok
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {compiledBody : LF.GeneralBody}
    (hBody :
      compileGeneralBody
          env
          { bodyKey := .messageServer server.name, selfSends := selfSends }
          0
          server.body =
        .ok compiledBody) :
    compileGeneralMessageServerReactionGroup
        env
        selfSends
        routes
        className
        server =
      .ok
        (assembleGeneralMessageReactions
            selfSends
            server
            compiledBody ++
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
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {message : String}
    (hBody :
      compileGeneralBody
          env
          { bodyKey := .messageServer server.name, selfSends := selfSends }
          0
          server.body =
        .error message) :
    compileGeneralMessageServerReactionGroup
        env
        selfSends
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

/--
The startup-reaction half of G3's tenth conjunct — see
`assembleGeneralMessageReaction_priority` for the attribution and for the scope of "half".

This is the equation that makes the conjunct's two-part walk necessary rather than tidy:
`LF.GeneralReactor` has no single `reactions` field, so `reactionPrioritiesAbsent` checks
`startupReaction` as a field of its own and `messageReactions` as a list, and this theorem
covers the field. F50 records that split.
-/
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
    (selfSends : List GeneralSelfSend)
    (classConstructor : DTR.GeneralConstructor) :
    Except String LF.GeneralReaction :=
  match
      compileGeneralBody
        env
        { bodyKey := .constructor, selfSends := selfSends }
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
    {selfSends : List GeneralSelfSend}
    {classConstructor : DTR.GeneralConstructor}
    {compiledBody : LF.GeneralBody}
    (hBody :
      compileGeneralBody
          env
          { bodyKey := .constructor, selfSends := selfSends }
          0
          classConstructor.body =
        .ok compiledBody) :
    compileGeneralConstructor
        env
        selfSends
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
    {selfSends : List GeneralSelfSend}
    {classConstructor : DTR.GeneralConstructor}
    {message : String}
    (hBody :
      compileGeneralBody
          env
          { bodyKey := .constructor, selfSends := selfSends }
          0
          classConstructor.body =
        .error message) :
    compileGeneralConstructor
        env
        selfSends
        classConstructor =
      .error message := by
  simp [
    compileGeneralConstructor,
    hBody
  ]

/--
One class's message servers, in the order the translation walks them: **message-server priority
order, ties broken by class declaration order**.

This is stage F's level-2 mechanism and the only place it enters reaction construction.
`docs/STAGE_F_DESIGN.md` §1.1 owes Lemma 2 of the paper an ordering of one actor's reaction
*blocks* by the priority of the message server each block serves. A block is one message server's
reaction group — its action reactions, then one port reaction per route into it — and
`compileGeneralMessageServerReactions` emits those groups in the order of the list it is handed.
So ordering the list here orders the blocks, and nothing downstream has to know that priority
exists. §5 states the premise that scopes the result: this is Lemma 2's **same-actor** case, every
statement staying inside one reactor.

Ties are resolved by source declaration order because `DTR.GeneralMessageServerPriority.normalize`
is a stable sort — the convention decision `0041` fixed for equal LF microsteps, and the one level
1 already uses. An unannotated server is a priority class of its own, ordered after every explicit
one; that convention is the AST's, stated at `Relico/DTR/GeneralSyntax.lean:335-337`, not this
function's.

Carries the `general` prefix because `Translation.priorityOrderedMessageServers` is already taken,
at `Relico/Translation/MultiStoreBasic.lean:18`, by the multi-store family's sort at its own AST
type — and both live in `Relico.Translation`, so the collision would be a redeclaration rather than
an overload. Level 1's `priorityOrderedInstances` needs no prefix because no other family sorts
instances. The rule this family follows is prefix-to-disambiguate, which is also why
`selfSendsOfClass` and `outputPortEnvOf` are bare.
-/
def generalPriorityOrderedMessageServers
    (reactiveClass : DTR.GeneralReactiveClass) :
    List DTR.GeneralMessageServer :=
  DTR.GeneralMessageServerPriority.normalize
    reactiveClass.messageServers

/--
The sort changes order and nothing else, so membership transfers both ways.

This is the lemma that keeps level 2 cheap. Every side condition in this file that quantifies over
a class's message servers — "every server's sends have an entry", and the like — was proved against
`reactiveClass.messageServers`, and each one is now asked about the sorted list instead. A
permutation lemma lets those proofs go through by rewriting the membership hypothesis rather than
by re-doing the argument, which is why re-keying eight sites needed no new induction.

`@[simp]`, matching `priorityOrderedMessageServers_mem_iff` at
`Relico/Translation/MultiStoreBasic.lean:26`, so the two families discharge this obligation the
same way.
-/
@[simp]
theorem generalPriorityOrderedMessageServers_mem_iff
    (messageServer : DTR.GeneralMessageServer)
    (reactiveClass : DTR.GeneralReactiveClass) :
    messageServer ∈
        generalPriorityOrderedMessageServers
          reactiveClass ↔
      messageServer ∈
        reactiveClass.messageServers :=
  DTR.GeneralMessageServerPriority.mem_normalize_iff
    messageServer
    reactiveClass.messageServers

/--
The sort drops nothing and duplicates nothing, so the block count is the server count.

Stated because a reader checking that stage F changed *order only* should be able to see the
length claim without unfolding `normalize`, and because a sort that lost a server would emit a
reactor with a missing reaction block — a failure that reads as an ordering bug and is not one.
-/
@[simp]
theorem generalPriorityOrderedMessageServers_length
    (reactiveClass : DTR.GeneralReactiveClass) :
    (generalPriorityOrderedMessageServers
      reactiveClass).length =
      reactiveClass.messageServers.length :=
  DTR.GeneralMessageServerPriority.length_normalize
    reactiveClass.messageServers

/--
Translate every message server into its group of reactions, in the order of the list it is given.

Explicit recursion and **no sort, deliberately**. That is not the same claim it was before stage
F: level 2's message-server priority sort is real and applied, but it is applied by the caller —
`compileGeneralReactiveClass` passes `generalPriorityOrderedMessageServers reactiveClass` rather
than `reactiveClass.messageServers`. A sort *inside* this function would be wrong, not merely
redundant: it recurses on the server list, so it would re-sort at every step, and the tail's
order would be decided as many times as the list is long.

So this function is order-**preserving** rather than order-**deciding**, and every theorem about
it is stated over an arbitrary server list. That is what lets the sort be re-keyed at one call
site without re-proving anything here. `Relico/Translation/MultiStoreBasic.lean` reaches the same
place by the same route, through its own `priorityOrderedMessageServers`; the two families now
agree on message-server order and differ only in that the general family also sorts *instances*,
which is level 1 and lives in `Relico/Translation/GeneralRouting.lean`.

Groups are **appended**, not consed, which is the one structural change stage E makes to this
function. A class's reaction list is therefore its message servers in the given order with
each server's arrivals contiguous behind it, and `compileGeneralMessageServerReactions_cons_ok`
says exactly that in one `++`. `compileGeneralMessageServerReactions_append` generalizes it from
a head-and-tail split to an arbitrary one, which is the form level 2's ordering theorem consumes.
-/
def compileGeneralMessageServerReactions
    (env : GeneralOutputPortEnv)
    (selfSends : List GeneralSelfSend)
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
            selfSends
            routes
            className
            server with

      | .error message =>
          .error message

      | .ok group =>
          match
              compileGeneralMessageServerReactions
                env
                selfSends
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
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (className : ClassName) :
    compileGeneralMessageServerReactions
        env
        selfSends
        routes
        className
        [] =
      .ok [] := by
  rfl

theorem compileGeneralMessageServerReactions_cons_ok
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    {compiledRemaining : List LF.GeneralReaction}
    (hServer :
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
        .ok group)
    (hRemaining :
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          remaining =
        .ok compiledRemaining) :
    compileGeneralMessageServerReactions
        env
        selfSends
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
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {message : String}
    (hServer :
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
        .error message) :
    compileGeneralMessageServerReactions
        env
        selfSends
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
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    {message : String}
    (hServer :
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
        .ok group)
    (hRemaining :
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          remaining =
        .error message) :
    compileGeneralMessageServerReactions
        env
        selfSends
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
and stage D's `compileGeneralReactiveClass_reactionNames` was replaced rather than adjusted for
exactly that reason. A theorem of that name is live again further down this file with a
different statement, so the name resolving to something is not evidence that the stage D
version survived; the paragraph in the module header above says the same thing in the word
"replaced".

`assembleGeneralReactor_logicalActions` still pins the *action* list to source order, and the
two lists have since parted company. Reaction order is decided, by stage F's level 2. The action
list is sorted by neither level and nothing permutes it, because level 2's sort is applied to the
server list handed to `compileGeneralMessageServerReactions` and this field is built from
`reactiveClass.messageServers` directly. Whether action declaration order is observable in the
target has not been measured — reaction declaration order has been, under `lfc` 0.11.0 — so this
theorem pins source order as a fact about the translation and claims nothing about its effect.
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
    compileGeneralMessageServerActionsOf
      (selfSendsOfClass
        reactiveClass)
      reactiveClass.messageServers

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

/--
The reactor's logical actions are the per-site action lists of its message servers, concatenated
in message-server order.

**The previous form of this theorem said `reactiveClass.messageServers.map
compileGeneralMessageServerAction`, and that statement is now false rather than merely
unproven.** A message server with two self-send sites contributes two actions, so the lists
differ in *length* as soon as any class self-sends the same message twice — `keep-alive.rebeca`
is the committed fixture that witnesses it. The `map` form survives exactly on the classes where
every message server has at most one site, which is nine of the ten positive fixtures, and that
is why the old statement went green for as long as it did.
-/
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
      compileGeneralMessageServerActionsOf
        (selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers := by
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
            (selfSendsOfClass reactiveClass)
            reactiveClass.constructor with

      | .error message =>
          .error message

      | .ok compiledStartupReaction =>
          match
              compileGeneralMessageServerReactions
                env
                (selfSendsOfClass reactiveClass)
                routes
                reactiveClass.name
                (generalPriorityOrderedMessageServers
                  reactiveClass) with

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
          (selfSendsOfClass reactiveClass)
          reactiveClass.constructor =
        .ok compiledStartupReaction)
    (hMessageServers :
      compileGeneralMessageServerReactions
          env
          (selfSendsOfClass reactiveClass)
          routes
          reactiveClass.name
          (generalPriorityOrderedMessageServers
            reactiveClass) =
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
          (selfSendsOfClass reactiveClass)
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
          (selfSendsOfClass reactiveClass)
          reactiveClass.constructor =
        .ok compiledStartupReaction)
    (hMessageServers :
      compileGeneralMessageServerReactions
          env
          (selfSendsOfClass reactiveClass)
          routes
          reactiveClass.name
          (generalPriorityOrderedMessageServers
            reactiveClass) =
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
design tension in that: the ten clauses live in `Relico/LF/GeneralWellFormed.lean` and none
of them carries prose fit for a diagnostic. The resolution below is a **mirror** — a list
pairing each clause with a sentence — and the mirror is used for the refusal *text only*. The
decision itself is made on `LF.GeneralProgram.wellFormed`, never on the mirror.

That split is deliberate and was the second design considered, not the first. A guard that
decided on an `Option String` diagnostic built from the mirror would need
`diagnostic program = none ↔ program.wellFormed = true` as its anti-drift tripwire, and that
biconditional unfolds into a one-thousand-and-twenty-four-leaf case split over ten independent
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
sight. Ten entries, the tenth added by G3 in the same commit as the conjunct it mirrors; if
`Relico/LF/GeneralWellFormed.lean` gains an eleventh conjunct, this list does not, and
`generalProgramExplanation`'s fallback is what says so.

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
    ),
    (
      "some reaction carries a priority, which Lingua Franca has no way to express: `lfc "
        ++ "0.11.0` rejects a reaction attribute named `priority` outright, and precedence "
        ++ "between the reactions of one reactor is given by their declaration order instead",
      LF.GeneralProgram.reactionPrioritiesAbsent
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
    {context : GeneralBodyContext}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiled : LF.GeneralBody}
    (hCompiled :
      compileGeneralBody
          env
          context
          index
          (statement :: remaining) =
        .ok compiled) :
    ∃ compiledStatement compiledRemaining,
      compileGeneralStmt
          env
          context
          index
          statement =
          .ok compiledStatement ∧
        compileGeneralBody
            env
            context
            (index + 1)
            remaining =
            .ok compiledRemaining ∧
          compiled =
            compiledStatement ::
              compiledRemaining := by

  cases hStatement :
      compileGeneralStmt
        env
        context
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
            context
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
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
        .ok group) :
    ∃ compiledBody,
      compileGeneralBody
          env
          { bodyKey := .messageServer server.name, selfSends := selfSends }
          0
          server.body =
          .ok compiledBody ∧
        group =
          assembleGeneralMessageReactions
              selfSends
              server
              compiledBody ++
            assembleGeneralPortReactions
              className
              server
              compiledBody
              routes := by

  cases hBody :
      compileGeneralBody
        env
        { bodyKey := .messageServer server.name, selfSends := selfSends }
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
    {selfSends : List GeneralSelfSend}
    {classConstructor : DTR.GeneralConstructor}
    {reaction : LF.GeneralReaction}
    (hCompiled :
      compileGeneralConstructor
          env
          selfSends
          classConstructor =
        .ok reaction) :
    ∃ compiledBody,
      compileGeneralBody
          env
          { bodyKey := .constructor, selfSends := selfSends }
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
        { bodyKey := .constructor, selfSends := selfSends }
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
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {compiled : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactions
          env
          selfSends
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
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {remaining : List DTR.GeneralMessageServer}
    {compiled : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          (server :: remaining) =
        .ok compiled) :
    ∃ group compiledRemaining,
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
          .ok group ∧
        compileGeneralMessageServerReactions
            env
            selfSends
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
        selfSends
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
            selfSends
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
Compiling a split server list concatenates the two compiled reaction lists.

Stated with the two *varying* quantifiers inside the conclusion rather than as hypotheses of the
theorem, which is the shape `routesOfInstances_append_aux` in
`Relico/Translation/GeneralRouting.lean` uses and for the same reason: the induction is on
`earlier`, `compiledEarlier` has to vary with it, and putting both under a `∀` in the goal avoids
`induction … generalizing` and leaves the induction hypothesis in an unambiguous shape. `later`
and `compiledLater` are fixed throughout and stay as parameters.

The two inversion lemmas above are why this needs no unfolding of its own: the nil case reads the
compiled list off `eq_nil_of_compileGeneralMessageServerReactions_nil_ok` and the cons case off
`exists_of_compileGeneralMessageServerReactions_cons_ok`, so the recursion is inverted in exactly
one place in this file and this proof consumes that inversion rather than repeating it. That is
also why this declaration sits here, below both inverters, rather than beside the `_cons_ok`
lemma it generalizes.
-/
private theorem compileGeneralMessageServerReactions_append_aux
    (env : GeneralOutputPortEnv)
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (className : ClassName)
    (later : List DTR.GeneralMessageServer)
    (compiledLater : List LF.GeneralReaction)
    (hLater :
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          later =
        .ok compiledLater) :
    ∀ (earlier : List DTR.GeneralMessageServer)
      (compiledEarlier : List LF.GeneralReaction),
      compileGeneralMessageServerReactions
            env
            selfSends
            routes
            className
            earlier =
          .ok compiledEarlier →
        compileGeneralMessageServerReactions
            env
            selfSends
            routes
            className
            (earlier ++ later) =
          .ok
            (compiledEarlier ++
              compiledLater) := by

  intro earlier

  induction earlier with

  | nil =>
      intro compiledEarlier hEarlier

      have hEmpty :
          compiledEarlier = [] :=
        eq_nil_of_compileGeneralMessageServerReactions_nil_ok
          hEarlier

      subst hEmpty

      simpa using hLater

  | cons server remaining inductionHypothesis =>
      intro compiledEarlier hEarlier

      obtain
          ⟨group,
            compiledRemaining,
            hServer,
            hRemaining,
            hSplit⟩ :=
        exists_of_compileGeneralMessageServerReactions_cons_ok
          hEarlier

      subst hSplit

      rw [
        List.cons_append,
        List.append_assoc
      ]

      exact
        compileGeneralMessageServerReactions_cons_ok
          hServer
          (inductionHypothesis
            compiledRemaining
            hRemaining)

/--
A class's reaction list splits where its server list splits, in order.

This is the order claim at the level of one class's reactions: no interleaving, no re-sorting, and
the cut point is **arbitrary**, so it holds between any earlier server and any later one rather
than only at the head of the list. `compileGeneralMessageServerReactions_cons_ok` is this statement
at a head-and-tail split; level 2's ordering theorem needs the arbitrary one, because it speaks
about a cut in message-server *priority* order and nothing distinguishes the first element of a
sorted list.

"No re-sorting" is a statement about this recursion, which walks whatever list it is handed. The
sort lives one level up, in `compileGeneralReactiveClass`, which hands it
`generalPriorityOrderedMessageServers reactiveClass` rather than `reactiveClass.messageServers` —
so a cut this theorem takes a hypothesis about is a cut in priority order whenever the list it is
given came from there. `routesOfInstances_append` in `Relico/Translation/GeneralRouting.lean` is
the level-1 counterpart, proved the same way for the same reason.

Binders are implicit here where the level-1 counterpart's are explicit. Every one of them is
determined by the two hypotheses, and this theorem is the generalization of
`compileGeneralMessageServerReactions_cons_ok`, whose binders are implicit; matching its immediate
neighbour matters more than matching the other family.
-/
theorem compileGeneralMessageServerReactions_append
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {earlier later : List DTR.GeneralMessageServer}
    {compiledEarlier compiledLater : List LF.GeneralReaction}
    (hEarlier :
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          earlier =
        .ok compiledEarlier)
    (hLater :
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          later =
        .ok compiledLater) :
    compileGeneralMessageServerReactions
        env
        selfSends
        routes
        className
        (earlier ++ later) =
      .ok
        (compiledEarlier ++
          compiledLater) :=
  compileGeneralMessageServerReactions_append_aux
    env
    selfSends
    routes
    className
    later
    compiledLater
    hLater
    earlier
    compiledEarlier
    hEarlier

/-!
### Route membership — the message-name ↔ event-kind bridge's translation half

Task `#129`'s bridge has two halves. The target half lives in `Relico/LF/GeneralSemantics.lean`:
`LF.findReactionForKind?_ne_none_of_mem` turns *membership plus a match* into *being found*, and
`LF.GeneralProgram.reactionFor?_eq_findReactionForKind?_of_reactorOfInstance?` composes that with
instance resolution. This block is the translation half, and it answers the question the C7 audit
found no existing theorem answering: **is the reaction a source message's send compiled to
actually present in the compiled reactor's reaction list?** For both routes the answer is a
construction theorem — not a naming-convention argument — because both routes build the reaction
and the list from one traversal, and these lemmas invert that traversal.

The route shapes, once each:

* **Action route** (a self-send): `send .selfTarget m …` compiles to `.schedule (generalActionNameAtSite selfSends site m) …` (`compileGeneralStmt_send_selfTarget`), and the receiving server's group emits one `.logicalAction` reaction per self-send site (`assembleGeneralMessageReactionAtSite`, trigger pinned by `assembleGeneralMessageReactionAtSite_trigger`).
* **Port route** (an external send): `send (.knownRebec r) m …` compiles to `.setPort entry.outputPort …` (`compileGeneralStmt_send_knownRebec_ok`), and every route into the server emits one `.inputPort` reaction whose port is `generalInputPortOfRoute route` (`assembleGeneralPortReaction`, trigger pinned by `assembleGeneralPortReaction_trigger`).
-/

/--
One server's compiled group is present, as a block, in any compiled list over a server list
containing that server.

The membership engine both route theorems run on. Two obligations in one induction: the server's
group really did compile (the error case is impossible, because a list whose walk returned `.ok`
cannot contain a server whose group errored — each cons step of the walk propagates the error),
and every reaction of that group is a member of the compiled list, by `List.mem_append` at each
cons step.

Kept `private` because no consumer needs the block shape — both public theorems below project a
single reaction out of the block — and public surface should be the two routes, not the walker.
-/
private theorem mem_of_compileGeneralMessageServerReactions
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer} :
    ∀ (servers : List DTR.GeneralMessageServer)
      (compiled : List LF.GeneralReaction),
      server ∈ servers →
        compileGeneralMessageServerReactions
            env
            selfSends
            routes
            className
            servers =
          .ok compiled →
        ∃ group : List LF.GeneralReaction,
          compileGeneralMessageServerReactionGroup
              env
              selfSends
              routes
              className
              server =
            .ok group ∧
          group ⊆ compiled := by

  intro servers
  induction servers with

  | nil =>
      intro compiled hMember

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro compiled hMember hCompiled

      rcases
          exists_of_compileGeneralMessageServerReactions_cons_ok
            hCompiled with
        ⟨
          headGroup,
          compiledRemaining,
          hHeadGroup,
          hRemaining,
          hCompiledEq
        ⟩

      subst hCompiledEq

      cases hMemberSplit : List.mem_cons.mp hMember with

      | inl hHead =>
          subst hHead

          exact
            ⟨
              headGroup,
              hHeadGroup,
              fun reaction hReaction =>
                List.mem_append.mpr
                  (Or.inl hReaction)
            ⟩

      | inr hTail =>
          rcases
              inductionHypothesis
                compiledRemaining
                hTail
                hRemaining with
            ⟨
              tailGroup,
              hTailGroup,
              hTailSubset
            ⟩

          exact
            ⟨
              tailGroup,
              hTailGroup,
              fun reaction hReaction =>
                List.mem_append.mpr
                  (Or.inr
                    (hTailSubset
                      hReaction))
            ⟩

/--
The reaction a self-send site compiles to is present in the compiled reactor's reaction list —
the **action route** of the message-name ↔ event-kind bridge.

Given a class that compiled to a reactor, a message server of that class (in declaration order —
`generalPriorityOrderedMessageServers_mem_iff` transfers from the sorted list the compilation
actually walked), and a self-send site of that class targeting the server's message, the theorem
produces the **compiled body** of the server and pins the member reaction completely: it triggers
on exactly that site's logical action, runs that compiled body, and has the server's parameter
names. Every conjunct is the corresponding `rfl`-equation or inversion already in this file; the
theorem's contribution is putting them behind one membership fact a consumer can rewrite with.

The trigger conjunct is the load-bearing one for `#129`: with it,
`LF.GeneralTrigger.matchesKind` decides the match on `.logicalAction`, and
`LF.findReactionForKind?_ne_none_of_mem` (plus instance resolution) turns membership-plus-match
into `reactionFor? = some …` — which is exactly the missing event-kind half of
`Correctness.GeneralConsumeMatch`'s deliberate omission.

The body is bound existentially rather than fixed by a premise, because a consumer holding only
the class and the site has no way to name the body, and requiring it to would push a
`compileGeneralBody` inversion into every caller. The theorem owns that inversion here, once.
-/
theorem compileGeneralReactiveClass_actionRoute_mem
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (server : DTR.GeneralMessageServer)
    (hServer :
      server ∈ reactiveClass.messageServers)
    (selfSend : GeneralSelfSend)
    (hSelfSend :
      selfSend ∈
        generalSelfSendSitesOf
          server.name
          (selfSendsOfClass reactiveClass)) :
    ∃ compiledBody : LF.GeneralBody,
      (
        {
          name :=
            messageReactionNameFor
              server.name

          trigger :=
            .logicalAction
              (generalActionNameAtSite
                (selfSendsOfClass reactiveClass)
                selfSend.site
                server.name)

          parameters :=
            server.parameters.map
              (fun parameter =>
                parameter.name)

          body :=
            compiledBody

          priority :=
            none
        } :
          LF.GeneralReaction
      ) ∈
        reactor.messageReactions ∧
      ∃ env : GeneralOutputPortEnv,
        outputPortEnvOf
            classes
            reactiveClass =
          .ok env ∧
        compileGeneralBody
            env
            { bodyKey := .messageServer server.name,
              selfSends :=
                selfSendsOfClass reactiveClass }
            0
            server.body =
          .ok compiledBody := by
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
            (selfSendsOfClass reactiveClass)
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
                (selfSendsOfClass reactiveClass)
                routes
                reactiveClass.name
                (generalPriorityOrderedMessageServers
                  reactiveClass) with

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

              injection hCompiled with hReactorEq

              subst hReactorEq

              have hSortedServer :
                  server ∈
                    generalPriorityOrderedMessageServers
                      reactiveClass :=
                (generalPriorityOrderedMessageServers_mem_iff
                  server
                  reactiveClass).mpr
                  hServer

              rcases
                  mem_of_compileGeneralMessageServerReactions
                    (generalPriorityOrderedMessageServers
                      reactiveClass)
                    compiledMessageReactions
                    hSortedServer
                    hMessageServers with
                ⟨
                  group,
                  hGroup,
                  hGroupSubset
                ⟩

              rcases
                  exists_of_compileGeneralMessageServerReactionGroup_ok
                    hGroup with
                  ⟨
                    compiledBody,
                    hBody,
                    hGroupEq
                  ⟩

              subst hGroupEq

              refine
                ⟨
                  compiledBody,
                  ?_,
                  env,
                  rfl,
                  hBody
                ⟩

              refine
                hGroupSubset
                  (show
                      ({
                        name :=
                          messageReactionNameFor
                            server.name

                        trigger :=
                          .logicalAction
                            (generalActionNameAtSite
                              (selfSendsOfClass reactiveClass)
                              selfSend.site
                              server.name)

                        parameters :=
                          server.parameters.map
                            (fun parameter =>
                              parameter.name)

                        body :=
                          compiledBody

                        priority :=
                          none
                      } :
                          LF.GeneralReaction
                      ) ∈
                        (assembleGeneralMessageReactions
                            (selfSendsOfClass reactiveClass)
                            server
                            compiledBody ++
                          assembleGeneralPortReactions
                            reactiveClass.name
                            server
                            compiledBody
                            routes)
                    from
                      ?_)

              cases hSites :
                  generalSelfSendSitesOf
                    server.name
                    (selfSendsOfClass reactiveClass) with

              | nil =>
                  exact absurd
                    hSelfSend
                    (by
                      rw [hSites]

                      simp)

              | cons siteHead siteTail =>
                  refine
                    List.mem_append.mpr
                      (Or.inl ?_)

                  rw [hSites] at hSelfSend

                  simp only [
                    assembleGeneralMessageReactions,
                    hSites
                  ]

                  exact
                    List.mem_map_of_mem
                      hSelfSend

/--
The reaction an external route compiles to is present in the compiled reactor's reaction list —
the **port route** of the message-name ↔ event-kind bridge.

Given a class that compiled to a reactor, a message server of that class, and a route into that
server, the theorem produces the server's compiled body and pins the member reaction completely:
it triggers on exactly `generalInputPortOfRoute route` — the input port the connection emitted,
the same name `compileGeneralStmt_send_knownRebec_ok`'s output-port entry feeds — runs that
compiled body, and has the server's parameter names.

The route hypothesis is membership in the **whole model's** route list, filtered to routes into
this server of this class — the shape `assembleGeneralPortReactions` consumes — so a consumer
holding a route need not prove it survives any per-class projection first. Which routes are in
the list is decided by `generalRoutesIntoMessageServer`'s filter on `(receiverClass, message)`,
unchanged here.
-/
theorem compileGeneralReactiveClass_portRoute_mem
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (server : DTR.GeneralMessageServer)
    (hServer :
      server ∈ reactiveClass.messageServers)
    (route : GeneralRoute)
    (hRoute :
      route ∈
        generalRoutesIntoMessageServer
          reactiveClass.name
          server.name
          routes) :
    ∃ compiledBody : LF.GeneralBody,
      (
        {
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
        } :
          LF.GeneralReaction
      ) ∈
        reactor.messageReactions ∧
      ∃ env : GeneralOutputPortEnv,
        outputPortEnvOf
            classes
            reactiveClass =
          .ok env ∧
        compileGeneralBody
            env
            { bodyKey := .messageServer server.name,
              selfSends :=
                selfSendsOfClass reactiveClass }
            0
            server.body =
          .ok compiledBody := by
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
            (selfSendsOfClass reactiveClass)
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
                (selfSendsOfClass reactiveClass)
                routes
                reactiveClass.name
                (generalPriorityOrderedMessageServers
                  reactiveClass) with

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

              injection hCompiled with hReactorEq

              subst hReactorEq

              have hSortedServer :
                  server ∈
                    generalPriorityOrderedMessageServers
                      reactiveClass :=
                (generalPriorityOrderedMessageServers_mem_iff
                  server
                  reactiveClass).mpr
                  hServer

              rcases
                  mem_of_compileGeneralMessageServerReactions
                    (generalPriorityOrderedMessageServers
                      reactiveClass)
                    compiledMessageReactions
                    hSortedServer
                    hMessageServers with
                ⟨
                  group,
                  hGroup,
                  hGroupSubset
                ⟩

              rcases
                  exists_of_compileGeneralMessageServerReactionGroup_ok
                    hGroup with
                  ⟨
                    compiledBody,
                    hBody,
                    hGroupEq
                  ⟩

              subst hGroupEq

              refine
                ⟨
                  compiledBody,
                  ?_,
                  env,
                  rfl,
                  hBody
                ⟩

              refine
                hGroupSubset
                  (show
                      ({
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
                      } :
                          LF.GeneralReaction
                      ) ∈
                        (assembleGeneralMessageReactions
                            (selfSendsOfClass reactiveClass)
                            server
                            compiledBody ++
                          assembleGeneralPortReactions
                            reactiveClass.name
                            server
                            compiledBody
                            routes)
                    from
                      ?_)

              refine
                List.mem_append.mpr
                  (Or.inr ?_)

              rw [
                assembleGeneralPortReactions
              ]

              exact
                List.mem_map_of_mem
                  hRoute

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
            (selfSendsOfClass reactiveClass)
            reactiveClass.constructor =
            .ok compiledStartupReaction ∧
          compileGeneralMessageServerReactions
              env
              (selfSendsOfClass reactiveClass)
              routes
              reactiveClass.name
              (generalPriorityOrderedMessageServers
                reactiveClass) =
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
            (selfSendsOfClass reactiveClass)
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
                (selfSendsOfClass reactiveClass)
                routes
                reactiveClass.name
                (generalPriorityOrderedMessageServers
                  reactiveClass) with

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
A compiled reactor's startup reaction body is a successful compilation of its class's constructor body.

The shape a state initializer on the target side needs: the body an initial `LF.GeneralReactorRuntime`
receives is not an arbitrary list of statements but exactly the compiled constructor body, under the port
environment and self-send list the reactor itself was compiled against. The existential is not slack —
`outputPortEnvOf` and `selfSendsOfClass` are functions of the class, and the pair only introduces names
for them, following `compileGeneralReactiveClass_outputPorts`' convention for the same situation.
-/
theorem compileGeneralReactiveClass_startupBody
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
    ∃ env compiledBody,
      outputPortEnvOf
          classes
          reactiveClass =
          .ok env ∧
        compileGeneralBody
            env
            { bodyKey := .constructor,
              selfSends :=
                selfSendsOfClass reactiveClass }
            0
            reactiveClass.constructor.body =
          .ok compiledBody ∧
        reactor.startupReaction.body =
          compiledBody := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      env,
      compiledStartupReaction,
      _,
      hEnv,
      hConstructor,
      _,
      hReactor
    ⟩

  subst hReactor

  rcases
      exists_of_compileGeneralConstructor_ok
        hConstructor with
    ⟨
      compiledBody,
      hBody,
      hStartupReaction
    ⟩

  exact
    ⟨
      env,
      compiledBody,
      hEnv,
      hBody,
      by
        rw [
          assembleGeneralReactor_startupReaction,
          hStartupReaction,
          assembleGeneralStartupReaction_body
        ]
    ⟩

/--
A compiled reactor's state variables are the translations of its class's, in declaration order.
-/
theorem compileGeneralReactiveClass_stateVariables
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
    reactor.stateVariables =
      reactiveClass.stateVariables.map
        compileGeneralStateVariableDecl := by

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
A compiled reactor's parameters are the translations of its class's constructor parameters, in
declaration order.
-/
theorem compileGeneralReactiveClass_parameters
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
    reactor.parameters =
      reactiveClass.constructor.parameters.map
        compileGeneralTypedParameter := by

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
On a list whose image has no duplicates, an injective function's preimage list has no duplicates
either.

Public because the initial correspondence needs it in exactly one place — deriving that a compiled
program's duplicate-free reactor names mean the model's class names were duplicate-free — and a second
private copy in another module would be the duplication this repository prefers to avoid. Hand-rolled
because this development depends on Lean core alone.
-/
theorem nodup_of_nodup_map_injective
    {α β : Type}
    (function : α → β) :
    ∀ (values : List α),
      (values.map function).Nodup →
        Function.Injective function →
          values.Nodup := by

  intro values
  induction values with

  | nil =>
      simp

  | cons head remaining inductionHypothesis =>
      intro hNodup hInjective

      refine
        List.nodup_cons.mpr
          ⟨
            ?_,
            inductionHypothesis
              (List.nodup_cons.mp hNodup).2
              hInjective
          ⟩

      intro hMember

      have hMapped :
          function head ∈
            remaining.map function :=
        List.mem_map_of_mem hMember

      exact
        (List.nodup_cons.mp hNodup).1
          hMapped

/--
Every reactor of a compiled class list comes from a class of that list, with the startup body and state
variables that class compiled to.

The membership companion of `compileGeneralReactiveClasses_ports`, answering the question that one
cannot: which **class** produced this reactor? The answer is the witness the initial correspondence
needs — it walks a compiled program's reactors and must, for each, name the source class whose
constructor parameters and state variables the initial states on the two sides were built from.

`allClasses` and `classes` are again independently quantified, for the same reason as
`compileGeneralReactiveClasses_ports`: `compileGeneralModel` instantiates both to `model.classes`, and
no consumer needs them related.

On a compiled class list whose class names are distinct — which every compiled *program* guarantees
through `reactorNamesUnique`, `compileGeneralModel_reactorNames` and
`Translation.reactorNameFor_injective` — the witness class is unique, but uniqueness is deliberately
not concluded here: no consumer needs it, and a uniqueness clause would force every caller to carry a
`Nodup` hypothesis through the membership walk.
-/
theorem compileGeneralReactiveClasses_startupBody :
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
            ∃ reactiveClass env compiledBody,
              reactiveClass ∈ classes ∧
                compileGeneralReactiveClass
                    allClasses
                    routes
                    reactiveClass =
                    .ok reactor ∧
                  outputPortEnvOf
                      allClasses
                      reactiveClass =
                      .ok env ∧
                compileGeneralBody
                    env
                    { bodyKey := .constructor,
                      selfSends :=
                        selfSendsOfClass reactiveClass }
                    0
                    reactiveClass.constructor.body =
                    .ok compiledBody ∧
                  reactor.startupReaction.body =
                    compiledBody ∧
                reactor.stateVariables =
                    reactiveClass.stateVariables.map
                      compileGeneralStateVariableDecl ∧
              reactor.parameters =
                  reactiveClass.constructor.parameters.map
                    compileGeneralTypedParameter := by

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
              compileGeneralReactiveClass_startupBody
                hClass with
            ⟨
              env,
              compiledBody,
              hEnv,
              hBody,
              hStartupBody
            ⟩

          exact
            ⟨
              reactiveClass,
              env,
              compiledBody,
              List.mem_cons.mpr
                (Or.inl rfl),
              hClass,
              hEnv,
              hBody,
              hStartupBody,
              compileGeneralReactiveClass_stateVariables
                hClass,
              compileGeneralReactiveClass_parameters
                hClass
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
              compiledBody,
              hWitnessMember,
              hWitnessClass,
              hEnv,
              hBody,
              hStartupBody,
              hStateVariables,
              hParameters
            ⟩

          exact
            ⟨
              witnessClass,
              env,
              compiledBody,
              List.mem_cons.mpr
                (Or.inr hWitnessMember),
              hWitnessClass,
              hEnv,
              hBody,
              hStartupBody,
              hStateVariables,
              hParameters
            ⟩

/--
A compiled program's connections are the routing projection of the model's routes.

The theorem stage E had to break, in its replacement form. It is still `rfl` under the
assembler and the guard, and that remains the point of routing the program through a total
assembler: the connection list is a property of a function with no failure case, so no branch
of the partial layer can quietly add or drop a connection, and the guard — which is the only
thing between the assembler and the caller — is transparent to shape.

One connection per route, in `routesOf`'s order, which since stage F is sending-actor priority order
with ties broken by main-block declaration order. That is a stronger statement than the empty list ever
was, and it is what the target gate's *"three connections on one `Gateway`"* assertion checks from the
outside. Connection order in the emitted text therefore moves when a priority annotation moves, which is
intended: it is the observable trace of the level-1 sort.
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
Every reactor of a compiled program comes from a class of the model, with that class's compiled startup
body and state variables.

The program-level form of `compileGeneralReactiveClasses_startupBody`, shaped like
`compileGeneralModel_ports` — the routes existentially bound, because they are recovered from the
compilation rather than named in the theorem's head — and it is the theorem the initial
correspondence consumes: given a reactor of a successfully compiled program it names the source class
behind it, the successful compilation of that class, the port environment the startup body was compiled
under, the compiled constructor body itself, and the translated state-variable list — everything an
initial-state argument needs to line one side's constructor entry up against the other's.
-/
theorem compileGeneralModel_startupBody
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
            ∃ reactiveClass env compiledBody,
              reactiveClass ∈ model.classes ∧
                compileGeneralReactiveClass
                    model.classes
                    routes
                    reactiveClass =
                    .ok reactor ∧
                  outputPortEnvOf
                      model.classes
                      reactiveClass =
                      .ok env ∧
                compileGeneralBody
                    env
                    { bodyKey := .constructor,
                      selfSends :=
                        selfSendsOfClass reactiveClass }
                    0
                    reactiveClass.constructor.body =
                    .ok compiledBody ∧
                  reactor.startupReaction.body =
                      compiledBody ∧
                reactor.stateVariables =
                    reactiveClass.stateVariables.map
                      compileGeneralStateVariableDecl ∧
              reactor.parameters =
                  reactiveClass.constructor.parameters.map
                    compileGeneralTypedParameter := by

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
    compileGeneralReactiveClasses_startupBody
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
declarations swaps their same-tag execution order — so the priority work is a permutation
of `messageReactions`. This block was written during stage D and attributed that permutation
to stage G. Stage F did it instead, at both levels, and the attribution is corrected here
rather than deleted because the *argument* was right and is what the sort was eventually
re-keyed against: proving that the order **is** source order gave the permutation a fixed
starting point to move away from, and turned any accidental reordering in between into a
failing proof rather than a silent behavioural change.

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
that a group's port reactions follow the route order, and that groups appear in the order of
whatever server list the theorem names. That third clause is where stage F entered, and it is
why the wording here is no longer "source order": the list the class-level theorem names is now
`generalPriorityOrderedMessageServers reactiveClass`, so it pins message-server **priority**
order. Level 1 decides the second clause, by sorting instances inside `routesOf` so that route
order is sending-actor priority order; level 2 decides the third. The fan-in ordering assertion
is the runnable form of both, and neither clause subsumes the other.

`List.flatMap` was the obvious alternative spelling and is deliberately avoided: its core name
has churned in the same family as `List.enum` and `String.capitalize`, and this development
depends on no such function. An explicit recursive specification costs nine lines and cannot
churn.
-/

/--
The action names one message server contributes, in declaration order.

The action-side counterpart of `generalMessageReactionNamesOf`, and the one place the two sides
visibly differ: reaction siblings all share a name, while action siblings must **not**, because
action names are declared identifiers and `LF.GeneralReactor.declaredNames` has to stay `Nodup`.
That asymmetry is not a style choice — it follows from `renderGeneralReaction` dropping reaction
names and the printer emitting action names.

The zero-site branch spells the name with `actionNameFor` rather than `generalActionNameAtSite`,
matching what `compileGeneralMessageServerActions` emits in the same branch. The two agree
per branch or the reaction triggers on an action the reactor never declares.
-/
def generalMessageActionNamesOf
    (allSelfSends : List GeneralSelfSend)
    (message : MsgName) :
    List ActionName :=
  match
      generalSelfSendSitesOf
        message
        allSelfSends with

  | [] =>
      [actionNameFor message]

  | sites =>
      sites.map
        (fun send =>
          generalActionNameAtSite
            allSelfSends
            send.site
            message)

/--
Deriving one message server's actions produces exactly the names the specification predicts.
-/
@[simp]
theorem compileGeneralMessageServerActions_names
    (allSelfSends : List GeneralSelfSend)
    (server : DTR.GeneralMessageServer) :
    (compileGeneralMessageServerActions
          allSelfSends
          server).map
        (fun action =>
          action.name) =
      generalMessageActionNamesOf
        allSelfSends
        server.name := by

  cases hSites :
      generalSelfSendSitesOf
        server.name
        allSelfSends with

  | nil =>
      simp [
        compileGeneralMessageServerActions,
        generalMessageActionNamesOf,
        compileGeneralMessageServerAction,
        hSites
      ]

  | cons firstSite remainingSites =>
      simp [
        compileGeneralMessageServerActions,
        generalMessageActionNamesOf,
        compileGeneralMessageServerActionAtSite,
        hSites
      ]

/--
The action names one class contributes, in declaration order.

Concatenation rather than `::` for the same reason `generalReactionNamesOf` concatenates: a
message server contributes a *list*, whose length is its self-send site count, so no
cons-shaped specification can state this.
-/
def generalActionNamesOf
    (allSelfSends : List GeneralSelfSend) :
    List DTR.GeneralMessageServer →
    List ActionName

  | [] =>
      []

  | server :: remaining =>
      generalMessageActionNamesOf
          allSelfSends
          server.name ++
        generalActionNamesOf
          allSelfSends
          remaining

/--
Deriving the actions of a message-server list preserves names and order.

**This replaced a theorem stating `servers.map compileGeneralMessageServerAction`, whose
right-hand side was `servers.map (fun server => actionNameFor server.name)`.** That statement was
true of the function it named and stopped being true of the reactor, because
`assembleGeneralReactor` no longer builds its action list with `map`. The length mismatch is
the same one §7.3 forced on the reaction side one stage earlier, arriving from a different
direction: there it was external senders multiplying reactions, here it is self-send sites
multiplying actions.
-/
theorem compileGeneralMessageServerActionsOf_names :
    ∀ (allSelfSends : List GeneralSelfSend)
      (servers : List DTR.GeneralMessageServer),
      (compileGeneralMessageServerActionsOf
            allSelfSends
            servers).map
          (fun action =>
            action.name) =
        generalActionNamesOf
          allSelfSends
          servers := by

  intro allSelfSends servers
  induction servers with

  | nil =>
      rfl

  | cons server remaining inductionHypothesis =>
      simp [
        compileGeneralMessageServerActionsOf,
        generalActionNamesOf,
        List.map_append,
        compileGeneralMessageServerActions_names,
        inductionHypothesis
      ]

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
The reaction names one message server contributes through its **own** actions, in declaration
order.

One name per self-send site, or the single name when nothing self-sends to this server. Every
entry is the same string, and that is the point rather than a shortcut: siblings differ in their
*triggers*, not their names, because reaction names are dropped by `renderGeneralReaction` and
checked for uniqueness nowhere. So what this specification pins is the **count** and the
**position** of the action reactions within the group, which is exactly what F56 got wrong — the
old shape had one where the target needs k.
-/
def generalMessageReactionNamesOf
    (allSelfSends : List GeneralSelfSend)
    (message : MsgName) :
    List ReactionName :=
  match
      generalSelfSendSitesOf
        message
        allSelfSends with

  | [] =>
      [messageReactionNameFor message]

  | sites =>
      sites.map
        (fun _ =>
          messageReactionNameFor message)

/--
Assembling a message server's action reactions produces exactly the names the specification
predicts.

The bridge between the two vocabularies the section note above defends: the left-hand side is
built from *reactions*, the right from *names*.
-/
@[simp]
theorem assembleGeneralMessageReactions_names
    (allSelfSends : List GeneralSelfSend)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReactions
          allSelfSends
          server
          compiledBody).map
        (fun reaction =>
          reaction.name) =
      generalMessageReactionNamesOf
        allSelfSends
        server.name := by

  cases hSites :
      generalSelfSendSitesOf
        server.name
        allSelfSends with

  | nil =>
      simp [
        assembleGeneralMessageReactions,
        generalMessageReactionNamesOf,
        assembleGeneralMessageReaction,
        hSites
      ]

  | cons firstSite remainingSites =>
      simp [
        assembleGeneralMessageReactions,
        generalMessageReactionNamesOf,
        assembleGeneralMessageReactionAtSite,
        hSites
      ]

/--
The triggers one message server's action reactions carry, in declaration order.

The specification `generalMessageReactionNamesOf` cannot express, for the reason recorded on
`assembleGeneralMessageReactionAtSite_trigger`: sibling reaction names are identical by design,
so which sibling listens to which action is invisible in names and visible only here.

This is what makes F56's closing obligation checkable rather than merely asserted. That finding
records that once one action per site is required, *"the generator must emit site reactions in
the order their sends appear in the body, which makes emission order a correctness property
rather than a formatting choice"*. A correctness property with nothing stating it is the shape
F44, F45 and F47 each recorded, so it is stated here instead of left to inspection of the
definition: the i-th reaction of the group triggers on the i-th site's action, with
`generalSelfSendSitesOf` fixing what i-th means.

The `[]` branch keeps `actionNameFor`'s spelling for the reason every zero-site branch in this
file does: the declaration side and the trigger side have to agree *per branch*, or a reaction
triggers on an action its own reactor never declares.
-/
def generalMessageReactionTriggersOf
    (allSelfSends : List GeneralSelfSend)
    (message : MsgName) :
    List LF.GeneralTrigger :=
  match
      generalSelfSendSitesOf
        message
        allSelfSends with

  | [] =>
      [.logicalAction
        (actionNameFor message)]

  | sites =>
      sites.map
        (fun send =>
          .logicalAction
            (generalActionNameAtSite
              allSelfSends
              send.site
              message))

/--
Assembling a message server's action reactions produces exactly the triggers the specification
predicts, in the order it predicts them.

Together with `assembleGeneralMessageReactions_names` this pins the group completely, and the
division of labour is exact: that theorem fixes the names and therefore the length, this one
fixes which action each position listens to. Neither implies the other — identical names carry
no order information, and identical triggers would carry no naming information — so the pair is
what a reader checking §7.3 needs, not either alone.
-/
@[simp]
theorem assembleGeneralMessageReactions_triggers
    (allSelfSends : List GeneralSelfSend)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReactions
          allSelfSends
          server
          compiledBody).map
        (fun reaction =>
          reaction.trigger) =
      generalMessageReactionTriggersOf
        allSelfSends
        server.name := by

  cases hSites :
      generalSelfSendSitesOf
        server.name
        allSelfSends with

  | nil =>
      simp [
        assembleGeneralMessageReactions,
        generalMessageReactionTriggersOf,
        assembleGeneralMessageReaction,
        hSites
      ]

  | cons firstSite remainingSites =>
      simp [
        assembleGeneralMessageReactions,
        generalMessageReactionTriggersOf,
        assembleGeneralMessageReactionAtSite,
        hSites
      ]

/--
The reaction names one class contributes, in the order they are declared.

The specification the section note above defends. Total, and independent of both the
translation and the `Except` layer — a reader can compare it against the design's §7.3 table
without holding any of this file in their head, with the one amendment F56 forced: the leading
entry of each group became a list of k entries, one per self-send site.

`selfSends` joins `routes` and `className` before the colon: none of the three varies in the
recursion, and the self-send list is the sending *class's*, so it is fixed for the whole server
list.
-/
def generalReactionNamesOf
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (className : ClassName) :
    List DTR.GeneralMessageServer →
    List ReactionName

  | [] =>
      []

  | server :: remaining =>
      (generalMessageReactionNamesOf
            selfSends
            server.name ++
          (generalRoutesIntoMessageServer
            className
            server.name
            routes).map
            (fun route =>
              portReactionNameFor
                (generalInputPortOfRoute route))) ++
        generalReactionNamesOf
          selfSends
          routes
          className
          remaining

/--
One message server's reaction group carries its action reactions first — one per self-send
site — then one port reaction per route into it, in route order.

The group-level half of the replacement, and the place the naming rule is pinned. Note what it
says about a message server nothing sends to from outside **and nothing self-sends to twice**:
the filtered route list is empty and the site list has at most one entry, so the group is a
one-element list and the reactor looks exactly as stage D left it. That is the precise sense in
which stage E is conservative on the inherited fixtures — not an appeal to their contents, but a
consequence of this equation.

**The second condition is new and was absent from this paragraph until F56.** The earlier text
named only the routing condition, which was sufficient while every message server had exactly
one action; it is not sufficient now, and `keep-alive.rebeca` is the committed fixture where the
route list is empty and the group is still two reactions long.
-/
theorem compileGeneralMessageServerReactionGroup_names
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
        .ok group) :
    group.map
        (fun reaction =>
          reaction.name) =
      generalMessageReactionNamesOf
          selfSends
          server.name ++
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

  simp [
    List.map_append,
    assembleGeneralMessageReactions_names,
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
      (selfSends : List GeneralSelfSend)
      (routes : List GeneralRoute)
      (className : ClassName)
      (servers : List DTR.GeneralMessageServer)
      (compiled : List LF.GeneralReaction),
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          servers =
          .ok compiled →
        compiled.map
            (fun reaction =>
              reaction.name) =
          generalReactionNamesOf
            selfSends
            routes
            className
            servers := by

  intro env selfSends routes className servers
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
A compiled reactor declares one logical action per self-send **site**, plus one for every
message server nothing self-sends to, in source order.

**The previous version of this docstring opened with "Unaffected by stage E" and "one logical
action per message server", and both were false by the time F56 was measured.** What the
sentence after them said is still true, and is why the error survived review: one action per
message server *no matter how many senders reach it*, because an action is the *self*-delivery
mechanism and self-sends were never routed. That correctly rules out the **routing** channel of
multiplication — a message server reached by two external senders still has one action and three
reactions — and it was read as ruling out every channel. Self-send sites multiply actions along
an axis routing never touches, so a claim that was sound about senders was wrong about actions.

The contrast with the reaction list is still the thing worth keeping, and it is now sharper: the
reaction list grows in *two* independent dimensions, senders and sites, while the action list
grows only in sites.
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
      generalActionNamesOf
        (selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers := by

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
    compileGeneralMessageServerActionsOf_names
      (selfSendsOfClass
        reactiveClass)
      reactiveClass.messageServers

/--
A compiled reactor's message reactions are its message servers' reaction groups, in
**message-server priority order**.

This is the statement §7.3 replaced, now carrying stage F's level-2 sort in its own right-hand
side. It used to say "in source order", and to name stage G as the stage that would permute it;
stage F did that instead, and the permutation is visible here rather than hidden — the right-hand
side reads `generalPriorityOrderedMessageServers reactiveClass`, not `reactiveClass.messageServers`.
Making the sort appear in the theorem statement is the point. A version that pushed `normalize`
down inside `generalReactionNamesOf` would prove the same equation while saying nothing about
order, which is exactly the shape finding **F60** caught elsewhere.

The two granularities stay distinct and both are now decided. Permuting whole groups is a
reordering of *message servers* and is level 2, applied here. Permuting *within* a group reorders
the delivery paths of one message server against each other and is level 1, applied upstream in
`routesOf`. They have different observable effects and different theorems, and neither subsumes
the other.
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
        (selfSendsOfClass
          reactiveClass)
        routes
        reactiveClass.name
        (generalPriorityOrderedMessageServers
          reactiveClass) := by

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
      (selfSendsOfClass reactiveClass)
      routes
      reactiveClass.name
      (generalPriorityOrderedMessageServers
        reactiveClass)
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

/--
A compiled reactor's startup reaction carries the constructor's parameter names, in declaration order.

Composed from the two facts just above — `compileGeneralReactiveClass_startupParameters` ties the
startup reaction's parameters to the reactor's, and `compileGeneralReactiveClass_parameters` ties the
reactor's to the class's constructor declarations — rather than proved a third time by inverting the
constructor compilation. The composition is the form the initial correspondence consumes: the target
initializer binds `reactor.startupReaction.parameters` against the instance's compiled arguments, the
source initializer binds the class's parameter names against the instance's arguments, and this lemma
says the two walks are the same names in the same order.
-/
theorem compileGeneralReactiveClass_startupParameterNames
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
      reactiveClass.constructor.parameters.map
        (fun parameter =>
          parameter.name) := by

  rw [
    compileGeneralReactiveClass_startupParameters
      hCompiled,
    compileGeneralReactiveClass_parameters
      hCompiled,
    compileGeneralTypedParameter_names
      reactiveClass.constructor.parameters
  ]

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
converse direction, and it is **not** merely deferred: as §8 words it — a decidable predicate over
DTR models, requiring no arity-zero send, no colliding generated names and DTR well-formedness — it
is **false**, refuted by the empty model, which satisfies all three conjuncts and is refused because
an LF program must declare at least one reactor and at least one instance. That is finding **F52**.

An earlier version of this passage deferred the condition to the site-totality obligation and gave as
its reason that the condition rests on the induction showing every external send site has an entry in
its class's resolved environment. That reason was wrong, and its own staleness proves it: the
induction landed, and the condition is still not provable as worded. What the condition actually
rests on is the **guard** — `declaredNames.Nodup` and `targetEndpointsUnique`, which F48 and F49
measure as failing on source the DTR layer accepts — and site totality is not about port names at
all, as the site-totality section says itself.

What is owed instead is a biconditional: acceptance holds exactly when the model is non-empty, name
resolution succeeds for every class, and the guard passes, with nothing between those able to fail.
That localises the refusal surface to two sites and replaces stage D's deleted biconditional with a
stronger statement rather than a weaker one. It cannot omit the guard, because a guard refusal is not
predictable from the source model without generating names, which are not injective (F34, F42). The
gate meanwhile answers the width question empirically for every committed fixture, and answers it
more convincingly than a theorem would, since it runs the real `lfc`.

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
Extract one conjunct of well-formedness — the ninth of ten, and until G3 the last.

A local copy of a lemma `Relico/LF/GeneralWellFormed.lean` already proves, duplicated because
that copy is `private` and this file is not the module it is private to. Duplicated rather than
de-privatised on purpose: the LF module's copy exists to serve proofs *about* well-formedness,
and making it public would invite translation-side proofs to reach past the `wellFormed`
interface for the other nine conjuncts one at a time, which is the habit that turns a
ten-clause predicate into ten independent obligations.

The proof is the house pattern — revert, unfold, split the conjunct — and it survived G3
appending a tenth conjunct *after* this one without an edit, because it case-splits on its own
named clause instead of projecting out of a fixed nesting: `&&` is right-associated and strict,
so a `false` anywhere collapses the whole chain and contradicts the hypothesis, while the `true`
branch leaves the goal trivially true. An earlier version of this comment credited the proof to
`targetEndpointsUnique` being *last*, which was a fact about the clause count of the day rather
than a property of the tactic.
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
run instead of being described here.

This docstring used to close by offering a *relative* statement — `reactorsWellFormed` together
with `instancesResolve` implies this clause — as what remained achievable. **F49 measured that as
false**: a hand-built program satisfies every other clause, including both of those, and
fails this one, so the clause is independent and no implication of that shape exists.
`instancesResolve` cannot supply the missing link, because a target endpoint pairs an *instance*
with a port name while input ports are declared on a *class*; resolution says the class exists,
not that two routes to one instance were filtered into one reactor.

The implication that does hold is indexed by the routing table rather than stated about
`LF.GeneralProgram`, and it is proved below as `assembleGeneralProgram_targetEndpointsUnique`: for
a program whose connections and whose reactor input ports are built from the *same* routes, and
whose routes agree about which class an instance has, `reactorsWellFormed` implies this clause.
That is the one-clause-fewer reduction §8's acceptance condition wants. It still derives one
guard clause from another rather than from the construction, so it licenses retiring nothing.
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
### The priority ladder — task `#147`, F84's owed theorem

G3's clause made a populated reaction priority a refusal, and the two theorems above say what
acceptance guarantees. Neither of them says the translator **never trips** the clause: a guard
that refuses is compatible with a translator that emits the offence and relies on the refusal.
`compileGeneralModel_targetEndpointsUnique` is proved *through* the guard, so for the ninth
clause that is exactly its epistemic position — the guard decided, and we read the decision off.

The tenth clause is different, and the difference is the whole content of **F84**: for priorities
we own the per-reaction equations (`assembleGeneralMessageReaction_priority`,
`assembleGeneralPortReaction_priority`, `assembleGeneralStartupReaction_priority`), and those can
be **composed up the assembly walk** — per-reaction, per-list, per-group, per-reactor, per-program —
into a proof that the assembled program satisfies the clause *before the guard ever sees it*. That
is the direction §8's original sentence had backwards, and it is what the ladder below proves.

The top two rungs are public because each states an invariant in its own words:
`assembleGeneralProgram_reactionPrioritiesAbsent` says the pre-guard assembly satisfies the
clause — the translator cannot trip it — and `compileGeneralModel_reactionPrioritiesAbsent`
says the accepted program does, **proved by composition rather than by reading the guard's
decision back**: the only guard fact its proof uses is `eq_of_guardGeneralProgram_ok`, which is
shape transparency (what the guard accepts, it returns unchanged), not the guard's verdict. Swap
the proof for `reactionPrioritiesAbsent_of_wellFormed ∘ compileGeneralModel_wellFormed` and the
statement survives while the invariant silently dies — which is why the docstring says so, and
why the assembly-level rung above it exists at all.
-/

/--
The at-site sibling of `assembleGeneralMessageReaction_priority`.

Stated for the ladder below: a message server with self-send sites contributes one action
reaction **per site**, each assembled by `assembleGeneralMessageReactionAtSite`, and every one
of those carries `priority := none` for the same reason the unsuffixed reaction does. Without
this leaf the ladder would cover the zero-site branch only, which is nine of the ten fixtures
and exactly the shape of gap that stays green while it narrows.
-/
@[simp]
theorem assembleGeneralMessageReactionAtSite_priority
    (allSelfSends : List GeneralSelfSend)
    (site : SendSite)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReactionAtSite
        allSelfSends
        site
        server
        compiledBody).priority =
      none := by
  rfl

private theorem assembleGeneralMessageReactions_prioritiesAbsent
    (allSelfSends : List GeneralSelfSend)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody) :
    (assembleGeneralMessageReactions
        allSelfSends
        server
        compiledBody).all
        (fun reaction =>
          reaction.priority.isNone) =
      true := by

  unfold
    assembleGeneralMessageReactions

  cases
      generalSelfSendSitesOf
        server.name
        allSelfSends with

  | nil =>
      simp

  | cons site remaining =>
      simp only [
        List.all_eq_true
      ]

      intro reaction hMember

      rw [
        List.mem_map
      ] at hMember

      obtain
          ⟨send, _, hReaction⟩ :=
        hMember

      rw [
        ← hReaction,
        assembleGeneralMessageReactionAtSite_priority
      ]

      rfl

private theorem assembleGeneralPortReactions_prioritiesAbsent
    (className : ClassName)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody)
    (routes : List GeneralRoute) :
    (assembleGeneralPortReactions
        className
        server
        compiledBody
        routes).all
        (fun reaction =>
          reaction.priority.isNone) =
      true := by

  simp only [
    List.all_eq_true
  ]

  intro reaction hMember

  unfold
    assembleGeneralPortReactions
      at hMember

  rw [
    List.mem_map
  ] at hMember

  obtain
      ⟨route, _, hReaction⟩ :=
    hMember

  rw [
    ← hReaction,
    assembleGeneralPortReaction_priority
  ]

  rfl

/--
One message server's whole reaction group carries no priority.

The group is the append of the action reactions and the port reactions, so this rung is
`List.all_append` over the two list rungs above. Inverting a successful group compilation goes
through `compileGeneralMessageServerReactionGroup_ok`, whose right-hand side names both lists —
which is what makes the inversion one `injection` rather than a walk.
-/
private theorem compileGeneralMessageServerReactionGroup_prioritiesAbsent
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    (hGroup :
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
        .ok group) :
    group.all
        (fun reaction =>
          reaction.priority.isNone) =
      true := by

  cases hBody :
      compileGeneralBody
        env
        { bodyKey := .messageServer server.name,
          selfSends := selfSends }
        0
        server.body with

  | error message =>
      rw [
        compileGeneralMessageServerReactionGroup_error
          hBody
      ] at hGroup

      simp at hGroup

  | ok compiledBody =>
      rw [
        compileGeneralMessageServerReactionGroup_ok
          hBody
      ] at hGroup

      injection hGroup with hGroup

      subst hGroup

      rw [
        List.all_append,
        Bool.and_eq_true
      ]

      exact
        ⟨
          assembleGeneralMessageReactions_prioritiesAbsent
            selfSends
            server
            compiledBody,
          assembleGeneralPortReactions_prioritiesAbsent
            className
            server
            compiledBody
            routes
        ⟩

/--
Every reaction of every message server of a class carries no priority, given that the reaction
list compiled.

The induction consumes one server per step through
`exists_of_compileGeneralMessageServerReactions_cons_ok`, which names the group and the tail —
so the append shape of the compiled list is available without unfolding the compilation at all.
-/
private theorem compileGeneralMessageServerReactions_prioritiesAbsent
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName} :
    ∀ (servers : List DTR.GeneralMessageServer)
      (compiled : List LF.GeneralReaction),
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          servers =
        .ok compiled →
        compiled.all
            (fun reaction =>
              reaction.priority.isNone) =
          true := by

  intro servers
  induction servers with

  | nil =>
      intro compiled hCompiled

      rw [
        eq_nil_of_compileGeneralMessageServerReactions_nil_ok
          hCompiled
      ]

      rfl

  | cons server remaining inductionHypothesis =>
      intro compiled hCompiled

      rcases
          exists_of_compileGeneralMessageServerReactions_cons_ok
            hCompiled with
        ⟨
          group,
          compiledRemaining,
          hGroup,
          hRemaining,
          hCompiledEq
        ⟩

      subst hCompiledEq

      rw [
        List.all_append,
        Bool.and_eq_true
      ]

      exact
        ⟨
          compileGeneralMessageServerReactionGroup_prioritiesAbsent
            hGroup,
          inductionHypothesis
            compiledRemaining
            hRemaining
        ⟩

/--
The reactor-granularity rung of the priority ladder: a successfully compiled reactor's startup
reaction and every one of its message reactions carry no priority.

This is the composition the three per-reaction theorems were always halves of. The startup half
inverts `compileGeneralConstructor` to recover the `assembleGeneralStartupReaction` shape and
applies `assembleGeneralStartupReaction_priority`; the message half is the server-list rung
above, over the very list `compileGeneralReactiveClass` assembled — including that it is
`generalPriorityOrderedMessageServers` that was walked, which is why the rung is stated against
the compilation rather than against the class's declaration order.
-/
theorem compileGeneralReactiveClass_prioritiesAbsent
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
    (reactor.startupReaction.priority.isNone &&
      reactor.messageReactions.all
        (fun reaction =>
          reaction.priority.isNone)) =
      true := by

  rcases
      exists_of_compileGeneralReactiveClass_ok
        hCompiled with
    ⟨
      env,
      compiledStartupReaction,
      compiledMessageReactions,
      _hEnv,
      hConstructor,
      hMessageReactions,
      hReactor
    ⟩

  subst hReactor

  show
    (compiledStartupReaction.priority.isNone &&
      compiledMessageReactions.all
        (fun reaction =>
          reaction.priority.isNone)) =
      true

  rw [
    Bool.and_eq_true
  ]

  constructor

  · rcases
        exists_of_compileGeneralConstructor_ok
          hConstructor with
      ⟨
        compiledBody,
        _hBody,
        hStartupReaction
      ⟩

    rw [
      hStartupReaction,
      assembleGeneralStartupReaction_priority
    ]

    rfl

  · exact
      compileGeneralMessageServerReactions_prioritiesAbsent
        (generalPriorityOrderedMessageServers
          reactiveClass)
        compiledMessageReactions
        hMessageReactions

private theorem compileGeneralReactiveClasses_prioritiesAbsent
    {allClasses : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute} :
    ∀ (classes : List DTR.GeneralReactiveClass)
      (compiled : List LF.GeneralReactor),
      compileGeneralReactiveClasses
          allClasses
          routes
          classes =
        .ok compiled →
        compiled.all
          (fun reactor =>
            reactor.startupReaction.priority.isNone &&
              reactor.messageReactions.all
                (fun reaction =>
                  reaction.priority.isNone)) =
          true := by

  intro classes
  induction classes with

  | nil =>
      intro compiled hCompiled

      rw [
        eq_nil_of_compileGeneralReactiveClasses_nil_ok
          hCompiled
      ]

      rfl

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

      rw [
        List.all_cons,
        Bool.and_eq_true
      ]

      exact
        ⟨
          compileGeneralReactiveClass_prioritiesAbsent
            hClass,
          inductionHypothesis
            compiledRemaining
            hRemaining
        ⟩

/--
The assembled program satisfies the tenth clause — **before the guard sees it**.

This is the invariant the ladder exists for, and the reason it is stated over
`assembleGeneralProgram` rather than over `compileGeneralModel`: no guard is mentioned, accepted
or refused, so the theorem says the translator *cannot* emit a reaction with a populated
priority, not merely that it cannot get away with one. `reactionPrioritiesAbsent` is a guard
clause today; if a later stage moved the check elsewhere, this theorem would still be true and
still be about the same artefact.
-/
theorem assembleGeneralProgram_reactionPrioritiesAbsent
    {model : DTR.GeneralModel}
    {routes : List GeneralRoute}
    {compiledReactors : List LF.GeneralReactor}
    (hClasses :
      compileGeneralReactiveClasses
          model.classes
          routes
          model.classes =
        .ok compiledReactors) :
    (assembleGeneralProgram
        model
        routes
        compiledReactors).reactionPrioritiesAbsent =
      true := by

  unfold
    LF.GeneralProgram.reactionPrioritiesAbsent

  rw [
    assembleGeneralProgram_reactors
  ]

  exact
    compileGeneralReactiveClasses_prioritiesAbsent
      model.classes
      compiledReactors
      hClasses

/--
An accepted program satisfies the tenth clause — **by composition, not by the guard's verdict**.

Task `#147`, the theorem F84 recorded as owed. The statement is one a reader could get from the
guard in two lines (`compileGeneralModel_wellFormed`, then a conjunct extraction), and the
two-line proof exists; it is deliberately not the proof here. Reading the clause off the guard's
decision establishes only that *if* the translator emitted a populated priority, *then* nobody
would see it — the refusal would hide it. Composing the per-reaction equations up through
`assembleGeneralProgram_reactionPrioritiesAbsent` establishes that the offence is never emitted
in the first place. Same conclusion, different theorem, and the weaker one is a strict subset of
the evidence.

The only guard fact this proof uses is `eq_of_guardGeneralProgram_ok` — what the guard accepts,
it returns unchanged — which is shape transparency rather than the guard's judgment. If a later
edit swaps this proof for the guard-extraction one, the statement survives and the invariant
silently dies; the assembly-level theorem above is what keeps that detectable.
-/
theorem compileGeneralModel_reactionPrioritiesAbsent
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program) :
    program.reactionPrioritiesAbsent =
      true := by

  rcases
      exists_of_compileGeneralModel_ok
        hCompiled with
    ⟨
      routes,
      compiledReactors,
      _hRoutes,
      hClasses,
      _hProgram
    ⟩

  rw [
    compileGeneralModel_ok
      _hRoutes
      hClasses
  ] at hCompiled

  have hAssembled :
      assembleGeneralProgram
          model
          routes
          compiledReactors =
        program :=
    eq_of_guardGeneralProgram_ok
      hCompiled

  rw [
    ← hAssembled
  ]

  exact
    assembleGeneralProgram_reactionPrioritiesAbsent
      hClasses

/--
`Nodup` of an append restricts to either side.

Hand-rolled for the same reason `LF.GeneralWellFormed`'s `eq_of_nodup_map` is: this development
depends on Lean core alone, and core exposes no `Nodup.of_append_left`. Both are needed because
`LF.GeneralReactor.declaredNames` is five appended lists and the input port names are the second
of the five, so reaching them costs three left steps and one right step.
-/
private theorem nodup_of_append_left
    {α : Type} :
    ∀ (left right : List α),
      (left ++ right).Nodup →
        left.Nodup := by

  intro left right
  induction left with

  | nil =>
      intro _
      simp

  | cons head remaining inductionHypothesis =>
      intro hNodup

      rw [List.cons_append] at hNodup

      cases hNodup with

      | cons hHead hTail =>
          constructor

          · intro value hMember
            exact
              hHead
                value
                (List.mem_append.mpr
                  (Or.inl hMember))

          · exact
              inductionHypothesis
                hTail

/--
The right-hand companion of `nodup_of_append_left`.
-/
private theorem nodup_of_append_right
    {α : Type} :
    ∀ (left right : List α),
      (left ++ right).Nodup →
        right.Nodup := by

  intro left right
  induction left with

  | nil =>
      intro hNodup
      rw [List.nil_append] at hNodup
      exact hNodup

  | cons head remaining inductionHypothesis =>
      intro hNodup

      rw [List.cons_append] at hNodup

      cases hNodup with

      | cons _ hTail =>
          exact
            inductionHypothesis
              hTail

/--
A well-formed reactor declares distinct input port names.

This is the projection that turns the guard's decided `declaredNames.Nodup` into the hypothesis
`Translation.generalRouteEndpoints_nodup` asks for. The clause is extracted by contradiction
rather than positionally: assume the negation, and the `&&` chain collapses to `false`, so the
proof does not depend on where in `wellFormed` the clause sits or on how the chain associates.
-/
private theorem inputPortNames_nodup_of_wellFormed
    {reactor : LF.GeneralReactor}
    (hWellFormed :
      reactor.wellFormed = true) :
    (reactor.inputPorts.map
      (fun port =>
        port.name.value)).Nodup := by

  have hNodup :
      reactor.declaredNames.Nodup := by
    by_cases hCandidate :
        reactor.declaredNames.Nodup

    · exact hCandidate

    · revert hWellFormed
      unfold LF.GeneralReactor.wellFormed
      simp [hCandidate]

  unfold LF.GeneralReactor.declaredNames at hNodup

  exact
    nodup_of_append_right _ _
      (nodup_of_append_left _ _
        (nodup_of_append_left _ _
          (nodup_of_append_left _ _
            hNodup)))

/--
A compiled reactor's input-port names are distinct whenever the reactor is well formed —
the **F81 discharge, input-port half**.

F81 measured (2026-08-26) that the routing/resolution theorems of
`Relico/Correctness/GeneralCorrespondence.lean` hypothesize this exact `Nodup` and that
nothing public concluded it: the projection that turns a decided `declaredNames.Nodup` into
it existed only as `inputPortNames_nodup_of_wellFormed` above, which is `private` by the rule
that a module's public surface widens only with a consumer. The consumer has since arrived, so
this theorem is the public, per-class restatement: `compileGeneralReactiveClass_inputPorts`
identifies the compiled reactor's ports with the routing projection for its class, and the
private projection supplies the distinctness. The private lemma is not de-privatised — this
theorem is the consumer-facing form, and it lives beside the lemma it wraps.
-/
theorem compileGeneralReactiveClass_inputPortNames_nodup
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (hWellFormed :
      reactor.wellFormed =
        true) :
    ((generalInputPortsOf
        reactiveClass.name
        routes).map
      (fun port =>
        port.name.value)).Nodup := by
  rw [
    ← compileGeneralReactiveClass_inputPorts
        hCompiled
  ]

  exact
    inputPortNames_nodup_of_wellFormed
      hWellFormed

/--
A compiled reactor's action names are distinct whenever the reactor is well formed —
the **F81 discharge, action-names half**, and the one F81 recorded as having *no* decided
source at all: `generalActionNamesOf` mixes the per-server names with the per-site names the
F56 repair introduced, and no theorem anywhere concluded its `Nodup`.

The decided source turns out to be the compiled reactor itself. The reactor's
`declaredNames.Nodup` — a `wellFormed` conjunct — has the logical-action names as its last
segment (`assembleGeneralReactor` builds the list, and `++` chains left-associatively, so one
`nodup_of_append_right` reaches it), and
`compileGeneralReactiveClass_actionNames` states that those names *are*
`generalActionNamesOf` for the class. The bridge is a map composition
(`List.map_map`) — no injectivity argument, no per-site reasoning, and no induction over
either function: F56's site-suffixing machinery is invisible because the distinctness is
inherited wholesale from the declaration the guard already decided.

Stated per class, like its input-port twin: the program-level plumbing that turns guard
acceptance into reactor well-formedness is the composition theorem's job
(`Correctness.generalTriggerDistinctness_of_wellFormed`), not this one's.
-/
theorem compileGeneralReactiveClass_actionNames_nodup
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (hWellFormed :
      reactor.wellFormed =
        true) :
    ((generalActionNamesOf
        (selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
      (fun name =>
        name.value)).Nodup := by
  have hNodup :
      reactor.declaredNames.Nodup := by
    by_cases hCandidate :
        reactor.declaredNames.Nodup

    · exact hCandidate

    · revert hWellFormed
      unfold LF.GeneralReactor.wellFormed
      simp [hCandidate]

  unfold LF.GeneralReactor.declaredNames at hNodup

  have hActions :
      (reactor.logicalActions.map
        (fun action =>
          action.name.value)).Nodup :=
    nodup_of_append_right _ _ hNodup

  rw [
    ← compileGeneralReactiveClass_actionNames
        hCompiled,
    List.map_map
  ]

  exact hActions

/--
The ninth well-formedness clause, derived from the third — on assembled programs, not in general.

F49 measured `targetEndpointsUnique` to be independent of every other clause, so this is the
strongest statement of its kind available: it is indexed by the routing table the assembler was
given, and `reactorsWellFormed` is what discharges it.

Two hypotheses beyond that clause, and both are real content rather than bookkeeping.

`hReceiverClass` says the routes agree about which class an instance has. `assembleGeneralProgram`
does not know this — nothing in its body relates its `compiledReactors` to its `routes` — and
without it two routes could target one instance through two different classes, where no single
reactor's `declaredNames` can see the collision.

`hReactorOf` is the link the opaque `compiledReactors` argument otherwise lacks: every route's
receiver class has a reactor among them whose input ports are the ones `generalInputPortsOf`
builds from these same routes.

**Scope, stated plainly.** This is content-equivalent to a `compileGeneralModel`-level statement
modulo two facts about the functions that produce these arguments — that `routesOf` resolves a
route's receiver class from its receiver instance, and that `compileGeneralReactiveClasses` emits
one reactor per class with `generalInputPortsOf` for its input ports. Those two are the named
residue, not a silent gap; `compileGeneralModel_targetEndpointsUnique` above continues to get the
same conclusion from the guard, so nothing downstream waits on them.
-/
theorem assembleGeneralProgram_targetEndpointsUnique
    {model : DTR.GeneralModel}
    {routes : List GeneralRoute}
    {compiledReactors : List LF.GeneralReactor}
    (hReceiverClass :
      ∀ (first : GeneralRoute),
        first ∈ routes →
        ∀ (second : GeneralRoute),
          second ∈ routes →
          first.receiverInstance = second.receiverInstance →
            first.receiverClass = second.receiverClass)
    (hReactorOf :
      ∀ (route : GeneralRoute),
        route ∈ routes →
          ∃ (reactor : LF.GeneralReactor),
            reactor ∈ compiledReactors ∧
              reactor.inputPorts =
                generalInputPortsOf
                  route.receiverClass
                  routes)
    (hReactorsWellFormed :
      (assembleGeneralProgram
        model
        routes
        compiledReactors).reactorsWellFormed =
          true) :
    (assembleGeneralProgram
      model
      routes
      compiledReactors).targetEndpointsUnique =
        true := by

  have hAll :
      ∀ (reactor : LF.GeneralReactor),
        reactor ∈ compiledReactors →
          reactor.wellFormed = true := by

    have hReactors := hReactorsWellFormed

    unfold LF.GeneralProgram.reactorsWellFormed at hReactors

    rw [
      assembleGeneralProgram_reactors
    ] at hReactors

    simp only [
      List.all_eq_true
    ] at hReactors

    intro reactor hMember

    exact
      hReactors
        reactor
        hMember

  have hInputPortNames :
      ∀ (route : GeneralRoute),
        route ∈ routes →
          ((generalInputPortsOf
            route.receiverClass
            routes).map
            (fun port =>
              port.name.value)).Nodup := by

    intro route hRoute

    rcases
        hReactorOf
          route
          hRoute
      with
        ⟨reactor,
         hMember,
         hPorts⟩

    rw [← hPorts]

    exact
      inputPortNames_nodup_of_wellFormed
        (hAll reactor hMember)

  unfold LF.GeneralProgram.targetEndpointsUnique

  rw [
    assembleGeneralProgram_connections
  ]

  simp only [
    decide_eq_true_eq
  ]

  exact
    generalConnectionsOf_targetEndpoints_nodup
      routes
      hReceiverClass
      hInputPortNames

/-!
## Site totality

The defensive arm at `compileGeneralStmt` — the one whose diagnostic says *"this is a defect in
the translator and not in the model"* — is unreachable whenever the environment it is given came
from `outputPortEnvOf`. This section proves that.

`docs/STAGE_E_DESIGN.md` §8 asks for a sufficient condition for acceptance, and this section does
**not** deliver it. What it delivers is *totality*: **given a resolved environment, compiling a
reactive class cannot fail at all.** The two are incomparable rather than ordered, and an earlier
version of this docstring claimed the second bought more than §8 asked for, which is false in both
directions. This result *assumes* the resolution stage succeeded — part of what §8's conjuncts were
meant to deliver — and it concludes about the middle stage only, so it says nothing about routing and
nothing about the guard, which is where refusal on legal models actually lives (F32, F43, F48, F49).
§8's ask is separately refuted as worded, by the empty model, as finding **F52**; the theorem owed in
its place is a biconditional localising the refusal surface to resolution and the guard, and this
section is its load-bearing half — it is what discharges the middle stage.

The reason is a measurement rather than an argument. Every `.error` in this file below
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
    (context : GeneralBodyContext)
    (index : Nat)
    (target : VarName)
    (value : DTR.GeneralExpr) :
    compileGeneralStmt
        env
        context
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
Compiling a local declaration cannot fail.

The third always-succeeding statement form, after `assign` and `trace`: a declaration
consults no port, no action and no site, because it performs no effect — which is also
why both send-site walks in `Relico/Translation/GeneralRouting.lean` contribute nothing
for one, and why `compileGeneralStmt` never had to thread anything through this arm that
its siblings do not already carry.

The name is unchanged and the type goes through `compileGeneralType`, the same map a
state variable's declaration and a port payload's fields go through, so a local's type is
spelled by the one place that spells every other declared type: `renderGeneralType` in the
printer. The initialiser goes through `compileGeneralExpr` like every other expression,
and is always present because the DTR constructor requires one — an absent source
initialiser is the elaborator's to default, the same way an absent `after` is.
-/
theorem compileGeneralStmt_localDecl
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext)
    (index : Nat)
    (name : VarName)
    (declaredType : DTR.GeneralType)
    (value : DTR.GeneralExpr) :
    compileGeneralStmt
        env
        context
        index
        (
          .localDecl
            name
            declaredType
            value
        ) =
      .ok
        (.localDecl
          name
          (compileGeneralType
            declaredType)
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
    (context : GeneralBodyContext)
    (index : Nat)
    (message : MsgName)
    (arguments : List DTR.GeneralExpr)
    (delay : Delay) :
    compileGeneralStmt
        env
        context
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
          (generalActionNameAtSite
            context.selfSends
            {
              body :=
                context.bodyKey

              index :=
                context.levelPath ++
                  [index]
            }
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
    (context : GeneralBodyContext)
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
              context.bodyKey

            index :=
              context.levelPath ++
                [index]
          } =
        some entry) :
    compileGeneralStmt
        env
        context
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

The hypothesis is quantified over `externalSendsFromIndex bodyKey levelPath index body` — the
sends of *this* body from *this* index at *this* level — and not over the class's whole send
list, which is what makes the recursion go through: the tail's hypothesis is the head's
hypothesis with one statement removed, and that is exactly what the six arm equations in
`Relico/Translation/GeneralRouting.lean` say. The index advances in step with
`externalSendsFromIndex` because both functions advance it once per statement, which is the
alignment the note on `compileGeneralBody` flags as worth stating even though no earlier theorem
needed it. This theorem needs it.

**Written as a recursive theorem rather than with `induction`, and that is stage H's doing.** The
conditional case has to apply this statement to the two *branch* bodies, and `induction` over a
list offers an induction hypothesis for the tail only. Recursing explicitly gives all three, and
Lean accepts it structurally for the same reason it accepts `externalSendsFromIndex`, whose
conditional arm walks the same three bodies.

**The conditional case is the reason this theorem was false for one build.** While
`compileGeneralStmt` refused conditionals, a body containing one made the hypothesis hold
vacuously — `externalSendsFromIndex` skipped branches, so it reported no sends to resolve — while
the conclusion asserted a compilation that returned `.error`. Two escapes were available and both
were declined: adding a branch-free hypothesis, which would have narrowed the statement, and
reverting the constructor. What repaired it is the translation compiling conditionals, which is
the ordering `docs/decisions/0046-send-site-identity-under-nested-control-flow.md` §6 sets out.
So this theorem is not merely restored: it now says that a *branch's* sends being resolvable is
enough for a branch to compile, which is a stronger sentence than the one stage E proved.

**Stage I falsified this theorem for `.localDecl` for exactly one layer's duration, and S-I3
repaired it.** S-I1 added the source constructor with a refusal here, which put the theorem back
in the falsified state stage H's conditional once made famous — the `.localDecl` case's hypothesis
held vacuously while its conclusion asserted a compilation that returned `.error` — and the case
was left as a named obligation rather than a weakened statement, exactly as the stage H S2
precedent directs. S-I3 replaced the refusal with the compile arm and the case closed as the
`assign` case does. The theorem is once again true unconditionally for every statement form the
source type carries, and the sentence above about *why* the ordering matters is the record of how
that was kept honest.
-/
theorem exists_compileGeneralBody
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext)
    (body : DTR.GeneralBody) :
    ∀ index : Nat,
      (∀ send ∈
          externalSendsFromIndex
            context.bodyKey
            context.levelPath
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
            context
            index
            body =
          .ok compiled := by

  intro index hSends

  cases body with

  | nil =>

      exact
        ⟨[],
         compileGeneralBody_nil
           env
           context
           index⟩

  | cons statement remaining =>

      cases statement with

      | assign target value =>

          have hStatement :
              compileGeneralStmt
                  env
                  context
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
              context
              index
              target
              value

          obtain ⟨compiledRemaining, hRemaining⟩ :=
            exists_compileGeneralBody
              env
              context
              remaining
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

      | trace tag =>

          have hStatement :
              compileGeneralStmt
                  env
                  context
                  index
                  (
                    .trace
                      tag
                  ) =
                .ok
                  (.trace
                    tag) := by
            simp [
              compileGeneralStmt
            ]

          obtain ⟨compiledRemaining, hRemaining⟩ :=
            exists_compileGeneralBody
              env
              context
              remaining
              (index + 1)
              (by
                intro send hMember

                exact
                  hSends
                    send
                    (by
                      rw [
                        externalSendsFromIndex_trace
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
                      context
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
                        (generalActionNameAtSite
                          context.selfSends
                          {
                            body :=
                              context.bodyKey

                            index :=
                              context.levelPath ++
                                [index]
                          }
                          message)
                        (arguments.map
                          compileGeneralExpr)
                        delay) :=
                compileGeneralStmt_send_selfTarget
                  env
                  context
                  index
                  message
                  arguments
                  delay

              obtain ⟨compiledRemaining, hRemaining⟩ :=
                exists_compileGeneralBody
                  env
                  context
                  remaining
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
                          context.bodyKey

                        index :=
                          context.levelPath ++
                            [index]
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
                          context.bodyKey

                        index :=
                          context.levelPath ++
                            [index]
                      } =
                    some entry :=
                hEntry

              have hStatement :
                  compileGeneralStmt
                      env
                      context
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
                  context
                  index
                  rebec
                  message
                  arguments
                  delay
                  hLookup

              obtain ⟨compiledRemaining, hRemaining⟩ :=
                exists_compileGeneralBody
                  env
                  context
                  remaining
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

      | ifThenElse condition thenBody elseBody =>

          obtain ⟨compiledThen, hThen⟩ :=
            exists_compileGeneralBody
              env
              {
                bodyKey :=
                  context.bodyKey

                selfSends :=
                  context.selfSends

                levelPath :=
                  context.levelPath ++
                    [index, 0]
              }
              thenBody
              0
              (by
                intro send hMember

                exact
                  hSends
                    send
                    (by
                      rw [
                        externalSendsFromIndex_ifThenElse
                      ]

                      exact
                        List.mem_append.mpr
                          (Or.inl
                            (List.mem_append.mpr
                              (Or.inl
                                hMember)))))

          obtain ⟨compiledElse, hElse⟩ :=
            exists_compileGeneralBody
              env
              {
                bodyKey :=
                  context.bodyKey

                selfSends :=
                  context.selfSends

                levelPath :=
                  context.levelPath ++
                    [index, 1]
              }
              elseBody
              0
              (by
                intro send hMember

                exact
                  hSends
                    send
                    (by
                      rw [
                        externalSendsFromIndex_ifThenElse
                      ]

                      exact
                        List.mem_append.mpr
                          (Or.inl
                            (List.mem_append.mpr
                              (Or.inr
                                hMember)))))

          have hStatement :
              compileGeneralStmt
                  env
                  context
                  index
                  (
                    .ifThenElse
                      condition
                      thenBody
                      elseBody
                  ) =
                .ok
                  (.ifThenElse
                    (compileGeneralExpr
                      condition)
                    compiledThen
                    compiledElse) := by
            simp [
              compileGeneralStmt,
              hThen,
              hElse
            ]

          obtain ⟨compiledRemaining, hRemaining⟩ :=
            exists_compileGeneralBody
              env
              context
              remaining
              (index + 1)
              (by
                intro send hMember

                exact
                  hSends
                    send
                    (by
                      rw [
                        externalSendsFromIndex_ifThenElse
                      ]

                      exact
                        List.mem_append.mpr
                          (Or.inr
                            hMember)))

          exact
            ⟨_,
             compileGeneralBody_cons_ok
               hStatement
               hRemaining⟩

      | localDecl name declaredType initialiser =>

          -- The repaired shape the S-I1 comment below promised. `hSends` reduces to the
          -- tail's hypothesis because this head contributes no external send, and the
          -- head now compiles, so the arm is the `assign` arm with a different equation
          -- lemma — no contradiction, no vacuity, nothing unproved.
          have hStatement :
              compileGeneralStmt
                  env
                  context
                  index
                  (
                    .localDecl
                      name
                      declaredType
                      initialiser
                  ) =
                .ok
                  (.localDecl
                    name
                    (compileGeneralType
                      declaredType)
                    (compileGeneralExpr
                      initialiser)) :=
            compileGeneralStmt_localDecl
              env
              context
              index
              name
              declaredType
              initialiser

          obtain ⟨compiledRemaining, hRemaining⟩ :=
            exists_compileGeneralBody
              env
              context
              remaining
              (index + 1)
              (by
                intro send hMember

                exact
                  hSends
                    send
                    (by
                      rw [
                        externalSendsFromIndex_localDecl
                      ]

                      exact hMember))

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
    (selfSends : List GeneralSelfSend)
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
          selfSends
          classConstructor =
        .ok compiled := by

  obtain ⟨compiledBody, hBody⟩ :=
    exists_compileGeneralBody
      env
      { bodyKey := .constructor, selfSends := selfSends }
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
    (selfSends : List GeneralSelfSend)
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
          selfSends
          routes
          className
          server =
        .ok compiled := by

  obtain ⟨compiledBody, hBody⟩ :=
    exists_compileGeneralBody
      env
      { bodyKey := .messageServer server.name, selfSends := selfSends }
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
    (selfSends : List GeneralSelfSend)
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
          selfSends
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
           selfSends
           routes
           className⟩

  | cons server remaining inductionHypothesis =>
      intro hSends

      obtain ⟨group, hGroup⟩ :=
        exists_compileGeneralMessageServerReactionGroup
          env
          selfSends
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
      (selfSendsOfClass reactiveClass)
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
      (selfSendsOfClass reactiveClass)
      routes
      reactiveClass.name
      (generalPriorityOrderedMessageServers
        reactiveClass)
      (by
        intro server hServer send hMember

        exact
          exists_generalEntryAtSite?_of_mem_sends
            hEnv
            (mem_externalSendsOfClass_of_mem_messageServer
              ((generalPriorityOrderedMessageServers_mem_iff
                server
                reactiveClass).mp
                hServer)
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

/--
The `cons` case of `compileGeneralBody`, read backwards.

The three equations near `compileGeneralBody` go from the parts to the whole. Every induction
that reasons about a body the translator *already* compiled needs the other direction, because
what such a proof holds is the hypothesis that the whole call succeeded.

Derived from those three equations by case analysis rather than by unfolding
`compileGeneralBody`, and the difference matters: unfolding exposes the shape of the match the
equation compiler generated, which is not part of this function's interface and has changed
under us before. The equations are the interface, and this lemma keeps them the only one.
-/
theorem compileGeneralBody_cons_ok_inversion
    {env : GeneralOutputPortEnv}
    {context : GeneralBodyContext}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {remaining : DTR.GeneralBody}
    {compiled : LF.GeneralBody}
    (hCompiled :
      compileGeneralBody
          env
          context
          index
          (statement :: remaining) =
        .ok compiled) :
    ∃ (compiledStatement : LF.GeneralStmt)
      (compiledRemaining : LF.GeneralBody),
      compileGeneralStmt
          env
          context
          index
          statement =
        .ok compiledStatement ∧
      compileGeneralBody
          env
          context
          (index + 1)
          remaining =
        .ok compiledRemaining ∧
      compiled =
        compiledStatement ::
          compiledRemaining := by

  cases hStatement :
      compileGeneralStmt
        env
        context
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
            context
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

          injection hCompiled with hEqual

          -- `rfl`, not `hStatement` and `hRemaining`, and the reason is worth stating
          -- because it cost a build: `cases h : e` generalizes `e` in the *goal* as well
          -- as recording the equation. Both compilation components of the existential
          -- mention the two scrutinees, so by here they have already been rewritten to
          -- `Except.ok _ = Except.ok _` and close by reflexivity. The two hypotheses are
          -- still needed -- they are what the `rw`s above consume -- but passing them
          -- here is an application type mismatch, since they still speak about the
          -- un-generalized calls.
          exact
            ⟨compiledStatement,
             compiledRemaining,
             rfl,
             rfl,
             hEqual.symm⟩

/--
A compiled `.setPort` came from an external send at *this* site, and it carries the port name
the routing table put there.

The only arm of `compileGeneralStmt` that emits `.setPort` is the external send, and that arm
takes its port name from `generalEntryAtSite?` at the index it was handed. That is the whole
content of this lemma, and it is what lets an induction over a *compiled* body talk about
sites at all: a `setPort` in the output is a witness that the environment has an entry at that
index, so the compiled body and the routing table can be compared without re-deriving either.

Both the environment and the body key are fixed, because both are fixed along
`compileGeneralBody`'s recursion and only the index moves.
-/
private theorem compileGeneralStmt_setPort_inversion
    {env : GeneralOutputPortEnv}
    {context : GeneralBodyContext}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {port : PortName}
    {arguments : List LF.GeneralExpr}
    (hStatement :
      compileGeneralStmt
          env
          context
          index
          statement =
        .ok
          (.setPort
            port
            arguments)) :
    ∃ (entry : GeneralOutputPortEntry),
      generalEntryAtSite?
          env
          {
            body :=
              context.bodyKey

            index :=
              context.levelPath ++
                [index]
          } =
        some entry ∧
      entry.outputPort = port := by

  cases statement with

  | assign target value =>
      simp [
        compileGeneralStmt
      ] at hStatement

  | trace tag =>
      simp [
        compileGeneralStmt
      ] at hStatement

  | send target message sendArguments delay =>

      cases target with

      | selfTarget =>
          simp [
            compileGeneralStmt
          ] at hStatement

      | knownRebec rebec =>

          cases hEntry :
              generalEntryAtSite?
                env
                {
                  body :=
                    context.bodyKey

                  index :=
                    context.levelPath ++
                      [index]
                } with

          | none =>
              simp [
                compileGeneralStmt,
                hEntry
              ] at hStatement

          | some entry =>
              simp only [
                compileGeneralStmt,
                hEntry,
                Except.ok.injEq,
                LF.GeneralStmt.setPort.injEq
              ] at hStatement

              -- `rfl` rather than `hEntry`, for the reason given at the end of
              -- `compileGeneralBody_cons_ok_inversion` above: the goal's lookup was
              -- generalized by the `cases hEntry :` that produced this branch.
              exact
                ⟨entry,
                 rfl,
                 hStatement.left⟩

  | localDecl _ _ _ =>
      -- A compiled local declaration is `.ok localDecl`, never `.ok setPort`, so this
      -- arm is discharged from `hStatement` alone: the two constructors differ, and
      -- the head equation reduces without casing anything, since the compile arm
      -- consults no site. The `cases` on the declared type that stood here during
      -- stage I's refusal period existed only to make the refusal message reduce and
      -- is dead now that the arm compiles.
      simp [
        compileGeneralStmt
      ] at hStatement

  | ifThenElse condition thenBody elseBody =>
      -- A compiled conditional is `.ifThenElse`, never `.setPort`, so this arm is
      -- discharged from `hStatement` alone. The two `cases` are needed because
      -- `compileGeneralStmt`'s conditional arm matches on two compilations before it
      -- returns, and a hypothesis about the whole match cannot be simplified until
      -- both scrutinees are known.
      cases hThen :
          compileGeneralBody
            env
            {
              bodyKey :=
                context.bodyKey

              selfSends :=
                context.selfSends

              levelPath :=
                context.levelPath ++
                  [index, 0]
            }
            0
            thenBody with

      | error message =>
          simp [
            compileGeneralStmt,
            hThen
          ] at hStatement

      | ok compiledThen =>

          cases hElse :
              compileGeneralBody
                env
                {
                  bodyKey :=
                    context.bodyKey

                  selfSends :=
                    context.selfSends

                  levelPath :=
                    context.levelPath ++
                      [index, 1]
                }
                0
                elseBody with

          | error message =>
              simp [
                compileGeneralStmt,
                hThen,
                hElse
              ] at hStatement

          | ok compiledElse =>
              simp [
                compileGeneralStmt,
                hThen,
                hElse
              ] at hStatement

/--
Compiling a source conditional succeeds exactly when both its branches do, and then the compiled
statement is the LF conditional over the compiled condition.

The **public** inversion, in the direction a correspondence proof needs: the source statement is known
to be a conditional and the target's shape is what has to be discovered. `compileGeneralStmt_ifThenElse_inversion`
below runs the other way — from a known compiled shape back to the source — and stays `private`, because
its two callers are the site lemmas in this module and `CONTRIBUTING.md` prefers a second small lemma to
a de-privatised one.

Both branch equations name the exact context the translation used, `context.levelPath ++ [index, 0]` and
`… ++ [index, 1]` from index `0`, so a consumer cannot accidentally relate a branch compiled at some
other address. That is the whole content of
`docs/decisions/0046-send-site-identity-under-nested-control-flow.md` as a proof obligation.
-/
theorem compileGeneralStmt_ifThenElse_ok_inversion
    {env : GeneralOutputPortEnv}
    {context : GeneralBodyContext}
    {index : Nat}
    {condition : DTR.GeneralExpr}
    {thenBody elseBody : DTR.GeneralBody}
    {compiledStatement : LF.GeneralStmt}
    (hStatement :
      compileGeneralStmt
          env
          context
          index
          (
            .ifThenElse
              condition
              thenBody
              elseBody
          ) =
        .ok compiledStatement) :
    ∃ (compiledThen compiledElse : LF.GeneralBody),
      compiledStatement =
          .ifThenElse
            (compileGeneralExpr
              condition)
            compiledThen
            compiledElse ∧
        compileGeneralBody
            env
          {
            bodyKey :=
              context.bodyKey

            selfSends :=
              context.selfSends

            levelPath :=
              context.levelPath ++
                [index, 0]
          }
            0
            thenBody =
          .ok compiledThen ∧
        compileGeneralBody
            env
          {
            bodyKey :=
              context.bodyKey

            selfSends :=
              context.selfSends

            levelPath :=
              context.levelPath ++
                [index, 1]
          }
            0
            elseBody =
          .ok compiledElse := by

  cases hThen :
      compileGeneralBody
        env
          {
            bodyKey :=
              context.bodyKey

            selfSends :=
              context.selfSends

            levelPath :=
              context.levelPath ++
                [index, 0]
          }
        0
        thenBody with

  | error message =>
      simp [
        compileGeneralStmt,
        hThen
      ] at hStatement

  | ok compiledThen =>

      cases hElse :
          compileGeneralBody
            env
          {
            bodyKey :=
              context.bodyKey

            selfSends :=
              context.selfSends

            levelPath :=
              context.levelPath ++
                [index, 1]
          }
            0
            elseBody with

      | error message =>
          simp [
            compileGeneralStmt,
            hThen,
            hElse
          ] at hStatement

      | ok compiledElse =>

          simp only [
            compileGeneralStmt,
            hThen,
            hElse,
            Except.ok.injEq
          ] at hStatement

          -- `rfl` rather than `hThen`/`hElse`: the two `cases` above generalized both branch
          -- compilations in the goal, so the equations they name are already the goal's own.
          exact
            ⟨compiledThen,
             compiledElse,
             hStatement.symm,
             rfl,
             rfl⟩

/--
A compiled conditional came from a source conditional, and its two branches are the
compilations of the source branches at the two addresses stage H assigns them.

The mirror of `compileGeneralStmt_setPort_inversion` for the constructor stage H added, and it
exists for the same reason: an induction over a *compiled* body meets a compiled statement and
needs to know what source statement produced it before it can say anything about the sites
inside it. Both branch equations name the exact context the translation used, so a proof that
consumes this lemma cannot accidentally reason about a branch compiled at some other address.

**It replaces `compileGeneralStmt_ne_ifThenElse`, which was true for exactly one build and is
now false.** That lemma said the translator never emits a conditional, which held only while
`compileGeneralStmt` refused one; its docstring said it must be deleted rather than adapted the
day the translation compiles conditionals, and this is that deletion. The two inductions below
now owe real branch cases, and they discharge them with this.
-/
private theorem compileGeneralStmt_ifThenElse_inversion
    {env : GeneralOutputPortEnv}
    {context : GeneralBodyContext}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {condition : LF.GeneralExpr}
    {compiledThen compiledElse : LF.GeneralBody}
    (hStatement :
      compileGeneralStmt
          env
          context
          index
          statement =
        .ok
          (.ifThenElse
            condition
            compiledThen
            compiledElse)) :
    ∃ (sourceCondition : DTR.GeneralExpr)
      (thenBody elseBody : DTR.GeneralBody),
      statement =
        .ifThenElse
          sourceCondition
          thenBody
          elseBody ∧
      compileGeneralBody
          env
          {
            bodyKey :=
              context.bodyKey

            selfSends :=
              context.selfSends

            levelPath :=
              context.levelPath ++
                [index, 0]
          }
          0
          thenBody =
        .ok compiledThen ∧
      compileGeneralBody
          env
          {
            bodyKey :=
              context.bodyKey

            selfSends :=
              context.selfSends

            levelPath :=
              context.levelPath ++
                [index, 1]
          }
          0
          elseBody =
        .ok compiledElse := by

  cases statement with

  | assign target value =>
      simp [
        compileGeneralStmt
      ] at hStatement

  | trace tag =>
      simp [
        compileGeneralStmt
      ] at hStatement

  | send target message sendArguments delay =>

      cases target with

      | selfTarget =>
          simp [
            compileGeneralStmt
          ] at hStatement

      | knownRebec rebec =>

          cases hEntry :
              generalEntryAtSite?
                env
                {
                  body :=
                    context.bodyKey

                  index :=
                    context.levelPath ++
                      [index]
                } with

          | none =>
              simp [
                compileGeneralStmt,
                hEntry
              ] at hStatement

          | some entry =>
              simp [
                compileGeneralStmt,
                hEntry
              ] at hStatement

  | localDecl _ _ _ =>
      -- A compiled local declaration is `.ok localDecl`, never `.ok ifThenElse`, so
      -- this arm is discharged from `hStatement` alone: the two constructors differ.
      -- The `cases` on the declared type that stood here during stage I's refusal
      -- period is dead now that the arm compiles, for the reason recorded on the
      -- setPort inversion's own localDecl arm above.
      simp [
        compileGeneralStmt
      ] at hStatement

  | ifThenElse sourceCondition thenBody elseBody =>

      cases hThen :
          compileGeneralBody
            env
            {
              bodyKey :=
                context.bodyKey

              selfSends :=
                context.selfSends

              levelPath :=
                context.levelPath ++
                  [index, 0]
            }
            0
            thenBody with

      | error message =>
          simp [
            compileGeneralStmt,
            hThen
          ] at hStatement

      | ok compiledThenBody =>

          cases hElse :
              compileGeneralBody
                env
                {
                  bodyKey :=
                    context.bodyKey

                  selfSends :=
                    context.selfSends

                  levelPath :=
                    context.levelPath ++
                      [index, 1]
                }
                0
                elseBody with

          | error message =>
              simp [
                compileGeneralStmt,
                hThen,
                hElse
              ] at hStatement

          | ok compiledElseBody =>

              simp only [
                compileGeneralStmt,
                hThen,
                hElse,
                Except.ok.injEq,
                LF.GeneralStmt.ifThenElse.injEq
              ] at hStatement

              exact
                ⟨sourceCondition,
                 thenBody,
                 elseBody,
                 rfl,
                 hThen.trans
                   (by
                     rw [hStatement.right.left]),
                 hElse.trans
                   (by
                     rw [hStatement.right.right])⟩

/--
Every port a compiled body sets was put there by a routing entry at some site of this body,
at or after the index the compilation started from.

The `index ≤ site` half is what makes this usable for a `Nodup` argument and it is the reason
the lemma is phrased over a *suffix* rather than a whole body. Walking `compileGeneralBody`'s
recursion, the head statement is at `index` and everything the tail contributes comes from
`index + 1` or later; so a port set by the head cannot also be set by the tail unless two
distinct sites carry one port name. That is exactly the hypothesis the theorem below takes,
and exactly what F48's model denies.

**Stage H split the address into `site` and `rest`, and kept `index ≤ site` on a `Nat`.** A port
set inside a conditional lives at `context.levelPath ++ (site :: rest)` where `site` is the
*conditional's* position in this level and `rest` records the branch and the position inside it.
For a branch-free body `rest` is `[]` and this statement is stage E's, character for character in
its arithmetic: the ordering fact stayed a `Nat` comparison rather than becoming a prefix
relation, because what the `Nodup` argument below needs is that the head and the tail differ in
the component at *this* level, and nesting below that component cannot change it.

**The recursion is explicit rather than by `induction`**, for the same reason as
`exists_compileGeneralBody`: the conditional case applies this statement to the two branch
bodies, each at its own level, and a list induction offers no hypothesis for either.
-/
private theorem compileGeneralBody_setPortNames_provenance
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext) :
    ∀ (statements : DTR.GeneralBody)
      (index : Nat)
      (compiled : LF.GeneralBody),
      compileGeneralBody
          env
          context
          index
          statements =
        .ok compiled →
      ∀ (port : PortName),
        port ∈
          LF.setPortNamesOfBody
            compiled →
        ∃ (site : Nat)
          (rest : List Nat)
          (entry : GeneralOutputPortEntry),
          index ≤ site ∧
          generalEntryAtSite?
              env
              {
                body :=
                  context.bodyKey

                index :=
                  context.levelPath ++
                    (site :: rest)
              } =
            some entry ∧
          entry.outputPort = port := by

  intro statements

  cases statements with

  | nil =>
      intro index compiled hCompiled port hPort

      rw [
        compileGeneralBody_nil
      ] at hCompiled

      injection hCompiled with hEqual

      subst hEqual

      simp [
        LF.setPortNamesOfBody
      ] at hPort

  | cons statement remaining =>
      intro index compiled hCompiled port hPort

      obtain
          ⟨compiledStatement,
           compiledRemaining,
           hStatement,
           hRemaining,
           hShape⟩ :=
        compileGeneralBody_cons_ok_inversion
          hCompiled

      subst hShape

      cases compiledStatement with

      | assign _ _ =>

          simp only [
            LF.setPortNamesOfBody_assign
          ] at hPort

          obtain ⟨site, rest, entry, hSite, hEntry, hPortName⟩ :=
            compileGeneralBody_setPortNames_provenance
              env
              context
              remaining
              (index + 1)
              compiledRemaining
              hRemaining
              port
              hPort

          exact
            ⟨site,
             rest,
             entry,
             by omega,
             hEntry,
             hPortName⟩

      | trace _ =>

          simp only [
            LF.setPortNamesOfBody_trace
          ] at hPort

          obtain ⟨site, rest, entry, hSite, hEntry, hPortName⟩ :=
            compileGeneralBody_setPortNames_provenance
              env
              context
              remaining
              (index + 1)
              compiledRemaining
              hRemaining
              port
              hPort

          exact
            ⟨site,
             rest,
             entry,
             by omega,
             hEntry,
             hPortName⟩

      | schedule _ _ _ =>

          simp only [
            LF.setPortNamesOfBody_schedule
          ] at hPort

          obtain ⟨site, rest, entry, hSite, hEntry, hPortName⟩ :=
            compileGeneralBody_setPortNames_provenance
              env
              context
              remaining
              (index + 1)
              compiledRemaining
              hRemaining
              port
              hPort

          exact
            ⟨site,
             rest,
             entry,
             by omega,
             hEntry,
             hPortName⟩

      | setPort statementPort _ =>

          simp only [
            LF.setPortNamesOfBody_setPort,
            List.mem_cons
          ] at hPort

          cases hPort with

          | inl hHere =>

              obtain ⟨entry, hEntry, hPortName⟩ :=
                compileGeneralStmt_setPort_inversion
                  hStatement

              exact
                ⟨index,
                 [],
                 entry,
                 by omega,
                 hEntry,
                 hPortName.trans
                   hHere.symm⟩

          | inr hThere =>

              obtain ⟨site, rest, entry, hSite, hEntry, hPortName⟩ :=
                compileGeneralBody_setPortNames_provenance
                  env
                  context
                  remaining
                  (index + 1)
                  compiledRemaining
                  hRemaining
                  port
                  hThere

              exact
                ⟨site,
                 rest,
                 entry,
                 by omega,
                 hEntry,
                 hPortName⟩

      | ifThenElse _ compiledThen compiledElse =>

          obtain
              ⟨sourceCondition,
               thenBody,
               elseBody,
               hSource,
               hThen,
               hElse⟩ :=
            compileGeneralStmt_ifThenElse_inversion
              hStatement

          simp only [
            LF.setPortNamesOfBody_ifThenElse,
            List.mem_append
          ] at hPort

          -- `++` is left-associative, so the three lists nest as
          -- `(then ++ else) ++ remaining` and the outer split separates the
          -- conditional's own ports from the enclosing level's.
          cases hPort with

          | inl hBranchPort =>

              cases hBranchPort with

              | inl hThenPort =>

                  obtain ⟨site, rest, entry, _, hEntry, hPortName⟩ :=
                    compileGeneralBody_setPortNames_provenance
                      env
                      {
                        bodyKey :=
                          context.bodyKey

                        selfSends :=
                          context.selfSends

                        levelPath :=
                          context.levelPath ++
                            [index, 0]
                      }
                      thenBody
                      0
                      compiledThen
                      hThen
                      port
                      hThenPort

                  refine
                    ⟨index,
                     0 :: site :: rest,
                     entry,
                     by omega,
                     ?_,
                     hPortName⟩

                  simpa using hEntry

              | inr hElsePort =>

                  obtain ⟨site, rest, entry, _, hEntry, hPortName⟩ :=
                    compileGeneralBody_setPortNames_provenance
                      env
                      {
                        bodyKey :=
                          context.bodyKey

                        selfSends :=
                          context.selfSends

                        levelPath :=
                          context.levelPath ++
                            [index, 1]
                      }
                      elseBody
                      0
                      compiledElse
                      hElse
                      port
                      hElsePort

                  refine
                    ⟨index,
                     1 :: site :: rest,
                     entry,
                     by omega,
                     ?_,
                     hPortName⟩

                  simpa using hEntry

          | inr hThere =>

              obtain ⟨site, rest, entry, hSite, hEntry, hPortName⟩ :=
                compileGeneralBody_setPortNames_provenance
                  env
                  context
                  remaining
                  (index + 1)
                  compiledRemaining
                  hRemaining
                  port
                  hThere

              exact
                ⟨site,
                 rest,
                 entry,
                 by omega,
                 hEntry,
                 hPortName⟩

      | localDecl name declaredType value =>

          -- A declaration contributes no port, so the body's port list is the tail's
          -- and the witness is the tail's, exactly as for `assign`. The source-cased
          -- contradiction block that stood here during stage I's refusal period — the
          -- one that cost the most to write, because casing the compiled type proves
          -- nothing about the source arm — collapsed into this when the compile arm
          -- arrived, and the nodup theorem's own localDecl arm below kept the same
          -- shape throughout, which is why it needed no change here.
          simp only [
            LF.setPortNamesOfBody_localDecl
          ] at hPort

          obtain ⟨site, rest, entry, hSite, hEntry, hPortName⟩ :=
            compileGeneralBody_setPortNames_provenance
              env
              context
              remaining
              (index + 1)
              compiledRemaining
              hRemaining
              port
              hPort

          exact
            ⟨site,
             rest,
             entry,
             by omega,
             hEntry,
             hPortName⟩

/--
§10.2's theorem, in the strongest form that is true: **if** the routing table gives distinct
sites of one body distinct output port names, **then** no compiled reaction body sets one
output port twice.

`docs/STAGE_E_DESIGN.md` §10.2 asks for the unconditional sentence — *"no reaction of an
emitted reactor sets one output port twice"* — and argues it *"follows from the site being an
address (§7.1): two `setPort`s in one compiled body come from two statements at two indices of
one body, so their sites differ, so `outputPortEnvOf` gave them different port names **or
refused**."*

**The inference does not go through, and the hypothesis below is exactly the step it skips.**
Sites differing is the premise, not the conclusion: `outputPortNameFor` concatenates message,
`To`, capitalized known rebec and site suffix without escaping the separator, so two distinct
sites can be handed distinct arguments and still produce one name (F34). The `or refused`
hedge does not rescue the argument either, because the refusal is a check on the *assembled
program*, and F48's model reaches assembly — it routes and compiles, which is what makes it a
witness at all. Finding F50 records the refutation and
`ALIASED_SETPORT_TWICE_IN_ONE_REACTION` in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`
is the witness that a single emitted reaction really does set one port twice.

So the property is *guard-relative*, in the same way and for the same reason as
`assembleGeneralProgram_targetEndpointsUnique`: what earns it is a check on generated names,
never the naming rule. The hypothesis is stated over sites of one `bodyKey` rather than as
`Nodup` of the whole environment's port names, because that is all the induction consumes and
it is the form a caller holding a per-class guard can actually supply.

**Stage H moved the hypothesis from index pairs to path pairs, and that is a generalisation
rather than a weakening.** Sites are `List Nat` now, and a conditional puts ports at paths of
every depth, so a premise quantified over `Nat` pairs would say nothing about them. Restricted to
paths of the form `[n]` the premise is exactly the one stage E stated, and the conclusion now
covers bodies with branches, which stage E's could not. Nothing about the guard-relativity
changes: what earns the property is still a check on generated names.

**The two ways one emitted reaction can now set one port twice are worth separating.** The first
is F50's: two *distinct* sites handed distinct arguments that concatenate to one name, which this
hypothesis rules out and no naming rule does. The second is stage H's own, and it is not a defect
in the naming: a port set in the then-branch and again in the else-branch appears twice in
`LF.setPortNamesOfBody` even though at most one arm runs, because
`docs/decisions/0046-send-site-identity-under-nested-control-flow.md` and the port ruling of
2026-09-03 keep that list a property of the compiled artefact rather than of a run. Those two
sites are distinct paths, so this theorem's conclusion still holds of them: the two branch ports
are *different* ports with different names, and it is a source that sets one known rebec's message
from both arms that is refused a single shared port, not this theorem that bends.
-/
theorem compileGeneralBody_setPortNames_nodup
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext)
    (hDistinctSites :
      ∀ (pathLeft pathRight : List Nat)
        (entryLeft entryRight : GeneralOutputPortEntry),
        generalEntryAtSite?
            env
            {
              body :=
                context.bodyKey

              index :=
                pathLeft
            } =
          some entryLeft →
        generalEntryAtSite?
            env
            {
              body :=
                context.bodyKey

              index :=
                pathRight
            } =
          some entryRight →
        entryLeft.outputPort = entryRight.outputPort →
          pathLeft = pathRight) :
    ∀ (statements : DTR.GeneralBody)
      (index : Nat)
      (compiled : LF.GeneralBody),
      compileGeneralBody
          env
          context
          index
          statements =
        .ok compiled →
      (LF.setPortNamesOfBody
        compiled).Nodup := by

  intro statements

  cases statements with

  | nil =>
      intro index compiled hCompiled

      rw [
        compileGeneralBody_nil
      ] at hCompiled

      injection hCompiled with hEqual

      subst hEqual

      simp [
        LF.setPortNamesOfBody
      ]

  | cons statement remaining =>
      intro index compiled hCompiled

      obtain
          ⟨compiledStatement,
           compiledRemaining,
           hStatement,
           hRemaining,
           hShape⟩ :=
        compileGeneralBody_cons_ok_inversion
          hCompiled

      subst hShape

      cases compiledStatement with

      | assign _ _ =>
          simp only [
            LF.setPortNamesOfBody_assign
          ]

          exact
            compileGeneralBody_setPortNames_nodup
              env
              context
              hDistinctSites
              remaining
              (index + 1)
              compiledRemaining
              hRemaining

      | trace _ =>
          simp only [
            LF.setPortNamesOfBody_trace
          ]

          exact
            compileGeneralBody_setPortNames_nodup
              env
              context
              hDistinctSites
              remaining
              (index + 1)
              compiledRemaining
              hRemaining

      | schedule _ _ _ =>
          simp only [
            LF.setPortNamesOfBody_schedule
          ]

          exact
            compileGeneralBody_setPortNames_nodup
              env
              context
              hDistinctSites
              remaining
              (index + 1)
              compiledRemaining
              hRemaining

      | setPort statementPort _ =>
          simp only [
            LF.setPortNamesOfBody_setPort
          ]

          constructor

          · intro other hOther hEqual

            have hMember :
                statementPort ∈
                  LF.setPortNamesOfBody
                    compiledRemaining := by
              rw [hEqual]
              exact hOther

            obtain
                ⟨site,
                 rest,
                 entry,
                 hSite,
                 hEntry,
                 hPortName⟩ :=
              compileGeneralBody_setPortNames_provenance
                env
                context
                remaining
                (index + 1)
                compiledRemaining
                hRemaining
                statementPort
                hMember

            obtain
                ⟨headEntry,
                 hHeadEntry,
                 hHeadPortName⟩ :=
              compileGeneralStmt_setPort_inversion
                hStatement

            have hSame :
                context.levelPath ++
                    (site :: rest) =
                  context.levelPath ++
                    [index] :=
              hDistinctSites
                (context.levelPath ++
                  (site :: rest))
                (context.levelPath ++
                  [index])
                entry
                headEntry
                hEntry
                hHeadEntry
                (hPortName.trans
                  hHeadPortName.symm)

            have hCons :
                site :: rest =
                  [index] :=
              List.append_cancel_left
                hSame

            injection hCons with hSiteEqual _

            omega

          · exact
              compileGeneralBody_setPortNames_nodup
                env
                context
                hDistinctSites
                remaining
                (index + 1)
                compiledRemaining
                hRemaining

      | ifThenElse _ compiledThen compiledElse =>

          obtain
              ⟨sourceCondition,
               thenBody,
               elseBody,
               hSource,
               hThen,
               hElse⟩ :=
            compileGeneralStmt_ifThenElse_inversion
              hStatement

          simp only [
            LF.setPortNamesOfBody_ifThenElse,
            List.nodup_append
          ]

          -- `++` is left-associative, so `List.nodup_append` splits
          -- `(then ++ else) ++ remaining` into the conditional's two branches, the
          -- enclosing level, and two disjointness obligations: between the branches,
          -- and between the conditional and everything after it.
          refine
            ⟨⟨compileGeneralBody_setPortNames_nodup
                env
                {
                  bodyKey :=
                    context.bodyKey

                  selfSends :=
                    context.selfSends

                  levelPath :=
                    context.levelPath ++
                      [index, 0]
                }
                hDistinctSites
                thenBody
                0
                compiledThen
                hThen,
              compileGeneralBody_setPortNames_nodup
                env
                {
                  bodyKey :=
                    context.bodyKey

                  selfSends :=
                    context.selfSends

                  levelPath :=
                    context.levelPath ++
                      [index, 1]
                }
                hDistinctSites
                elseBody
                0
                compiledElse
                hElse,
              ?_⟩,
             compileGeneralBody_setPortNames_nodup
               env
               context
               hDistinctSites
               remaining
               (index + 1)
               compiledRemaining
               hRemaining,
             ?_⟩

          -- The then-branch's ports against the else-branch's. Their paths agree down to
          -- this level's position and differ in the side component, `0` against `1`,
          -- which is exactly what the alternating encoding buys.
          · intro thenPort hThenPort elsePort hElsePort hEqualPorts

            obtain
                ⟨thenSite,
                 thenRest,
                 thenEntry,
                 _,
                 hThenEntry,
                 hThenPortName⟩ :=
              compileGeneralBody_setPortNames_provenance
                env
                {
                  bodyKey :=
                    context.bodyKey

                  selfSends :=
                    context.selfSends

                  levelPath :=
                    context.levelPath ++
                      [index, 0]
                }
                thenBody
                0
                compiledThen
                hThen
                thenPort
                hThenPort

            obtain
                ⟨elseSite,
                 elseRest,
                 elseEntry,
                 _,
                 hElseEntry,
                 hElsePortName⟩ :=
              compileGeneralBody_setPortNames_provenance
                env
                {
                  bodyKey :=
                    context.bodyKey

                  selfSends :=
                    context.selfSends

                  levelPath :=
                    context.levelPath ++
                      [index, 1]
                }
                elseBody
                0
                compiledElse
                hElse
                elsePort
                hElsePort

            have hSame :
                context.levelPath ++
                    (index ::
                      0 ::
                        thenSite ::
                          thenRest) =
                  context.levelPath ++
                    (index ::
                      1 ::
                        elseSite ::
                          elseRest) :=
              hDistinctSites
                (context.levelPath ++
                  (index ::
                    0 ::
                      thenSite ::
                        thenRest))
                (context.levelPath ++
                  (index ::
                    1 ::
                      elseSite ::
                        elseRest))
                thenEntry
                elseEntry
                (by
                  simpa using hThenEntry)
                (by
                  simpa using hElseEntry)
                (hThenPortName.trans
                  (hEqualPorts.trans
                    hElsePortName.symm))

            have hCons :
                index ::
                    0 ::
                      thenSite ::
                        thenRest =
                  index ::
                    1 ::
                      elseSite ::
                        elseRest :=
              List.append_cancel_left
                hSame

            simp at hCons

          -- The conditional's ports, from either branch, against the enclosing level's.
          -- Both branch paths carry `index` at this level's position and every later
          -- statement's carries `index + 1` or more.
          · intro branchPort hBranchPort tailPort hTailPort hEqualPorts

            obtain
                ⟨tailSite,
                 tailRest,
                 tailEntry,
                 hTailSite,
                 hTailEntry,
                 hTailPortName⟩ :=
              compileGeneralBody_setPortNames_provenance
                env
                context
                remaining
                (index + 1)
                compiledRemaining
                hRemaining
                tailPort
                hTailPort

            rw [
              List.mem_append
            ] at hBranchPort

            cases hBranchPort with

            | inl hThenPort =>

                obtain
                    ⟨thenSite,
                     thenRest,
                     thenEntry,
                     _,
                     hThenEntry,
                     hThenPortName⟩ :=
                  compileGeneralBody_setPortNames_provenance
                    env
                    {
                      bodyKey :=
                        context.bodyKey

                      selfSends :=
                        context.selfSends

                      levelPath :=
                        context.levelPath ++
                          [index, 0]
                    }
                    thenBody
                    0
                    compiledThen
                    hThen
                    branchPort
                    hThenPort

                have hSame :
                    context.levelPath ++
                        (index ::
                          0 ::
                            thenSite ::
                              thenRest) =
                      context.levelPath ++
                        (tailSite ::
                          tailRest) :=
                  hDistinctSites
                    (context.levelPath ++
                      (index ::
                        0 ::
                          thenSite ::
                            thenRest))
                    (context.levelPath ++
                      (tailSite ::
                        tailRest))
                    thenEntry
                    tailEntry
                    (by
                      simpa using hThenEntry)
                    hTailEntry
                    (hThenPortName.trans
                      (hEqualPorts.trans
                        hTailPortName.symm))

                have hCons :
                    index ::
                        0 ::
                          thenSite ::
                            thenRest =
                      tailSite ::
                        tailRest :=
                  List.append_cancel_left
                    hSame

                injection hCons with hSiteEqual _

                omega

            | inr hElsePort =>

                obtain
                    ⟨elseSite,
                     elseRest,
                     elseEntry,
                     _,
                     hElseEntry,
                     hElsePortName⟩ :=
                  compileGeneralBody_setPortNames_provenance
                    env
                    {
                      bodyKey :=
                        context.bodyKey

                      selfSends :=
                        context.selfSends

                      levelPath :=
                        context.levelPath ++
                          [index, 1]
                    }
                    elseBody
                    0
                    compiledElse
                    hElse
                    branchPort
                    hElsePort

                have hSame :
                    context.levelPath ++
                        (index ::
                          1 ::
                            elseSite ::
                              elseRest) =
                      context.levelPath ++
                        (tailSite ::
                          tailRest) :=
                  hDistinctSites
                    (context.levelPath ++
                      (index ::
                        1 ::
                          elseSite ::
                            elseRest))
                    (context.levelPath ++
                      (tailSite ::
                        tailRest))
                    elseEntry
                    tailEntry
                    (by
                      simpa using hElseEntry)
                    hTailEntry
                    (hElsePortName.trans
                      (hEqualPorts.trans
                        hTailPortName.symm))

                have hCons :
                    index ::
                        1 ::
                          elseSite ::
                            elseRest =
                      tailSite ::
                        tailRest :=
                  List.append_cancel_left
                    hSame

                injection hCons with hSiteEqual _

                omega

      | localDecl _ _ _ =>
          -- A declaration contributes no port, so the body's port list is the tail's and
          -- its `Nodup` is the recursive call. Written in the post-S-I3 shape rather than
          -- discharged from `hStatement`'s contradiction, so the arm survives the layer
          -- that starts compiling local declarations unchanged.
          simp only [
            LF.setPortNamesOfBody_localDecl
          ]

          exact
            compileGeneralBody_setPortNames_nodup
              env
              context
              hDistinctSites
              remaining
              (index + 1)
              compiledRemaining
              hRemaining

/-!
## §8 revisited: where each refusal lives

`docs/STAGE_E_DESIGN.md` §8 asks, as its second owed statement, for a decidable predicate over DTR
models that implies acceptance. That statement is **false as worded**, and the empty model refutes
it, which is finding **F52**: `⟨[], []⟩` satisfies all three conjuncts §8 names and is still
refused, because the guard requires a reactor and an instance.

What the section's own *title* asks for is available, and this is where it is proved. Acceptance
factors into exactly three conditions — routing resolves, every class's port environment resolves,
and the guard passes — and **nothing between them can fail**. That last clause is what the site
totality of the preceding section buys: it is why the middle stage appears in the statement below
only as a way to name the reactors, and never as something a caller has to show succeeds.

This replaces stage D's `compileGeneralModel_ok_iff_selfSendOnly`, which stage E deleted when
self-sends stopped being the only translatable shape. It is stronger than the sufficient condition
§8 asked for, being a biconditional, and it is honest about the guard rather than silent on it: the
third condition is stated on the assembled program, so the F37 weakening is visible in the statement
instead of hidden behind it.
-/

/--
Inversion for one class: if a class compiled, its port environment resolved.

The converse of `compileGeneralReactiveClass_ok`, and it holds for a structural reason rather than a
semantic one. `compileGeneralReactiveClass` matches on `outputPortEnvOf` first and propagates its
refusal unchanged — which is what `compileGeneralReactiveClass_error_env` records — so an `.ok`
result cannot have been reached through a failing environment.
-/
theorem compileGeneralReactiveClass_ok_env
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {compiled : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok compiled) :
    ∃ env,
      outputPortEnvOf
          classes
          reactiveClass =
        .ok env := by
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
      exact ⟨env, rfl⟩

/--
Inversion for a list of classes: if the list compiled, every class in it resolved.

The mirror of `exists_compileGeneralReactiveClasses`, and stated the same way — hypothesis as an
arrow, class table a separate parameter from the traversed list — so that the two compose into a
biconditional without either being reshaped at the use site. The induction needs only the two
propagation lemmas: a head refusal and a tail refusal each refuse the whole list, so an `.ok` list
rules both out.
-/
theorem compileGeneralReactiveClasses_ok_env
    (allClasses : List DTR.GeneralReactiveClass)
    (routes : List GeneralRoute)
    (classList : List DTR.GeneralReactiveClass) :
    (∃ compiled,
        compileGeneralReactiveClasses
            allClasses
            routes
            classList =
          .ok compiled) →
    ∀ reactiveClass ∈ classList,
      ∃ env,
        outputPortEnvOf
            allClasses
            reactiveClass =
          .ok env := by
  induction classList with
  | nil =>
      intro _ reactiveClass hMember
      simp at hMember
  | cons head remaining inductionHypothesis =>
      intro hCompiled reactiveClass hMember
      obtain ⟨compiled, hCompiled⟩ := hCompiled
      cases hHead :
          compileGeneralReactiveClass
            allClasses
            routes
            head with
      | error message =>
          rw [
            compileGeneralReactiveClasses_cons_error_head
              hHead
          ] at hCompiled
          simp at hCompiled
      | ok compiledHead =>
          cases hRemaining :
              compileGeneralReactiveClasses
                allClasses
                routes
                remaining with
          | error message =>
              rw [
                compileGeneralReactiveClasses_cons_error_tail
                  hHead
                  hRemaining
              ] at hCompiled
              simp at hCompiled
          | ok compiledRemaining =>
              rcases List.mem_cons.mp hMember with
                hHeadCase | hTailCase
              · subst hHeadCase
                exact
                  compileGeneralReactiveClass_ok_env
                    hHead
              · exact
                  inductionHypothesis
                    ⟨compiledRemaining, hRemaining⟩
                    reactiveClass
                    hTailCase

/--
Acceptance, factored: routing, resolution, guard — and nothing in between.

The theorem `docs/STAGE_E_DESIGN.md` §8 should have asked for, in place of the predicate finding F52
refutes. Read left to right it localises every refusal `compileGeneralModel` can produce to one of
two sites: either `routesOf` refused, or some class's `outputPortEnvOf` refused, or the assembled
program failed the guard. Read right to left it says those three are jointly sufficient.

The middle stage is absent from the right-hand side as an obligation and present only as a binder,
and that asymmetry is the content. `exists_compileGeneralReactiveClasses` says a resolved
environment is all class compilation ever needs, so no caller has to show it succeeds, while
`compileGeneralReactiveClasses_ok_env` says nothing else could have made it succeed. Everything
between resolution and the guard is total, which is what the site-totality induction was for.

What this does **not** say is that a model in the paper's DTR fragment is accepted. The third
condition is a hypothesis about the translation's own output rather than a property of the source,
and F32/F43 exhibit a legal DTR model whose assembled program fails the guard. Nor can that
condition be decided from the source by inspection, because collision of generated names is not a
syntactic property of a model (F34, F42). The gap is named here rather than papered over: no
sufficient condition for acceptance can omit the guard.
-/
theorem compileGeneralModel_ok_iff
    (model : DTR.GeneralModel) :
    (∃ program,
        compileGeneralModel model =
          .ok program) ↔
      ∃ routes,
        routesOf model =
            .ok routes ∧
          (∀ reactiveClass ∈ model.classes,
              ∃ env,
                outputPortEnvOf
                    model.classes
                    reactiveClass =
                  .ok env) ∧
            ∀ compiledReactors,
              compileGeneralReactiveClasses
                    model.classes
                    routes
                    model.classes =
                  .ok compiledReactors →
                (assembleGeneralProgram
                    model
                    routes
                    compiledReactors).wellFormed =
                  true := by
  constructor

  · intro hAccepted
    obtain ⟨program, hProgram⟩ := hAccepted
    cases hRoutes :
        routesOf model with
    | error message =>
        rw [
          compileGeneralModel_error_routes
            hRoutes
        ] at hProgram
        simp at hProgram
    | ok routes =>
        refine
          ⟨routes,
           rfl,
           ?_,
           ?_⟩

        · cases hClasses :
              compileGeneralReactiveClasses
                model.classes
                routes
                model.classes with
          | error message =>
              rw [
                compileGeneralModel_error_classes
                  hRoutes
                  hClasses
              ] at hProgram
              simp at hProgram
          | ok compiledReactors =>
              exact
                compileGeneralReactiveClasses_ok_env
                  model.classes
                  routes
                  model.classes
                  ⟨compiledReactors, hClasses⟩

        · intro compiledReactors hClasses
          rw [
            compileGeneralModel_ok
              hRoutes
              hClasses
          ] at hProgram
          exact
            guardGeneralProgram_wellFormed
              hProgram

  · intro hFactored
    obtain
        ⟨routes,
         hRoutes,
         hEnvironments,
         hGuard⟩ :=
      hFactored
    obtain ⟨compiledReactors, hClasses⟩ :=
      exists_compileGeneralReactiveClasses
        model.classes
        routes
        model.classes
        hEnvironments
    refine
      ⟨assembleGeneralProgram
         model
         routes
         compiledReactors,
       ?_⟩
    rw [
      compileGeneralModel_ok
        hRoutes
        hClasses
    ]
    exact
      guardGeneralProgram_of_wellFormed
        (hGuard
          compiledReactors
          hClasses)

/-!
## Instance-declaration order

`docs/STAGE_E_DESIGN.md` §10.2's fourth owed item, composite half. The routing half is
`routesOf_split` in `Relico/Translation/GeneralRouting.lean`; what this section adds is the step
from a split routing table to a split group of reactions, and the statement that puts the two
together.
-/

/--
One message server's port reactions split wherever the route list splits.

Immediate from `generalRoutesIntoMessageServer_append` and `List.map_append`, because
`assembleGeneralPortReactions` is a `map` over the filter and nothing else. Stated for an arbitrary
class, server and compiled body: if no route in either half lands on this server the two sides are
both empty and the equation is the empty split, which is the honest content in that case rather than
a degenerate one to be excluded by hypothesis.
-/
theorem assembleGeneralPortReactions_append
    (className : ClassName)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody)
    (earlierRoutes laterRoutes : List GeneralRoute) :
    assembleGeneralPortReactions
        className
        server
        compiledBody
        (earlierRoutes ++ laterRoutes) =
      assembleGeneralPortReactions
          className
          server
          compiledBody
          earlierRoutes ++
        assembleGeneralPortReactions
          className
          server
          compiledBody
          laterRoutes := by

  simp [
    assembleGeneralPortReactions,
    generalRoutesIntoMessageServer_append
  ]

/--
A receiver's port reactions for one message server appear in the order the translation walks the main
block, which since stage F is **actor-priority order, ties broken by main-block declaration order**.

`docs/STAGE_E_DESIGN.md` §10.2 owes this statement explicitly, and this is it. Read the hypothesis
`priorityOrderedInstances model = earlier ++ later` as a cut anywhere in the walked instance list: the
first conjunct says the routing table splits at that cut, the second says the group of port reactions
for any one message server splits at the same point. Together they say that every reaction owed to an
instance walked earlier precedes every reaction owed to one walked later, for every cut, which is what
"in this order" means without a list-order API.

**The hypothesis was re-keyed when stage F landed, and the two conjuncts had different fates.** It
previously read `model.instances = earlier ++ later`, which was the same list while nothing sorted.
`routesOf` now routes `priorityOrderedInstances model`, so a split of the *declared* list no longer
implies a split of the table — a sort does not distribute over an arbitrary append — while a split of
the walked list does. Conjunct 2 never mentioned a model and was unaffected: it says only that port
reaction assembly distributes over append, i.e. that it is order-preserving, and it is what makes this
theorem composable with the sort at all. `docs/STAGE_F_DESIGN.md` §7.1 and §7.2 record the reasoning
and the count of declarations that alternative choices would have cost.

**This statement carries the structural half of the priority claim, not the claim itself.** The
distinction is worth stating precisely rather than modestly, because the two halves of it point in
opposite directions. Reaction declaration order is genuinely observable in the target: within *one*
reactor it totally orders the reactions enabled at the same tag, measured rather than assumed, and
every port reaction this statement is about belongs to the single receiving reactor.
`docs/PAPER_CORRECTIONS.md` P1 is the boundary that makes the qualifier load-bearing — *across* reactors
the order comes from the dependency graph the connections induce and not from declaration order at all,
so a statement of this shape would be unsound if it reached across reactors. This one does not.

What is *not* here is the step from "splits at every cut of the walked list" to "realizes the sending
actors' priority order". That step needs the sort's own ordering property and lives in
`Relico/Correctness/GeneralPriorityOrder.lean`, exactly as
`priorityServerNamePrecedesOrEqual_compileMessageReactions` in `Relico/Correctness/PriorityOrder.lean`
composes the restricted family's order-preservation lemma with `MessageServerPriority.normalize`. The
contrast with that family is now one of scope rather than of kind: it sorts message servers inside one
actor, this stage sorts sending actors across the main block.

**One half of the paper's ask is still open at this commit.** Level 1 (§III-D, ordering a server's port
reactions by the sending actor's priority) is what `priorityOrderedInstances` delivers.
`DTR.GeneralMessageServer.priority` is still dropped, so the per-server *groups* are still emitted in
source order; that is level 2, and it is owed at the walk inside `compileGeneralReactiveClass`.
`assembleGeneralMessageReaction_priority` continues to record that `LF.GeneralReaction.priority` is left
unset, which stays true at both levels because the printer never reads that field — list order is the
only mechanism the target offers.

Two further things this statement deliberately does not say. It says nothing about the order of the
action reaction relative to the port reactions — that is `compileGeneralMessageServerReactions`'s
concern and §7.3's order, covered separately. And it says nothing about port *names*: names are
guard-relative in this stage (F34, F37, F42), whereas order is carried by the construction here, and
conflating the two is the defect finding F53 records three instances of.
-/
theorem assembleGeneralPortReactions_instanceDeclarationOrder
    (model : DTR.GeneralModel)
    (earlier later : List DTR.GeneralActorInstance)
    (earlierRoutes laterRoutes : List GeneralRoute)
    (className : ClassName)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody)
    (hInstances :
      priorityOrderedInstances
          model =
        earlier ++ later)
    (hEarlier :
      routesOfInstances
          model
          earlier =
        .ok earlierRoutes)
    (hLater :
      routesOfInstances
          model
          later =
        .ok laterRoutes) :
    routesOf model =
        .ok
          (earlierRoutes ++
            laterRoutes) ∧
      assembleGeneralPortReactions
          className
          server
          compiledBody
          (earlierRoutes ++ laterRoutes) =
        assembleGeneralPortReactions
            className
            server
            compiledBody
            earlierRoutes ++
          assembleGeneralPortReactions
            className
            server
            compiledBody
            laterRoutes :=
  ⟨routesOf_split
      model
      earlier
      later
      earlierRoutes
      laterRoutes
      hInstances
      hEarlier
      hLater,
    assembleGeneralPortReactions_append
      className
      server
      compiledBody
      earlierRoutes
      laterRoutes⟩

/-!
## F80's second half — the emitted port reactions carry pairwise distinct triggers

`LF.GeneralProgram.reactionFor?_perm_of_nodup_triggers` (`Relico/LF/GeneralSemantics.lean`) makes
reaction lookup permutation-invariant once the reactions in a list have pairwise distinct triggers.
F80 asks row 8 for the other half — that the translator always produces them distinct — and this
section supplies it for one message server's group of port reactions, **relative to the guard**,
which is the only honest form available.

Unconditionally the claim is false, and the obvious route to it is closed. A port trigger is
`.inputPort (generalInputPortOfRoute route)`, and `generalInputPortOfRoute` is
`inputPortNameFor route.senderInstance route.outputPort`, which F42 (`docs/STAGE_E_FINDINGS.md`)
measured to be **not injective**: `capitalizeName` folds case, so senders `hub` and `Hub` name one
input port, and both spellings are legal Rebeca. What makes the emitted triggers distinct is
therefore not the naming function but the guard — `LF.GeneralReactor.declaredNames` carries the input
port names and `decide (reactor.declaredNames.Nodup)` is a `wellFormed` conjunct, so a colliding
program is **refused** rather than mistranslated. This is the third appearance of the shape F50 and
`#60` gave §10.2's refuted `setPort` obligation: the property is inherited from a decided guard
clause, never claimed by construction.

The hypothesis is taken in the spelling `Translation.generalRouteEndpoints_nodup` already uses —
duplicate freedom of `(generalInputPortsOf className routes).map (fun port => port.name.value)` —
because `inputPortNames_nodup_of_wellFormed` above is exactly the projection that discharges it from
the guard, and `assembleGeneralReactor_inputPorts` above is what identifies a compiled reactor's
input ports with the ports these routes declare.

Scoped to one server's group, for the reason `assembleGeneralPortReactions_names` gives: a
class-level statement would need a flattening combinator over groups, and `List.flatMap` is a core
name this development has twice been burned by trusting. The concatenation across a class's message
servers is in any case a sub-**multiset** of the routes into that class rather than a sub-list of
them, so it needs a permutation argument rather than a stronger version of anything here.
-/

/--
The triggers of one message server's port reactions, in route order.

The trigger analogue of `mapNames_map_assembleGeneralPortReaction`, proved the same way and for the
same reason: `change` names the head on both sides, and the tail is the induction hypothesis under
`List.cons`. No list-map equation is used, so nothing here depends on `List.map_map` or on
`Function.comp` reducing at the point of use.
-/
private theorem mapTriggers_map_assembleGeneralPortReaction
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
            reaction.trigger) =
        routes.map
          (fun candidate =>
            LF.GeneralTrigger.inputPort
              (generalInputPortOfRoute candidate)) := by

  intro routes
  induction routes with

  | nil =>
      rfl

  | cons route remaining inductionHypothesis =>
      change
        LF.GeneralTrigger.inputPort
              (generalInputPortOfRoute route) ::
            (remaining.map
                (fun candidate =>
                  assembleGeneralPortReaction
                    server
                    candidate
                    compiledBody)).map
                (fun reaction =>
                  reaction.trigger) =
          LF.GeneralTrigger.inputPort
              (generalInputPortOfRoute route) ::
            remaining.map
              (fun candidate =>
                LF.GeneralTrigger.inputPort
                  (generalInputPortOfRoute candidate))

      exact
        congrArg
          (List.cons
            (LF.GeneralTrigger.inputPort
              (generalInputPortOfRoute route)))
          inductionHypothesis

/--
Each of one message server's port reactions is triggered by the port its route lands on.

The trigger companion of `assembleGeneralPortReactions_names`, and instantiated the same way: the
private lemma above is stated over an arbitrary route list, and the filter is supplied here.
-/
theorem assembleGeneralPortReactions_triggers
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
          reaction.trigger) =
      (generalRoutesIntoMessageServer
        className
        server.name
        routes).map
        (fun candidate =>
          LF.GeneralTrigger.inputPort
            (generalInputPortOfRoute candidate)) :=
  mapTriggers_map_assembleGeneralPortReaction
    server
    compiledBody
    (generalRoutesIntoMessageServer
      className
      server.name
      routes)

/--
The port names a route list declares are the routes' own port names, in route order.

Stated over an arbitrary list and instantiated below rather than proved by induction on the routes
`generalInputPortsOf` filters, because the recursion that matters is the one over the already
filtered list. The proof is the `mapNames_map_assembleGeneralPortReaction` template a third time; in
particular it is not `List.map_map`, which would leave a `Function.comp` to reduce in the statement
the guard's hypothesis has to match.
-/
private theorem mapPortNames_map_generalInputPortDeclOf :
    ∀ (routes : List GeneralRoute),
      (routes.map
          generalInputPortDeclOf).map
          (fun port =>
            port.name.value) =
        routes.map
          (fun candidate =>
            (generalInputPortOfRoute candidate).value) := by

  intro routes
  induction routes with

  | nil =>
      rfl

  | cons route remaining inductionHypothesis =>
      change
        (generalInputPortOfRoute route).value ::
            (remaining.map
                generalInputPortDeclOf).map
                (fun port =>
                  port.name.value) =
          (generalInputPortOfRoute route).value ::
            remaining.map
              (fun candidate =>
                (generalInputPortOfRoute candidate).value)

      exact
        congrArg
          (List.cons
            ((generalInputPortOfRoute route).value))
          inductionHypothesis

/--
The guard's input-port clause, restated on the routes it came from.

`generalInputPortsOf` is a map of `generalInputPortDeclOf` over the class filter, so this is the
lemma above at that filter. It exists so that the theorem below can consume the hypothesis
`generalRouteEndpoints_nodup` and `inputPortNames_nodup_of_wellFormed` already speak in, without
either of them having to know about triggers.
-/
private theorem generalInputPortsOf_portNames
    (className : ClassName)
    (routes : List GeneralRoute) :
    (generalInputPortsOf
        className
        routes).map
        (fun port =>
          port.name.value) =
      (generalRoutesIntoClass
        className
        routes).map
        (fun candidate =>
          (generalInputPortOfRoute candidate).value) := by

  unfold generalInputPortsOf

  exact
    mapPortNames_map_generalInputPortDeclOf
      (generalRoutesIntoClass
        className
        routes)

/--
One message server's port reactions have pairwise distinct triggers — relative to the guard.

This is the second half of what F80 asks row 8 for. The first half,
`LF.GeneralProgram.reactionFor?_perm_of_nodup_triggers`, says reaction lookup is permutation-invariant
when the reactions in a list have pairwise distinct triggers; this says the translator emits them
distinct.

`hInputPortNames` carries the whole content, and it is deliberately a hypothesis rather than a step
of the proof. It is not provable here and it is not an assumption about the source model: F42
measured `inputPortNameFor` to be non-injective, so two routes into one class really can name one
input port. It is the `decide (reactor.declaredNames.Nodup)` clause of `LF.GeneralReactor.wellFormed`,
projected — `inputPortNames_nodup_of_wellFormed` above does the projection, and
`assembleGeneralReactor_inputPorts` above identifies a compiled reactor's input ports with the ports
these routes declare. So the reading is that a program which would have collided is refused by the
guard, not mistranslated; the composition that turns this into a statement about which reaction fires
is stated where both `LF.GeneralSemantics` and `LF.GeneralWellFormed` are in scope, which this module
is not.

The proof has exactly two steps beyond rewriting. `nodup_map_of_reflecting` carries duplicate freedom
from the `String` names the guard decides up to the triggers, because `PortName.value` is a function
and `LF.GeneralTrigger.inputPort` is a constructor. `generalRoutesIntoMessageServer_nodup_map` then
carries it from the class filter down to the message-server filter, which is the direction the
argument needs and the one an order API is not required for.

Two things this does **not** say, both deliberate. The action reactions
`assembleGeneralMessageReactions` emits are not covered — their triggers are logical actions, and
`LF.GeneralTrigger.matchesKind`'s two cross-constructor `false` cases already make an action trigger
and a port trigger unable to collide with each other, so that side is a separate argument about
`actionNameFor` and `generalActionNameAtSite`, not a stronger version of this one. And the
concatenation across a class's message servers is not covered, for the reason the section header
gives.
-/
theorem assembleGeneralPortReactions_triggers_nodup
    (className : ClassName)
    (server : DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody)
    (routes : List GeneralRoute)
    (hInputPortNames :
      ((generalInputPortsOf
        className
        routes).map
        (fun port =>
          port.name.value)).Nodup) :
    ((assembleGeneralPortReactions
        className
        server
        compiledBody
        routes).map
        (fun reaction =>
          reaction.trigger)).Nodup := by

  rw [
    generalInputPortsOf_portNames
      className
      routes
  ] at hInputPortNames

  have hReflect :
      ∀ (first second : GeneralRoute),
        LF.GeneralTrigger.inputPort
            (generalInputPortOfRoute first) =
          LF.GeneralTrigger.inputPort
            (generalInputPortOfRoute second) →
          (generalInputPortOfRoute first).value =
            (generalInputPortOfRoute second).value := by

    intro first second hTrigger

    simp only [
      LF.GeneralTrigger.inputPort.injEq
    ] at hTrigger

    rw [hTrigger]

  have hClassLevel :
      ((generalRoutesIntoClass
        className
        routes).map
        (fun candidate =>
          LF.GeneralTrigger.inputPort
            (generalInputPortOfRoute candidate))).Nodup :=
    nodup_map_of_reflecting
      (fun candidate =>
        (generalInputPortOfRoute candidate).value)
      (fun candidate =>
        LF.GeneralTrigger.inputPort
          (generalInputPortOfRoute candidate))
      hReflect
      (generalRoutesIntoClass
        className
        routes)
      hInputPortNames

  rw [
    assembleGeneralPortReactions_triggers
      className
      server
      compiledBody
      routes
  ]

  exact
    generalRoutesIntoMessageServer_nodup_map
      (fun candidate =>
        LF.GeneralTrigger.inputPort
          (generalInputPortOfRoute candidate))
      className
      server.name
      routes
      hClassLevel

/-!
## The reactor-level trigger list

`assembleGeneralPortReactions_triggers_nodup` above states distinctness for **one message server's
port-reaction group**. What consumes it —
`LF.GeneralProgram.reactionFor?_perm_of_nodup_triggers` — asks for distinctness of
`reactor.messageReactions.map (fun reaction => reaction.trigger)`, the whole reactor's list. This
section closes that distance, and the shape it takes was forced rather than chosen.

**Why a specification is unavoidable.** The direct route — induct through the `Except` layer proving
`Nodup` of the accumulated reaction list — does not close. `Nodup` of `xs ++ ys` needs `xs` and `ys`
to be individually duplicate-free *and disjoint from each other*, and the disjointness obligation
quantifies over the tail's triggers. An induction hypothesis that says only "the tail is `Nodup`"
cannot discharge it, because it does not say **what** the tail's triggers are. So the aggregation
needs a description of the list, not merely a property of it, and the description has to come first.

**The description mirrors an existing, reviewed one exactly.** `generalReactionNamesOf` and its
three-rung ladder — `compileGeneralMessageServerReactionGroup_names`,
`compileGeneralMessageServerReactions_names`, `compileGeneralReactiveClass_reactionNames` — already
do this for reaction *names*. The four declarations here are the trigger analogue, rung for rung,
and both group-level ingredients were already in the tree: `assembleGeneralMessageReactions_triggers`
for the action half and `assembleGeneralPortReactions_triggers` for the port half. Since
`compileGeneralMessageServerReactionGroup` is literally an append of those two assemblies,
`List.map_append` splits the group-level goal into exactly them.

**Names and triggers are independent, and that is the reason both ladders exist.** The point is
recorded on `assembleGeneralMessageReactions_triggers`: sibling reaction names in one group are
identical by design, so which sibling listens to which action is invisible in names. A `Nodup`
statement about names would therefore be *false* where the trigger statement is true, and neither
ladder can be derived from the other.

**This section adds no runtime assertion, and claims none.** `generalReactionNamesOf` is checked
against emitted output in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`;
`generalMessageReactionTriggersOf` is not, and occurs nowhere outside this file. Proof-only is
therefore the established precedent for the trigger side, and crediting these theorems with gate
coverage they do not have is the shape findings **F45**, **F47** and **F59** each recorded.

Stage F's level-2 sort stays visible in the last rung's right-hand side, for the reason **F60**
gives: a version that pushed the permutation down inside the specification would prove the same
equation while saying nothing about order.
-/

/--
The triggers one class's reactions carry, in the order they are declared.

The trigger counterpart of `generalReactionNamesOf`, and deliberately its exact shape: groups are
**concatenated** rather than consed, because a message server reached from outside contributes more
than one reaction, so the trigger list is longer than the server list exactly when some server is
routed to.

`selfSends`, `routes` and `className` all sit before the colon for the same reason they do there:
none of the three varies in the recursion, and the self-send list belongs to the sending *class*, so
it is fixed for the whole server list.

The port half is written inline rather than given its own definition, again matching
`generalReactionNamesOf`. There is nothing to name: a port reaction's trigger is its input port and
its input port is `generalInputPortOfRoute`, so a wrapper would only restate the `map`. The action
half *does* have a definition, `generalMessageReactionTriggersOf`, because it has real content — the
site list decides how many actions there are and which one each reaction listens to.
-/
def generalReactionTriggersOf
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (className : ClassName) :
    List DTR.GeneralMessageServer →
    List LF.GeneralTrigger

  | [] =>
      []

  | server :: remaining =>
      (generalMessageReactionTriggersOf
            selfSends
            server.name ++
          (generalRoutesIntoMessageServer
            className
            server.name
            routes).map
            (fun route =>
              LF.GeneralTrigger.inputPort
                (generalInputPortOfRoute route))) ++
        generalReactionTriggersOf
          selfSends
          routes
          className
          remaining

/--
One message server's reaction group triggers on its self-send actions first — one per site, in site
order — then on one input port per route into it, in route order.

Rung one, and the group-level half of the aggregation. The division of labour against
`compileGeneralMessageServerReactionGroup_names` is the one the two group ingredients already draw:
that theorem fixes how many reactions there are and what they are called, this one fixes what each
of them listens to.

The proof is the names rung with the two ingredients swapped. `List.map_append` splits the mapped
append, and then the goal is exactly `assembleGeneralMessageReactions_triggers` on the left and
`assembleGeneralPortReactions_triggers` on the right — the second of which is what
`assembleGeneralPortReactions_triggers_nodup` above is stated against, so the two halves of this
section meet at the same spelling rather than at two that need reconciling.

The `Except` inversion is unavoidable: compiling a body can fail, so the group is not a function of
the server alone, and `exists_of_compileGeneralMessageServerReactionGroup_ok` is what turns a
successful compilation back into the append. The compiled body itself is discarded — every reaction
in the group shares it, and no trigger mentions it.
-/
theorem compileGeneralMessageServerReactionGroup_triggers
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
        .ok group) :
    group.map
        (fun reaction =>
          reaction.trigger) =
      generalMessageReactionTriggersOf
          selfSends
          server.name ++
        (generalRoutesIntoMessageServer
          className
          server.name
          routes).map
          (fun route =>
            LF.GeneralTrigger.inputPort
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

  simp [
    List.map_append,
    assembleGeneralMessageReactions_triggers,
    assembleGeneralPortReactions_triggers
  ]

/--
Compiled reactions carry the triggers their message servers specify, groups in the order the server
list gives them.

Rung two. The list is not a `map` of the server list — a body can fail to compile — so the induction
inverts a successful compilation at each step, which is what the two private inversion lemmas are
for. The recursion is over the server list rather than the reaction list for the same reason the
names rung is: the reaction list has no structure of its own to recurse on, since group lengths vary
with routing and with self-send sites independently.

Everything after the colon is universally quantified so that `induction servers` gets an induction
hypothesis general in `compiled`. The compiled list is *not* fixed before the induction: each step
splits it into a group and a remainder, and the remainder is what the hypothesis is applied to.

Note what this rung does **not** say. It fixes the trigger list of a compiled reaction list against
a given server list, in that server list's order; it says nothing about which server list a reactor
is compiled from. That is rung three's content, and it is where stage F's sort enters.
-/
theorem compileGeneralMessageServerReactions_triggers :
    ∀ (env : GeneralOutputPortEnv)
      (selfSends : List GeneralSelfSend)
      (routes : List GeneralRoute)
      (className : ClassName)
      (servers : List DTR.GeneralMessageServer)
      (compiled : List LF.GeneralReaction),
      compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          servers =
          .ok compiled →
        compiled.map
            (fun reaction =>
              reaction.trigger) =
          generalReactionTriggersOf
            selfSends
            routes
            className
            servers := by

  intro env selfSends routes className servers
  induction servers with

  | nil =>
      intro compiled hCompiled

      simp [
        generalReactionTriggersOf,
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
        generalReactionTriggersOf,
        compileGeneralMessageServerReactionGroup_triggers
          hServer,
        inductionHypothesis
          compiledRemaining
          hRemaining
      ]

/--
A compiled reactor's message reactions trigger on its message servers' actions and input ports, in
**message-server priority order**.

Rung three, and the statement the aggregation was built for: it describes
`reactor.messageReactions.map (fun reaction => reaction.trigger)`, which is exactly the list
`LF.GeneralProgram.reactionFor?_perm_of_nodup_triggers` asks to be duplicate-free. With this equation
in hand that `Nodup` obligation becomes a question about `generalReactionTriggersOf`, a total
function of the class and the routes, rather than a question about a compilation.

`generalPriorityOrderedMessageServers reactiveClass` appears on the right, not
`reactiveClass.messageServers`, matching `compileGeneralReactiveClass_reactionNames`. Keeping stage
F's level-2 sort in the statement is deliberate: **F60** caught the opposite shape, where a
permutation pushed down inside a specification let a theorem prove the same equation while saying
nothing about order.

The sort is also why the `Nodup` this rung feeds is worth having. Stage F's sort permutes whole
groups, so it changes this list; `reactionFor?_perm_of_nodup_triggers` says that under distinct
triggers the permutation cannot change which reaction fires. That is **F80**'s point stated
positively — stage F's ordering theorems are run-level inert — and this equation is the last piece
of the translator-side half of it.
-/
theorem compileGeneralReactiveClass_reactionTriggers
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
          reaction.trigger) =
      generalReactionTriggersOf
        (selfSendsOfClass
          reactiveClass)
        routes
        reactiveClass.name
        (generalPriorityOrderedMessageServers
          reactiveClass) := by

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
    compileGeneralMessageServerReactions_triggers
      env
      (selfSendsOfClass reactiveClass)
      routes
      reactiveClass.name
      (generalPriorityOrderedMessageServers
        reactiveClass)
      compiledMessageReactions
      hMessageServers

/-!
## One reaction group's triggers are distinct

`compileGeneralReactiveClass_reactionTriggers` above turns
`reactionFor?_perm_of_nodup_triggers`'s hypothesis into a question about
`generalReactionTriggersOf`. This section answers it for **one message server's group**, which
is the rung the class-level answer will induct over, and it is deliberately the same scoping
choice `assembleGeneralPortReactions_names` records: a class-level statement needs a
combinator over groups, and this development depends on no `List.flatMap`.

**Why the group splits into exactly two arguments and one of them is free.** A group is the
action reactions followed by the port reactions, so `List.nodup_append` reduces distinctness to
three obligations: the action half, the port half, and no action trigger equal to a port
trigger. The third is free, and free for a structural reason rather than by luck —
`LF.GeneralTrigger.logicalAction` and `LF.GeneralTrigger.inputPort` are different constructors,
so the two halves cannot meet whatever the names inside them are. That is the same fact
`matchesKind`'s two cross-constructor `false` cases give the semantics side, arriving here from
the syntax side.

**The action half needed no new name reasoning, and measuring that removed two obligations.**
The plan for this section carried an owed suffix-cancellation lemma in `NameGeneration.lean`
plus an ordinal-distinctness argument over sites, on the assumption that distinctness of
`generalActionNameAtSite` across a server's sites had to be *proved*. It does not:
`generalMessageActionNamesOf` already specifies exactly those names, `generalMessageReactionTriggersOf`
is that list under one constructor, and distinctness of the names is a **decided guard clause**,
because action names are declared identifiers and `LF.GeneralReactor.declaredNames` carries them.
So the action half is the port half's argument with a different constructor, and both are
guard-relative in the `F50`/`#60` shape rather than claimed by construction.

**Both hypotheses are stated at the list the conclusion is about, not projected from the guard
here.** That is forced by a measured asymmetry inside one reactor: `assembleGeneralReactor`
builds `logicalActions` from `reactiveClass.messageServers` but `messageReactions` from
`generalPriorityOrderedMessageServers reactiveClass`. The two lists are permutations of each
other, so every reaction still triggers on an action its reactor declares and there is no defect
here — but a projection out of `declaredNames` would land on the *unsorted* list while this
conclusion is about whichever list its caller names. Keeping the hypotheses at the caller's list
leaves that permutation transfer to the step that composes, where the sort is visible, instead of
burying it in a projection.
-/

/--
A message server's action-reaction triggers are its action names under one constructor.

Both sides branch on `generalSelfSendSitesOf`, and they agree branch for branch by construction
rather than by argument — `generalMessageActionNamesOf` was written as the action-declaration
counterpart of `generalMessageReactionNamesOf`, and F56's repair made the trigger list follow the
same site list. Stating the equation is what lets the distinctness argument below run entirely on
names, where the guard speaks, instead of on triggers, where it does not.

The zero-site branch is the one that would break silently: both sides must spell the name with
`actionNameFor` there, and they do, for the reason every zero-site branch in this file records —
otherwise a reaction triggers on an action its own reactor never declares.
-/
private theorem generalMessageReactionTriggersOf_eq_map_logicalAction
    (selfSends : List GeneralSelfSend)
    (message : MsgName) :
    generalMessageReactionTriggersOf
        selfSends
        message =
      (generalMessageActionNamesOf
        selfSends
        message).map
        LF.GeneralTrigger.logicalAction := by

  cases hSites :
      generalSelfSendSitesOf
        message
        selfSends with

  | nil =>
      simp [
        generalMessageReactionTriggersOf,
        generalMessageActionNamesOf,
        hSites
      ]

  | cons firstSite remainingSites =>
      simp [
        generalMessageReactionTriggersOf,
        generalMessageActionNamesOf,
        hSites
      ]

/--
Distinct action names give distinct action triggers.

The `logicalAction` counterpart of the `inputPort` step inside
`assembleGeneralPortReactions_triggers_nodup`, and it is the same instrument:
`nodup_map_of_reflecting` wants only that equal triggers force equal names, which constructor
injectivity supplies. `hReflect` is hoisted into an explicit `have` rather than passed as an
inline `by` block, because an inline one leaves the goal as an un-beta-reduced application of the
`target` lambda and the rewrite inside it then has nothing to fire on.
-/
private theorem nodup_map_logicalAction
    (names : List ActionName)
    (hNames :
      (names.map
        (fun name =>
          name.value)).Nodup) :
    (names.map
      LF.GeneralTrigger.logicalAction).Nodup := by

  have hReflect :
      ∀ (first second : ActionName),
        LF.GeneralTrigger.logicalAction first =
            LF.GeneralTrigger.logicalAction second →
          first.value = second.value := by

    intro first second hTrigger

    simp only [
      LF.GeneralTrigger.logicalAction.injEq
    ] at hTrigger

    rw [hTrigger]

  exact
    nodup_map_of_reflecting
      (fun name =>
        name.value)
      LF.GeneralTrigger.logicalAction
      hReflect
      names
      hNames

/--
Every reaction in one message server's group carries a distinct trigger.

The group-level rung of the distinctness ladder, and the exact analogue of
`assembleGeneralPortReactions_triggers_nodup` one level up: that theorem covers the port half of
one group, this one covers the whole group. Both are **guard-relative** — the two hypotheses are
the distinctness facts a well-formed reactor's `declaredNames` carries, and neither is claimed by
construction, because F42 measured that the translator can in fact emit two port declarations with
one name and the standing doctrine is to state the scoped theorem rather than assert the
unconditional one.

`hCompiled` is discharged through `compileGeneralMessageServerReactionGroup_triggers`, so the
`Nodup` argument never touches the compiler — it runs entirely on the specification, which is what
that theorem was written for.

The third `List.nodup_append` obligation is discharged by constructor disjointness alone. It is
worth being explicit that this is not a convenience: it is the syntax-side form of the same fact
`LF.GeneralTrigger.matchesKind` gives the semantics side in its two cross-constructor `false`
cases, and it is why the action half and the port half can be reasoned about in isolation at all.
Without it every cross pair would need an argument relating a generated action name to a generated
port name, and no such relation is available or wanted.
-/
theorem compileGeneralMessageServerReactionGroup_triggers_nodup
    {env : GeneralOutputPortEnv}
    {selfSends : List GeneralSelfSend}
    {routes : List GeneralRoute}
    {className : ClassName}
    {server : DTR.GeneralMessageServer}
    {group : List LF.GeneralReaction}
    (hCompiled :
      compileGeneralMessageServerReactionGroup
          env
          selfSends
          routes
          className
          server =
        .ok group)
    (hActionNames :
      ((generalMessageActionNamesOf
        selfSends
        server.name).map
        (fun name =>
          name.value)).Nodup)
    (hInputPortNames :
      ((generalInputPortsOf
        className
        routes).map
        (fun port =>
          port.name.value)).Nodup) :
    (group.map
      (fun reaction =>
        reaction.trigger)).Nodup := by

  rcases exists_of_compileGeneralMessageServerReactionGroup_ok hCompiled with
    ⟨compiledBody, _, _⟩

  rw [
    compileGeneralMessageServerReactionGroup_triggers hCompiled,
    List.nodup_append
  ]

  refine ⟨?_, ?_, ?_⟩

  · rw [generalMessageReactionTriggersOf_eq_map_logicalAction]

    exact
      nodup_map_logicalAction
        (generalMessageActionNamesOf
          selfSends
          server.name)
        hActionNames

  · rw [
      ← assembleGeneralPortReactions_triggers
          className
          server
          compiledBody
          routes
    ]

    exact
      assembleGeneralPortReactions_triggers_nodup
        className
        server
        compiledBody
        routes
        hInputPortNames

  · intro actionTrigger hActionTrigger portTrigger hPortTrigger

    rw [
      generalMessageReactionTriggersOf_eq_map_logicalAction
    ] at hActionTrigger

    rcases List.mem_map.mp hActionTrigger with ⟨actionName, _, hActionEq⟩

    rcases List.mem_map.mp hPortTrigger with ⟨route, _, hPortEq⟩

    subst hActionEq

    subst hPortEq

    intro hSame

    simp at hSame

/-!
## Three tools the class-level trigger `Nodup` needs

`compileGeneralMessageServerReactionGroup_triggers_nodup` above settles one group. Concatenating
groups across a class needs strictly more than "each group is `Nodup`" — the cross-group obligation
`List.nodup_append` hands back quantifies over the *other* group's triggers — and the three
declarations here are exactly the missing pieces, each stated in the form that walk consumes.

**Why the port half is restated rather than reused directly.**
`assembleGeneralPortReactions_triggers_nodup` is indexed by a `compiledBody` that its own conclusion
never mentions, because it speaks about `assembleGeneralPortReactions`. A statement about the
*specification* list cannot supply such a body: `LF.GeneralBody` has no `Inhabited` instance, and
inventing a phantom parameter to feed a lemma that ignores it would push that awkwardness onto every
later caller. `generalPortReactionTriggers_nodup` below is therefore the body-free form of the same
fact, proved by the same two steps, and it is the shape the group- and class-level statements both
want.

**Why injectivity-on-membership has to be stated here.** The cross-group argument compares a route
into one message server against a route into another. Both live in `generalRoutesIntoClass`, whose
port names the guard makes `Nodup`, and the two routes differ because they carry different messages —
but getting from "different routes in a list whose image is `Nodup`" to "different images" is
precisely the content of `eq_of_nodup_map`, which is `private` in `LF/GeneralWellFormed.lean` and out
of reach. `nodup_map_ne_of_mem` states the contrapositive directly, which is the direction every use
here wants, and keeps the dependency to `List.nodup_cons` and `List.mem_map`.
-/

/--
In a list whose image under `projection` is duplicate-free, distinct members have distinct images.

The positive form of the fact `eq_of_nodup_map` (`LF/GeneralWellFormed.lean:562`) states negatively,
restated because that one is `private` in a module this file cannot reach. Stating it as an
inequality rather than as an injectivity-on-membership equation is deliberate: every consumer here
is discharging a `List.nodup_append` cross obligation, whose goal is already an inequality, so the
equation form would be immediately contraposed at each of the four call sites.

`∀ values` sits after `projection` so that `induction` leaves the induction hypothesis as the whole
implication rather than only its conclusion — the placement `mem_generalRoutesIntoClass` and
`generalRoutesIntoMessageServer_nodup_map` both use, and for the same reason.
-/
private theorem nodup_map_ne_of_mem
    {α β : Type}
    (projection : α → β) :
    ∀ (values : List α),
      (values.map
        projection).Nodup →
        ∀ first,
          first ∈ values →
            ∀ second,
              second ∈ values →
                first ≠ second →
                  projection first ≠ projection second := by

  intro values

  induction values with

  | nil =>
      intro _ first hFirst
      simp at hFirst

  | cons head remaining inductionHypothesis =>
      intro hNodup first hFirst second hSecond hDistinct

      rw [
        List.map_cons,
        List.nodup_cons
      ] at hNodup

      rcases List.mem_cons.mp hFirst with hFirstHead | hFirstTail

      · rcases List.mem_cons.mp hSecond with hSecondHead | hSecondTail

        · exact
            absurd
              (hFirstHead.trans hSecondHead.symm)
              hDistinct

        · subst hFirstHead

          intro hEqual

          exact
            hNodup.left
              (hEqual ▸
                List.mem_map.mpr
                  ⟨second, hSecondTail, rfl⟩)

      · rcases List.mem_cons.mp hSecond with hSecondHead | hSecondTail

        · subst hSecondHead

          intro hEqual

          exact
            hNodup.left
              (hEqual.symm ▸
                List.mem_map.mpr
                  ⟨first, hFirstTail, rfl⟩)

        · exact
            inductionHypothesis
              hNodup.right
              first
              hFirstTail
              second
              hSecondTail
              hDistinct

/--
The port-reaction triggers of one message server are distinct, stated about the specification list.

The body-free counterpart of `assembleGeneralPortReactions_triggers_nodup`, proved by the same two
steps: constructor injectivity lifts the guard's port-name `Nodup` to the class-level trigger list,
then `generalRoutesIntoMessageServer_nodup_map` descends to one server, the filtered list being a
sublist of the class-level one in the only sense that matters — membership, which is what B1's
`mem_generalRoutesIntoClass_of_mem_generalRoutesIntoMessageServer` supplies.

Generalised from `server.name` to an arbitrary `serverName` because the class-level walk applies it
at each server in turn, and at a server it has only the name of.
-/
private theorem generalPortReactionTriggers_nodup
    (className : ClassName)
    (serverName : MsgName)
    (routes : List GeneralRoute)
    (hInputPortNames :
      ((generalInputPortsOf
        className
        routes).map
        (fun port =>
          port.name.value)).Nodup) :
    (((generalRoutesIntoMessageServer
      className
      serverName
      routes).map
      (fun route =>
        LF.GeneralTrigger.inputPort
          (generalInputPortOfRoute route)))).Nodup := by

  rw [
    generalInputPortsOf_portNames
      className
      routes
  ] at hInputPortNames

  have hReflect :
      ∀ (first second : GeneralRoute),
        LF.GeneralTrigger.inputPort
              (generalInputPortOfRoute first) =
            LF.GeneralTrigger.inputPort
              (generalInputPortOfRoute second) →
          (generalInputPortOfRoute first).value =
            (generalInputPortOfRoute second).value := by

    intro first second hTrigger

    simp only [
      LF.GeneralTrigger.inputPort.injEq
    ] at hTrigger

    rw [hTrigger]

  have hClassLevel :
      ((generalRoutesIntoClass
        className
        routes).map
        (fun candidate =>
          LF.GeneralTrigger.inputPort
            (generalInputPortOfRoute candidate))).Nodup :=
    nodup_map_of_reflecting
      (fun candidate =>
        (generalInputPortOfRoute candidate).value)
      (fun candidate =>
        LF.GeneralTrigger.inputPort
          (generalInputPortOfRoute candidate))
      hReflect
      (generalRoutesIntoClass
        className
        routes)
      hInputPortNames

  exact
    generalRoutesIntoMessageServer_nodup_map
      (fun candidate =>
        LF.GeneralTrigger.inputPort
          (generalInputPortOfRoute candidate))
      className
      serverName
      routes
      hClassLevel

/--
One message server's whole reaction group has distinct triggers, stated about the specification list.

The body-free counterpart of `compileGeneralMessageServerReactionGroup_triggers_nodup`, and the form
the class-level walk consumes: an induction over `generalReactionTriggersOf` never mentions a compiled
body, so a hypothesis that needs one cannot be threaded through it.

The three obligations `List.nodup_append` produces are the action half from the guard's action names,
the port half from the guard's port names, and no action trigger equal to a port trigger — the last
discharged by constructor disjointness alone, which is the syntax-side form of the two
cross-constructor `false` cases in `LF.GeneralTrigger.matchesKind`.

Both name hypotheses are stated at the arguments the conclusion is about rather than projected from
`LF.GeneralReactor.declaredNames` here. That is not stylistic: `assembleGeneralReactor` builds
`logicalActions` from `reactiveClass.messageServers` while `messageReactions` goes through
`generalPriorityOrderedMessageServers reactiveClass`, so a projection would land on the unsorted list
while this statement is used at whichever list its caller names. The two are permutations of each
other — every reaction still triggers on an action its reactor declares, so there is nothing wrong
with the translator here — but the transfer between them belongs to the step where the sort is
visible, not buried inside this lemma.
-/
theorem generalMessageServerReactionTriggers_nodup
    (className : ClassName)
    (serverName : MsgName)
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (hActionNames :
      ((generalMessageActionNamesOf
        selfSends
        serverName).map
        (fun name =>
          name.value)).Nodup)
    (hInputPortNames :
      ((generalInputPortsOf
        className
        routes).map
        (fun port =>
          port.name.value)).Nodup) :
    (generalMessageReactionTriggersOf
      selfSends
      serverName ++
      (generalRoutesIntoMessageServer
        className
        serverName
        routes).map
        (fun route =>
          LF.GeneralTrigger.inputPort
            (generalInputPortOfRoute route))).Nodup := by

  rw [List.nodup_append]

  refine ⟨?_, ?_, ?_⟩

  · rw [generalMessageReactionTriggersOf_eq_map_logicalAction]

    exact
      nodup_map_logicalAction
        (generalMessageActionNamesOf
          selfSends
          serverName)
        hActionNames

  · exact
      generalPortReactionTriggers_nodup
        className
        serverName
        routes
        hInputPortNames

  · intro actionTrigger hActionTrigger portTrigger hPortTrigger

    rw [
      generalMessageReactionTriggersOf_eq_map_logicalAction
    ] at hActionTrigger

    rcases List.mem_map.mp hActionTrigger with ⟨actionName, _, hActionEq⟩

    rcases List.mem_map.mp hPortTrigger with ⟨route, _, hPortEq⟩

    subst hActionEq

    subst hPortEq

    intro hSame

    simp at hSame

/-!
### Distinct triggers across a whole reactive class

The last translator-side step. `generalReactionTriggersOf` concatenates one group per message server,
and `generalMessageServerReactionTriggers_nodup` above says each group is duplicate-free, so what is
left is that no two groups collide. That is not free: `List.nodup_append`'s third component quantifies
over the *tail's* triggers, and an induction hypothesis saying only "the tail is duplicate-free"
cannot describe them. The inversion lemma below supplies the description — the same reason B3 needed
a specification function before it could state anything about the list, arriving one level up.
-/

/--
Every trigger of a class's reaction list is either one of its action names or one of its input ports,
and in the port case the route is a route into the class whose message names one of the servers.

The membership inversion the cross-group obligation needs. The `∃ server` component is the load-
bearing half: without it a tail trigger's route is known only to route into the *class*, which is not
enough to distinguish it from a head route, since both would then satisfy the same predicate. With
it, the two routes carry the names of two different servers, and distinctness of server names does the
rest.

Both disjuncts are stated with `trigger` on the left of the equation so that a caller can `subst`
them directly against a `List.mem_map` witness, which produces the equation the other way round.
-/
private theorem mem_generalReactionTriggersOf
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (className : ClassName)
    (trigger : LF.GeneralTrigger) :
    ∀ (servers : List DTR.GeneralMessageServer),
      trigger ∈
        generalReactionTriggersOf
          selfSends
          routes
          className
          servers →
        (∃ name,
            name ∈
              generalActionNamesOf
                selfSends
                servers ∧
              trigger =
                LF.GeneralTrigger.logicalAction
                  name) ∨
          (∃ route,
              route ∈
                generalRoutesIntoClass
                  className
                  routes ∧
                (∃ server,
                    server ∈ servers ∧
                    route.message = server.name) ∧
                trigger =
                  LF.GeneralTrigger.inputPort
                    (generalInputPortOfRoute route)) := by

  intro servers
  induction servers with

  | nil =>
      intro hMember

      simp [
        generalReactionTriggersOf
      ] at hMember

  | cons server remaining inductionHypothesis =>
      intro hMember

      simp only [
        generalReactionTriggersOf
      ] at hMember

      rcases List.mem_append.mp hMember with hGroup | hTail

      · rcases List.mem_append.mp hGroup with hAction | hPort

        · rw [
            generalMessageReactionTriggersOf_eq_map_logicalAction
          ] at hAction

          rcases List.mem_map.mp hAction with ⟨name, hName, hEqual⟩

          refine Or.inl ⟨name, ?_, hEqual.symm⟩

          simp only [
            generalActionNamesOf
          ]

          exact List.mem_append.mpr (Or.inl hName)

        · rcases List.mem_map.mp hPort with ⟨route, hRoute, hEqual⟩

          exact
            Or.inr
              ⟨route,
                mem_generalRoutesIntoClass_of_mem_generalRoutesIntoMessageServer
                  className
                  server.name
                  route
                  routes
                  hRoute,
                ⟨server,
                  List.mem_cons.mpr (Or.inl rfl),
                  message_of_mem_generalRoutesIntoMessageServer
                    className
                    server.name
                    route
                    routes
                    hRoute⟩,
                hEqual.symm⟩

      · rcases inductionHypothesis hTail with
          ⟨name, hName, hEqual⟩ |
            ⟨route, hRoute, ⟨tailServer, hTailServer, hMessage⟩, hEqual⟩

        · refine Or.inl ⟨name, ?_, hEqual⟩

          simp only [
            generalActionNamesOf
          ]

          exact List.mem_append.mpr (Or.inr hName)

        · exact
            Or.inr
              ⟨route,
                hRoute,
                ⟨tailServer,
                  List.mem_cons.mpr (Or.inr hTailServer),
                  hMessage⟩,
                hEqual⟩

/--
A reactive class's reactions have pairwise distinct triggers — relative to the guard.

The statement `LF.GeneralProgram.reactionFor?_perm_of_nodup_triggers` asks for, transported to the
translator's specification of the list by `compileGeneralReactiveClass_reactionTriggers`. Composing
the two is the remaining commit; this is the last one that reasons about the translator alone.

**All three hypotheses are stated at the caller's server list and none is projected from the guard
here.** That is forced, not stylistic: `assembleGeneralReactor` builds `logicalActions` from
`reactiveClass.messageServers` and `messageReactions` from
`generalPriorityOrderedMessageServers reactiveClass`, and those two lists are permutations of each
other rather than equal. A projection out of `LF.GeneralReactor.declaredNames` would therefore land
on the unsorted list while this conclusion is about whichever list the caller names. The permutation
transfer belongs to the step where the sort is visible, and `List.Perm.nodup` is its instrument —
noting that permuting the *server* list permutes concatenated per-server blocks, which is not a free
step.

The three hypotheses, and where each is discharged. The action-name and port-name hypotheses are the
`Nodup` clauses of `declaredNames`, in the spellings `generalActionNamesOf` and `generalInputPortsOf`
already use. The server-name hypothesis is a conjunct of `DTR.GeneralModel.namesUniqueAndValid`; it
is what makes two groups' port sets disjoint, and it is the only one of the three that plays no part
in the single-group statement above.

Four obligations, of which one is real. The head group is
`generalMessageServerReactionTriggers_nodup`; the tail is the induction hypothesis; an action trigger
and a port trigger can never be equal because they are different constructors of
`LF.GeneralTrigger`; and the cross-group case splits into action-against-action, which the appended
action names already forbid, and port-against-port, which is the argument the inversion lemma above
exists for.
-/
theorem generalReactionTriggersOf_nodup
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (className : ClassName)
    (hInputPortNames :
      ((generalInputPortsOf
        className
        routes).map
        (fun port =>
          port.name.value)).Nodup) :
    ∀ (servers : List DTR.GeneralMessageServer),
      ((generalActionNamesOf
        selfSends
        servers).map
        (fun name =>
          name.value)).Nodup →
      (servers.map
        (fun server =>
          server.name)).Nodup →
        (generalReactionTriggersOf
          selfSends
          routes
          className
          servers).Nodup := by

  intro servers
  induction servers with

  | nil =>
      intro _ _

      simp [
        generalReactionTriggersOf
      ]

  | cons server remaining inductionHypothesis =>
      intro hActionNames hServerNames

      simp only [
        generalActionNamesOf,
        List.map_append
      ] at hActionNames

      rw [List.nodup_append] at hActionNames

      obtain ⟨hHeadActionNames, hTailActionNames, hActionCross⟩ := hActionNames

      rw [
        List.map_cons,
        List.nodup_cons
      ] at hServerNames

      obtain ⟨hServerFresh, hRemainingServers⟩ := hServerNames

      have hClassPortNames :
          ((generalRoutesIntoClass
            className
            routes).map
            (fun candidate =>
              (generalInputPortOfRoute candidate).value)).Nodup := by
        rw [
          ← generalInputPortsOf_portNames
            className
            routes
        ]

        exact hInputPortNames

      simp only [
        generalReactionTriggersOf
      ]

      rw [List.nodup_append]

      refine ⟨?_, ?_, ?_⟩

      · exact
          generalMessageServerReactionTriggers_nodup
            className
            server.name
            selfSends
            routes
            hHeadActionNames
            hInputPortNames

      · exact
          inductionHypothesis
            hTailActionNames
            hRemainingServers

      · intro headTrigger hHeadTrigger tailTrigger hTailTrigger

        rcases List.mem_append.mp hHeadTrigger with hHeadAction | hHeadPort

        · rw [
            generalMessageReactionTriggersOf_eq_map_logicalAction
          ] at hHeadAction

          rcases List.mem_map.mp hHeadAction with ⟨headName, hHeadName, hHeadEq⟩

          rcases
              mem_generalReactionTriggersOf
                selfSends
                routes
                className
                tailTrigger
                remaining
                hTailTrigger with
            ⟨tailName, hTailName, hTailEq⟩ | ⟨_, _, _, hTailEq⟩

          · subst hHeadEq

            subst hTailEq

            intro hSame

            simp only [
              LF.GeneralTrigger.logicalAction.injEq
            ] at hSame

            have hNameValues :
                headName.value =
                  tailName.value := by
              rw [hSame]

            exact
              hActionCross
                headName.value
                (List.mem_map.mpr ⟨headName, hHeadName, rfl⟩)
                tailName.value
                (List.mem_map.mpr ⟨tailName, hTailName, rfl⟩)
                hNameValues

          · subst hHeadEq

            subst hTailEq

            intro hSame

            simp at hSame

        · rcases List.mem_map.mp hHeadPort with ⟨headRoute, hHeadRoute, hHeadEq⟩

          rcases
              mem_generalReactionTriggersOf
                selfSends
                routes
                className
                tailTrigger
                remaining
                hTailTrigger with
            ⟨_, _, hTailEq⟩ |
              ⟨tailRoute, hTailRoute, ⟨tailServer, hTailServer, hTailMessage⟩, hTailEq⟩

          · subst hHeadEq

            subst hTailEq

            intro hSame

            simp at hSame

          · subst hHeadEq

            subst hTailEq

            intro hSame

            simp only [
              LF.GeneralTrigger.inputPort.injEq
            ] at hSame

            have hRoutesDistinct :
                headRoute ≠ tailRoute := by
              intro hEqualRoutes

              apply hServerFresh

              rw [
                ← message_of_mem_generalRoutesIntoMessageServer
                  className
                  server.name
                  headRoute
                  routes
                  hHeadRoute,
                hEqualRoutes,
                hTailMessage
              ]

              exact List.mem_map.mpr ⟨tailServer, hTailServer, rfl⟩

            have hPortValues :
                (generalInputPortOfRoute headRoute).value =
                  (generalInputPortOfRoute tailRoute).value := by
              rw [hSame]

            exact
              nodup_map_ne_of_mem
                (fun candidate =>
                  (generalInputPortOfRoute candidate).value)
                (generalRoutesIntoClass
                  className
                  routes)
                hClassPortNames
                headRoute
                (mem_generalRoutesIntoClass_of_mem_generalRoutesIntoMessageServer
                  className
                  server.name
                  headRoute
                  routes
                  hHeadRoute)
                tailRoute
                hTailRoute
                hRoutesDistinct
                hPortValues

/-!
### The emitted reaction list has distinct triggers

`generalReactionTriggersOf_nodup` above is stated at whatever server list its caller names, and
`compileGeneralReactiveClass_reactionTriggers` keys the emitted list to
`generalPriorityOrderedMessageServers reactiveClass` — the **sorted** list. The two do not meet
directly, because `assembleGeneralReactor` builds `logicalActions` from
`reactiveClass.messageServers` (**unsorted**), so the action-name distinctness a caller can actually
produce from the guard is the unsorted one.

**The cheap direction is to permute the conclusion, not the hypotheses.** Applying the induction at
the unsorted list makes all three hypotheses guard-shaped with no transfer at all, and leaves exactly
one permutation obligation: that the trigger list itself is order-invariant under reordering of the
servers. Transferring the *action-name* hypothesis instead would have needed the same flattened
permutation **plus** a second one for the server names, and — if routed through injectivity of the
generated names rather than the guard — would have resurrected the suffix-cancellation and
site-ordinal arguments the group-level proof deliberately retired.
-/

/--
Swapping the first two of three appended lists is a permutation.

Stated separately, generic in the element type, and with `List.append_assoc` applied to **explicit**
arguments. That last point is the reason this is a lemma rather than two `rw`s inline: the goal it
serves has an appended head group, so `rw [← List.append_assoc]` with the arguments left implicit
finds a *second*, unwanted match inside that group and reassociates the wrong pair. Fixing the three
arguments makes the rewrite pattern unambiguous.
-/
private theorem perm_append_swap_middle
    {α : Type}
    (first second remaining : List α) :
    List.Perm
      (first ++
        (second ++ remaining))
      (second ++
        (first ++ remaining)) := by

  rw [
    ← List.append_assoc
      first
      second
      remaining,
    ← List.append_assoc
      second
      first
      remaining
  ]

  exact
    List.Perm.append_right
      remaining
      List.perm_append_comm

/--
Reordering the message servers permutes the emitted trigger list.

Proved by induction on the `List.Perm` derivation rather than on either list, which is what makes the
four cases align with the four ways a permutation is built: `nil` is reflexivity, `cons` keeps a
shared head group and recurses, `swap` is the append exchange above, and `trans` composes.

`simp only` rather than `simp` throughout. Plain `simp` can reach `List.append_assoc` and
reassociate `(actionPart ++ portPart) ++ recursive`, which would move the goal out from under the
shape each case's closing lemma expects.

This is the first `List.Perm` statement in this file. It is deliberately about the specification
function and not about `reactor.messageReactions`, so it composes with the rung-3 description rather
than duplicating it.
-/
theorem generalReactionTriggersOf_perm
    (selfSends : List GeneralSelfSend)
    (routes : List GeneralRoute)
    (className : ClassName)
    {first second : List DTR.GeneralMessageServer}
    (hPerm :
      List.Perm
        first
        second) :
    List.Perm
      (generalReactionTriggersOf
        selfSends
        routes
        className
        first)
      (generalReactionTriggersOf
        selfSends
        routes
        className
        second) := by

  induction hPerm with

  | nil =>
      simp only [
        generalReactionTriggersOf
      ]

      exact List.Perm.nil

  | cons _ _ inductionHypothesis =>
      simp only [
        generalReactionTriggersOf
      ]

      exact
        List.Perm.append_left
          _
          inductionHypothesis

  | swap _ _ _ =>
      simp only [
        generalReactionTriggersOf
      ]

      exact
        perm_append_swap_middle
          _
          _
          _

  | trans _ _ inductionHypothesisFirst inductionHypothesisSecond =>
      exact
        inductionHypothesisFirst.trans
          inductionHypothesisSecond

/--
A compiled reactive class emits reactions with pairwise distinct triggers — relative to the guard.

The translator-side half of item 1b, packaged in the shape
`LF.GeneralProgram.reactionFor?_perm_of_nodup_triggers` asks for: `hNodup` about
`reactor.messageReactions.map (fun reaction => reaction.trigger)`. Everything after this is the
composition in `Relico/Correctness/GeneralCorrespondence.lean`, which is the only cheap module that
sees both `LF.GeneralSemantics` and `LF.GeneralWellFormed`; this file can reach neither, which is why
`Nodup` and not `LF.UniquelyTriggered` is the interface the whole ladder speaks.

**All three distinctness facts are hypotheses at `reactiveClass.messageServers`, the source model's
own list.** None is claimed by construction — the F50/`#60` shape. Two of the three are exactly the
`Nodup` clauses a well-formed reactor's `declaredNames` carries, and the third is a conjunct of
`DTR.GeneralModel.namesUniqueAndValid`. `generalActionNamesOf` is keyed to the unsorted list on
purpose: that is the list `assembleGeneralReactor` declares its logical actions from, so a caller
projecting out of the guard lands here and needs no permutation of its own.

The sort is bridged by `DTR.GeneralMessageServerPriority.normalize_perm` and
`generalReactionTriggersOf_perm`, so stage F's level-2 message-server order is **visible in the proof
and absent from the statement** — which is the honest reading: distinctness of triggers is a fact
about the *set* of servers, and the sort only decides the order the reactions are emitted in.
-/
theorem compileGeneralReactiveClass_reactionTriggers_nodup
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (hInputPortNames :
      ((generalInputPortsOf
        reactiveClass.name
        routes).map
        (fun port =>
          port.name.value)).Nodup)
    (hActionNames :
      ((generalActionNamesOf
        (selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
        (fun name =>
          name.value)).Nodup)
    (hServerNames :
      (reactiveClass.messageServers.map
        (fun server =>
          server.name)).Nodup) :
    (reactor.messageReactions.map
      (fun reaction =>
        reaction.trigger)).Nodup := by

  rw [
    compileGeneralReactiveClass_reactionTriggers
      hCompiled
  ]

  unfold generalPriorityOrderedMessageServers

  refine
    (generalReactionTriggersOf_perm
      (selfSendsOfClass
        reactiveClass)
      routes
      reactiveClass.name
      (DTR.GeneralMessageServerPriority.normalize_perm
        reactiveClass.messageServers)).nodup_iff.mpr
    ?_

  exact
    generalReactionTriggersOf_nodup
      (selfSendsOfClass
        reactiveClass)
      routes
      reactiveClass.name
      hInputPortNames
      reactiveClass.messageServers
      hActionNames
      hServerNames

end Translation
end Relico
