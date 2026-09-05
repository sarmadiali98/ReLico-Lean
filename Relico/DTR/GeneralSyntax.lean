import Relico.Common.ActorTopology
import Relico.Common.Name
import Relico.Common.Store
import Relico.Common.Time

set_option autoImplicit false

namespace Relico
namespace DTR

/-!
The general Timed Rebeca source syntax.

This family is the first one able to represent every model the `general-v1`
frontend accepts: several reactive classes, several actor instances, declared
known rebecs with per-instance bindings, constructor parameters with instance
arguments, sends that target `self` or a declared known rebec, and boolean as
well as integer values.

The family is additive. It does not widen `Relico.Value` and it does not widen
`Relico.Payload`, which is mentioned in a large fraction of the existing
development; a general value type is introduced here instead, and the earlier
families keep the types they were proved against.

Control flow is deliberately absent. Statement bodies are flat lists, so the
later stage that admits branching and iteration must add constructors, and
adding a constructor breaks every exhaustive match rather than falling through
a default branch.
-/

/--
The value types the general fragment admits.

Only `int` appears in any example in the paper. `boolean` is admitted because
the frontend's own expression language contains boolean literals and boolean
operators, and a constructor with a boolean parameter would otherwise be
impossible to instantiate.
-/
inductive GeneralType where
  | int
  | boolean

deriving Repr, DecidableEq, BEq, Inhabited

/--
A general value.

This is deliberately a new type rather than a widening of `Relico.Value`. The
integer-only value and its `Payload` alias are load-bearing for every earlier
family, and widening them would put those proofs in the blast radius of a
change that buys them nothing.
-/
inductive GeneralValue where
  | int :
      Int →
      GeneralValue

  | bool :
      Bool →
      GeneralValue

deriving Repr, DecidableEq, BEq, Inhabited

/--
A general message payload, positional and typed per element.
-/
abbrev GeneralPayload := List DTR.GeneralValue

namespace GeneralValue

/--
The type of a value.
-/
def typeOf :
    DTR.GeneralValue →
    DTR.GeneralType

  | .int _ =>
      .int

  | .bool _ =>
      .boolean

/--
Whether a value inhabits a declared type.
-/
def hasType
    (value : DTR.GeneralValue)
    (expected : DTR.GeneralType) :
    Bool :=
  value.typeOf == expected

@[simp]
theorem hasType_typeOf
    (value : DTR.GeneralValue) :
    hasType value value.typeOf =
      true := by
  cases value <;> rfl

end GeneralValue

namespace GeneralType

/--
The implicit initial value of a state variable of this type.

A source-level initializer is rejected upstream of this development, and the
general state variable declaration carries no initializer field, so the initial
valuation is determined by the declared type alone.
-/
def initialValue :
    DTR.GeneralType →
    DTR.GeneralValue

  | .int =>
      .int 0

  | .boolean =>
      .bool false

@[simp]
theorem typeOf_initialValue
    (declaredType : DTR.GeneralType) :
    (initialValue declaredType).typeOf =
      declaredType := by
  cases declaredType <;> rfl

end GeneralType


/--
The binary operators the general fragment admits.

The paper never defines its expression language: `Expr` occurs on seven
right-hand sides of its grammar and is never given a production, and its only
handles on expressions are the opaque semantic ones. So this operator set is
this project's choice and must not be presented as a citation.
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
The unary operators the general fragment admits.
-/
inductive GeneralUnaryOp where
  | negate
  | logicalNot

deriving Repr, DecidableEq, BEq, Inhabited


/--
A general expression.

The frontend reports one `variable` node and leaves the state-variable versus
parameter distinction to be recovered from the enclosing scope. That resolution
happens in the elaborator, not here, so this syntax keeps the two-constructor
split every earlier family was proved against.

**As of stage I, `.parameterVar` no longer means only a parameter.** It means
**a name that is not a state variable**, and it covers message-server
parameters and local variables alike. That is one of stage I's approved rulings
(`docs/decisions/0047-local-declarations-in-the-fragment.md`), and the argument
is about the target rather than about cost: the emitted C++ binds a parameter
and a local to a bare identifier in the same reaction block, so a read that
could not tell the two apart could not compile to the text this development
actually emits. The split that remains load-bearing is `.stateVar` versus
everything else, because only a state variable survives the reaction boundary.

There is no constructor mentioning `KnownRebecName`. That is what makes "a known
rebec used as a value" unrepresentable rather than merely checked: a known rebec
can appear only as a send target.

Expression type-correctness is not enforced anywhere in this family. It is not
one of the restrictions this development owes, because the operator set above is
this project's own choice rather than a fragment restriction, and because the
upstream typechecker rejects ill-typed expressions before a document is emitted.
Adding a typing judgement later is a scoped addition; leaving unused typing
machinery here would repeat a pattern this family exists to correct.
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
      DTR.GeneralBinaryOp →
      GeneralExpr →
      GeneralExpr →
      GeneralExpr

  | unary :
      DTR.GeneralUnaryOp →
      GeneralExpr →
      GeneralExpr

deriving Repr, DecidableEq, BEq, Inhabited


/--
Where a send is directed.

The frontend emits one `send` node whose target discriminator is either `self`
or a named known rebec, and this syntax mirrors that shape rather than splitting
self-sends into their own statement. One constructor means a traversal cannot
handle self-sends and forget external ones, and it gives the existing
`selfSendNotExternal` failure a real traversal to fire on instead of only a
hand-built adapter record.
-/
inductive GeneralSendTarget where
  | selfTarget

  | knownRebec :
      KnownRebecName →
      GeneralSendTarget

deriving Repr, DecidableEq, BEq, Inhabited

/--
A general statement.

The delay is a `Delay` rather than an optional one. The frontend carries an
absent `after` through as null because its output is an abstract syntax tree,
and applying the zero default is this side's responsibility; the elaborator
does it, so by the time a statement exists the delay is always present.

`trace` carries a literal tag for generated target output. It is intentionally
part of the syntax before any executable trace semantics: this milestone wires
the tag through translation and printing, while the target printer remains the
owner of the observable output.

`ifThenElse` carries a condition and two branch bodies, spelled `List GeneralStmt`
rather than `GeneralBody` because the abbreviation is declared after this
inductive; the two are the same type, since `GeneralBody` is reducible. The
constructor makes the type recursive, so a body is no longer flat, and
`docs/decisions/0046-send-site-identity-under-nested-control-flow.md` records
why that is the approved shape: a send site is a *position*, and no alternative
that stores an identifier on a statement was accepted. An `if` without an `else`
is represented with an empty second branch rather than an option, so a branch is
always a body and every traversal has one fewer case to consider.

**No semantics accompanied this constructor when stage H added it, and the period
without them is over.** From stage H until stage I0 the frontend refused
branching, so no well-formed source document could contain a conditional and the
accepted fragment was unchanged; stage I0 lifted that, and the constructor now
has source step rules, target statements, a runtime frame stack and path-based
send-site threading, all landed with stage H and accepted with stage I0. The
refusal period is recorded because its shape is reused one paragraph down.

`localDecl` is in that refusal period, partway through it. It carries a name, a declared type
and a **required** initialiser expression: the frontend applies the declared type's
`initialValue` when the source omits one, exactly as it already applies the zero default for
an absent `after`, so by the time a statement exists the initialiser is always present. The
local-read design decision is one of stage I's approved rulings, to be recorded in a decision
record by the stage's documentation layer: a local is read through the existing
`.parameterVar` constructor, which is the accurate model of the emitted target rather than an
overload, because `renderGeneralParameterRead` already emits a block-scoped C++ binding under
the source name. **No guard accepts the constructor yet, and the translator compiles it.**
Stage I's S-I3 layer gave `compileGeneralStmt` its arm, so a local declaration now survives
translation into `LF.GeneralStmt.localDecl`; what still refuses it are the two
well-formedness clauses (`statementResolves`, `statementTargetDeclared`) and the frontend,
which still raises `localDeclarationNotSupported`. So no well-formed source document contains
one — the accepted fragment is unchanged — but a hand-built model that does contain one now
compiles rather than erroring, which is the ordering stage H and I0 proved out and the reason
`exists_compileGeneralBody` stayed true: the guards admit the construct only after the
translator compiles it.
-/
inductive GeneralStmt where
  | assign :
      VarName →
      DTR.GeneralExpr →
      GeneralStmt

  | trace :
      String →
      GeneralStmt

  | send :
      DTR.GeneralSendTarget →
      MsgName →
      List DTR.GeneralExpr →
      Delay →
      GeneralStmt

  | ifThenElse :
      DTR.GeneralExpr →
      List GeneralStmt →
      List GeneralStmt →
      GeneralStmt

  | localDecl :
      VarName →
      DTR.GeneralType →
      DTR.GeneralExpr →
      GeneralStmt

deriving Repr, BEq, Inhabited

/--
A statement sequence.

This was a flat list until stage H added `GeneralStmt.ifThenElse`. The
*container* is still `List`, and that is deliberate: the element type became
recursive instead, so `compileGeneralBody`'s `nil` and `cons` equations and every
list operation on a body survive at each nesting level. What changed is that a
body is now a tree when read through its statements, and a statement's position
within one body no longer identifies it across a whole message server. The
replacement notion of identity is a path, per
`docs/decisions/0046-send-site-identity-under-nested-control-flow.md`.

The original note here recorded that the stage admitting branching *"has to
change this type, and that change is a build error at every function that walks
a body rather than a silent default branch"*. That prediction held: adding the
constructor produced build errors at the traversals rather than silent
misbehaviour, which is why the type was left this shape.
-/
abbrev GeneralBody := List DTR.GeneralStmt

/-
Decidable equality for a general statement and for a body is written by hand
below. The docstrings sit on the two definitions rather than on the `mutual`
block, because a `mutual` block does not accept one.
-/
mutual

/--
Decide equality of two general statements.

**Not derived, and the reason is a toolchain limitation rather than a preference.**
`GeneralStmt.ifThenElse` carries `List GeneralStmt`, which makes the type a
*nested* inductive, and Lean 4.32's `DecidableEq` deriving handler does not apply
to one: it reports *"None of the deriving handlers for class `DecidableEq` applied
to `GeneralStmt`"*. Confirmed against this toolchain rather than assumed, including
that the standalone `deriving instance DecidableEq for ...` command fails the same
way. `Repr`, `BEq` and `Inhabited` all still derive, so those stay on the
`deriving` clause of the inductive and only this one instance is manual.

This is mutually recursive with `decEqGeneralBody` because the type is: deciding
equality of two `ifThenElse` statements requires deciding equality of their branch
bodies, and deciding equality of two bodies requires deciding equality of their
head statements.

Every arm is exhaustive over both arguments with no wildcard on the pair, for the
same reason the traversals in `Translation.GeneralRouting` avoid one: a later stage
that adds a statement should get a build error here rather than a `false` that
looks like a decision.
-/
def decEqGeneralStmt :
    (first second : DTR.GeneralStmt) →
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
  | .assign _ _, .send _ _ _ _ => .isFalse (by simp)
  | .assign _ _, .ifThenElse _ _ _ => .isFalse (by simp)
  | .assign _ _, .localDecl _ _ _ => .isFalse (by simp)

  | .trace firstTag, .trace secondTag =>
      if hTag : firstTag = secondTag then
        .isTrue (by subst hTag; rfl)
      else
        .isFalse (by simp [hTag])

  | .trace _, .assign _ _ => .isFalse (by simp)
  | .trace _, .send _ _ _ _ => .isFalse (by simp)
  | .trace _, .ifThenElse _ _ _ => .isFalse (by simp)
  | .trace _, .localDecl _ _ _ => .isFalse (by simp)

  | .send firstTarget firstMessage firstArguments firstDelay,
    .send secondTarget secondMessage secondArguments secondDelay =>
      if hTarget : firstTarget = secondTarget then
        if hMessage : firstMessage = secondMessage then
          if hArguments : firstArguments = secondArguments then
            if hDelay : firstDelay = secondDelay then
              .isTrue
                (by
                  subst hTarget
                  subst hMessage
                  subst hArguments
                  subst hDelay
                  rfl)
            else
              .isFalse (by simp [hDelay])
          else
            .isFalse (by simp [hArguments])
        else
          .isFalse (by simp [hMessage])
      else
        .isFalse (by simp [hTarget])

  | .send _ _ _ _, .assign _ _ => .isFalse (by simp)
  | .send _ _ _ _, .trace _ => .isFalse (by simp)
  | .send _ _ _ _, .ifThenElse _ _ _ => .isFalse (by simp)
  | .send _ _ _ _, .localDecl _ _ _ => .isFalse (by simp)

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
  | .ifThenElse _ _ _, .send _ _ _ _ => .isFalse (by simp)
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
  | .localDecl _ _ _, .send _ _ _ _ => .isFalse (by simp)
  | .localDecl _ _ _, .ifThenElse _ _ _ => .isFalse (by simp)

/--
Decide equality of two statement bodies.

A `List` decision procedure specialised to this element type rather than an appeal
to the generic `List` instance, because the generic one needs
`DecidableEq GeneralStmt` as an instance argument, which is exactly what
`decEqGeneralStmt` is defining.
-/
def decEqGeneralBody :
    (first second : DTR.GeneralBody) →
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

instance : DecidableEq DTR.GeneralStmt := decEqGeneralStmt


/--
A state variable declaration.

There is no initializer field. A source-level initializer is rejected before a
frontend document is emitted, and omitting the field here is what re-establishes
that restriction in this development: the rejected program cannot be written as
a term of this type. The initial valuation comes from the declared type.
-/
structure GeneralStateVariableDecl where
  name :
    VarName

  declaredType :
    DTR.GeneralType

deriving Repr, DecidableEq, BEq, Inhabited

/--
A typed formal parameter of a constructor or a message server.

Declared types are carried because instance arguments have to be checked against
constructor parameters, and because a payload can now hold booleans as well as
integers.
-/
structure GeneralTypedParameter where
  name :
    VarName

  declaredType :
    DTR.GeneralType

deriving Repr, DecidableEq, BEq, Inhabited

/--
One declared known rebec of a reactive class.

The declared class is what makes a send's receiving class computable, and hence
what makes it possible to check that the named message server exists.
-/
structure GeneralKnownRebecDecl where
  name :
    KnownRebecName

  className :
    ClassName

deriving Repr, DecidableEq, BEq, Inhabited


/--
A constructor of a reactive class.

Unlike every earlier family, this one has parameters. They are what instance
arguments are checked against.
-/
structure GeneralConstructor where
  parameters :
    List DTR.GeneralTypedParameter

  body :
    DTR.GeneralBody

deriving Repr, DecidableEq, BEq, Inhabited

/--
A message server.

`priority` is local message-server priority. An absent priority is a priority
class in its own right and is ordered after every explicit one, which is the
convention the earlier payload family already fixed.
-/
structure GeneralMessageServer where
  name :
    MsgName

  parameters :
    List DTR.GeneralTypedParameter

  body :
    DTR.GeneralBody

  priority :
    Option Nat :=
      none

deriving Repr, DecidableEq, BEq, Inhabited

/--
A reactive class.

A class may declare no known rebecs, no state variables and no message servers.
All three are needed to accept the paper's own figures, and each is recorded as
a considered divergence from its grammar rather than an unimplemented check.
-/
structure GeneralReactiveClass where
  name :
    ClassName

  knownRebecs :
    List DTR.GeneralKnownRebecDecl

  stateVariables :
    List DTR.GeneralStateVariableDecl

  constructor :
    DTR.GeneralConstructor

  messageServers :
    List DTR.GeneralMessageServer

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralReactiveClass

/--
The declared priorities of a class's message servers, in declaration order.

An absent priority is retained as `none` rather than dropped, because absence is
a priority class and two absences are a tie.
-/
def messageServerPriorities
    (reactiveClass : DTR.GeneralReactiveClass) :
    List (Option Nat) :=
  reactiveClass.messageServers.map
    (fun messageServer =>
      messageServer.priority)

end GeneralReactiveClass


/--
An actor instance.

`bindings` is the per-instance known-rebec binding store, and it is the field
whose absence made the topology of every earlier family empty. With it decoded,
known-rebec resolution can succeed, which is what the external-send layer needs
in order to be reachable from a frontend document at all.

`arguments` are the positional constructor arguments. `priority` is actor-level
priority and is independent of message-server priority.
-/
structure GeneralActorInstance where
  name :
    ActorName

  className :
    ClassName

  bindings :
    KnownRebecBindings

  arguments :
    List DTR.GeneralValue

  priority :
    Option Nat :=
      none

deriving Repr, DecidableEq, BEq, Inhabited

/--
A complete general model.

The topology is not a field. It is derived from `instances`, so a model cannot
carry a topology that disagrees with the instances it describes, and the class of
well-formedness obligation that guarded that agreement in the earlier global
family does not arise here.
-/
structure GeneralModel where
  classes :
    List DTR.GeneralReactiveClass

  instances :
    List DTR.GeneralActorInstance

deriving Repr, DecidableEq, BEq, Inhabited

/--
Find a declared known rebec by name.

The four lookups below are written as explicit recursion over decidable equality
rather than through `List.find?` on `BEq`. Deriving `DecidableEq` and `BEq`
independently does not produce a lawfulness bridge between them, and `Store`
lookup is already stated in terms of decidable equality, so keeping one notion of
equality throughout is what lets the topology lemma below be proved at all.
-/
def findKnownRebec? :
    List DTR.GeneralKnownRebecDecl →
    KnownRebecName →
    Option DTR.GeneralKnownRebecDecl

  | [], _ =>
      none

  | declaration :: remaining, knownRebec =>
      if declaration.name = knownRebec then
        some declaration
      else
        findKnownRebec?
          remaining
          knownRebec

/--
Find a declared message server by name.
-/
def findMessageServer? :
    List DTR.GeneralMessageServer →
    MsgName →
    Option DTR.GeneralMessageServer

  | [], _ =>
      none

  | messageServer :: remaining, messageName =>
      if messageServer.name = messageName then
        some messageServer
      else
        findMessageServer?
          remaining
          messageName

/--
Find a reactive class by name.
-/
def findClass? :
    List DTR.GeneralReactiveClass →
    ClassName →
    Option DTR.GeneralReactiveClass

  | [], _ =>
      none

  | reactiveClass :: remaining, className =>
      if reactiveClass.name = className then
        some reactiveClass
      else
        findClass?
          remaining
          className

/--
Find an actor instance by name.
-/
def findActor? :
    List DTR.GeneralActorInstance →
    ActorName →
    Option DTR.GeneralActorInstance

  | [], _ =>
      none

  | actor :: remaining, actorName =>
      if actor.name = actorName then
        some actor
      else
        findActor?
          remaining
          actorName

namespace GeneralReactiveClass

/--
Find a known rebec this class declares.
-/
def knownRebec?
    (reactiveClass : DTR.GeneralReactiveClass)
    (knownRebec : KnownRebecName) :
    Option DTR.GeneralKnownRebecDecl :=
  DTR.findKnownRebec?
    reactiveClass.knownRebecs
    knownRebec

/--
Find a message server this class declares.
-/
def messageServer?
    (reactiveClass : DTR.GeneralReactiveClass)
    (messageName : MsgName) :
    Option DTR.GeneralMessageServer :=
  DTR.findMessageServer?
    reactiveClass.messageServers
    messageName

end GeneralReactiveClass

namespace GeneralModel

/--
Find a class this model declares.
-/
def class?
    (model : DTR.GeneralModel)
    (className : ClassName) :
    Option DTR.GeneralReactiveClass :=
  DTR.findClass?
    model.classes
    className

/--
Find an actor this model instantiates.
-/
def actor?
    (model : DTR.GeneralModel)
    (actorName : ActorName) :
    Option DTR.GeneralActorInstance :=
  DTR.findActor?
    model.instances
    actorName

/--
The class of a named actor, when both the actor and its class exist.
-/
def classOfActor?
    (model : DTR.GeneralModel)
    (actorName : ActorName) :
    Option DTR.GeneralReactiveClass :=
  match model.actor? actorName with

  | none =>
      none

  | some actor =>
      model.class? actor.className

/--
The topology this model describes.

Derived rather than stored, in main-block declaration order.
-/
def topology
    (model : DTR.GeneralModel) :
    ActorTopology :=
  model.instances.map
    (fun actor =>
      (
        actor.name,
        actor.bindings
      ))

/--
The declared actor priorities, in main-block declaration order.

As with message servers, an absent priority is retained as `none`.
-/
def actorPriorities
    (model : DTR.GeneralModel) :
    List (Option Nat) :=
  model.instances.map
    (fun actor =>
      actor.priority)

private theorem lookup_topologyOf
    (instances : List DTR.GeneralActorInstance)
    (actorName : ActorName) :
    Store.lookup
        (instances.map
          (fun actor =>
            (
              actor.name,
              actor.bindings
            )))
        actorName =
      (DTR.findActor? instances actorName).map
        (fun actor =>
          actor.bindings) := by

  induction instances with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      by_cases hHead :
          head.name = actorName

      · simp [
          Store.lookup,
          DTR.findActor?,
          hHead
        ]

      · simp [
          Store.lookup,
          DTR.findActor?,
          hHead,
          inductionHypothesis
        ]

/--
Topology lookup agrees with the instance it was derived from.

This is the payoff of deriving the topology instead of storing it: the two cannot
disagree, and the agreement is a lemma rather than a well-formedness obligation.
-/
theorem lookup_topology
    (model : DTR.GeneralModel)
    (actorName : ActorName) :
    Store.lookup
        model.topology
        actorName =
      (model.actor? actorName).map
        (fun actor =>
          actor.bindings) := by
  unfold topology actor?
  exact
    lookup_topologyOf
      model.instances
      actorName

/--
Known-rebec resolution succeeds through the derived topology whenever the sender
exists and binds that name.

This is the statement the external-send layer needs and could never obtain from a
decoded model before this family, because every earlier decoder gave every actor
an empty binding store and so made resolution fail unconditionally.
-/
theorem resolve_topology_of_actor
    (model : DTR.GeneralModel)
    (sender : ActorName)
    (knownRebec : KnownRebecName)
    (actor : DTR.GeneralActorInstance)
    (hActor :
      model.actor? sender =
        some actor) :
    ActorTopology.resolve
        model.topology
        sender
        knownRebec =
      Store.lookup
        actor.bindings
        knownRebec := by

  simp [
    ActorTopology.resolve,
    lookup_topology,
    hActor
  ]

/--
Resolution fails when the sender is not an instance of the model.
-/
theorem resolve_topology_of_missing
    (model : DTR.GeneralModel)
    (sender : ActorName)
    (knownRebec : KnownRebecName)
    (hActor :
      model.actor? sender =
        none) :
    ActorTopology.resolve
        model.topology
        sender
        knownRebec =
      none := by

  simp [
    ActorTopology.resolve,
    lookup_topology,
    hActor
  ]

end GeneralModel


end DTR
end Relico
