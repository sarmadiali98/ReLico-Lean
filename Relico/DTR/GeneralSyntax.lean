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

deriving Repr, DecidableEq, BEq, Inhabited

/--
A statement sequence.

This is a flat list on purpose. The stage that admits branching and iteration
has to change this type, and that change is a build error at every function
that walks a body rather than a silent default branch.
-/
abbrev GeneralBody := List DTR.GeneralStmt


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
