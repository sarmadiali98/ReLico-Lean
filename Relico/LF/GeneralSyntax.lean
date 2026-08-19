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
family adds them, and nothing else. It does not add control flow, it does not
widen the value domain, and it does not touch `Relico.Payload`, which is
load-bearing for the proofs the earlier families already carry.

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
A general expression in generated LF.

Three constructors, the same three the payload family already carries. There is
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

The asymmetry with `DTR.GeneralExpr` — which carries boolean literals, binary
operators and unary operators — is deliberate, and the debt it creates is recorded
here rather than pre-empted. No printer in this development can emit an operator,
so widening this type now would produce a construct nothing can print. The stage
that writes the translation is the one that has to either widen this type or
restrict its own domain, and leaving the two sides visibly unequal is what forces
that choice to be made in the open instead of inside a default branch.
-/
inductive GeneralExpr where
  | intLiteral :
      Int →
      GeneralExpr

  | stateVar :
      VarName →
      GeneralExpr

  | parameterVar :
      VarName →
      GeneralExpr

deriving Repr, DecidableEq, BEq, Inhabited


/--
A general reaction statement.

`setPort` takes one expression while `schedule` takes a list, and that asymmetry
is the paper's: `LFStmt ::= outPort([Expr])?.set(Expr);` admits exactly one value,
while a typed logical action's payload arity follows the parameter list of the
message server it was derived from. Keeping `schedule`'s argument list unbounded
also keeps the translation total and the printer partial, which is the split this
repository already has — a multi-value action payload is refused in the C++
printer, so the external-send stage inherits that refusal site instead of having
to make its translation return `Except`.

The delay on `schedule` is a `Delay` rather than an optional one, matching the DTR
side: an absent `after` has already had the zero default applied by the time a
statement exists.

There is no `if` and no `for`. Fig. 5's `LFStmt` has both. Control flow is a later
stage on both sides at once, and adding the LF half alone would create a construct
nothing can produce.
-/
inductive GeneralStmt where
  | assign :
      VarName →
      LF.GeneralExpr →
      GeneralStmt

  | schedule :
      ActionName →
      List LF.GeneralExpr →
      Delay →
      GeneralStmt

  | setPort :
      PortName →
      LF.GeneralExpr →
      GeneralStmt

deriving Repr, DecidableEq, BEq, Inhabited

/--
A statement sequence.

Flat on purpose, exactly as on the DTR side: the stage that admits branching has
to change this type, and that change is a build error at every function that walks
a body rather than a silent default branch.
-/
abbrev GeneralBody :=
  List LF.GeneralStmt

/--
A generated typed logical-action declaration.

The ordered field names mirror source formal-parameter order, and the value domain
is integer-only, as in the payload family this borrows its shape from.
-/
structure GeneralAction where
  name :
    ActionName

  parameters :
    List VarName

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

`priority` is carried and never consulted. Priority distinctness is a theorem
hypothesis rather than a well-formedness conjunct — the settled decision — so
well-formedness must not mention this field, and neither may the printer, which
honours declaration *order* instead. It is here so that the later stage which
makes priority observable has somewhere to attach it.

`name` identifies a reaction inside Lean and nothing else. LF reactions are
anonymous in concrete syntax: a printer emits `reaction(<trigger>)` and never the
name, so uniqueness of this field is deliberately not required anywhere. Requiring
it would constrain an identifier the target language never sees.
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

Ports are plain `List PortName`: no width field and no payload field. Fig. 5's
`PortDecl` admits a multiport width `([intLiteral])?`, but `lfc 0.11.0` rejects
`reaction(in[0])` and a whole-multiport trigger fires once per tag regardless of
channel count, so multiports cannot implement the paper's receiver-side fan-in and
named ports are forced. Omitting the width field is what makes the rejected
construct unrepresentable rather than merely unused. There is no payload field
because every port in the paper and in the fixtures carries exactly one integer —
Fig. 1b writes `reading.set(0)` for a *parameterless* message, and §II-B explains
that *"the value 0 is a dummy value used only to trigger the parameterless
destination reaction"*, so there is no zero-payload port to distinguish.

Input ports, output ports, state variables and logical actions are four lists but
**one** name scope. An LF reactor does not let `input v` and `state v` coexist, so
the uniqueness obligation over them is a single check over the union rather than
four per-list checks; four checks would accept a program no LF compiler will.

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

  inputPorts :
    List PortName

  outputPorts :
    List PortName

  stateVariables :
    List LF.StateVariableDecl

  logicalActions :
    List LF.GeneralAction

  startupReaction :
    LF.GeneralReaction

  messageReactions :
    List LF.GeneralReaction

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
    List LF.ReactorInstance

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
    List LF.ReactorInstance →
    ActorName →
    Option LF.ReactorInstance

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
    Option LF.ReactorInstance :=
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

end LF
end Relico
