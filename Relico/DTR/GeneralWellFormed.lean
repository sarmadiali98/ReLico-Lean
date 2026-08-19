import Relico.DTR.GeneralSyntax

set_option autoImplicit false

namespace Relico
namespace DTR

/-!
# Well-formedness for the general fragment

`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md` lists eight restrictions that
the upstream Rebeca parser and typechecker enforce before a frontend document
exists. Upstream enforcement makes them *less* covered here, not more: nothing
between a JSON document and this development typechecks anything, so all eight
come due again. They are discharged three different ways, and the split matters
because a restriction made unrepresentable is stronger than one that is tested.

Two are unrepresentable, so no clause appears below. An initialized state
variable cannot be written, because `GeneralStateVariableDecl` has no
initializer field. A known rebec used as a value cannot be written, because no
`GeneralExpr` constructor mentions `KnownRebecName`.

Two are consequences of scope resolution and belong to the elaborator: a read of
the implicit `sender`, and a send to it. Both hold only while the elaborator's
scope stays exactly the declared state variables and parameters, so the coverage
is conditional on a negative and is recorded at the scope function itself.

Four are real clauses here, and one more is added: `namesUniqueAndValid`. That
fifth clause is not one of the eight and was not in the approved design. It is
here because deriving the topology from the instances makes the two agree but
does not make either unique, while `ActorTopology.wellFormed` requires
`Store.KeysUnique` of both, and because all four lookups in `GeneralSyntax`
return the first match and so are ambiguous under a repeated name.

Priority distinctness is deliberately **not** part of `wellFormed`. It is stated
separately as a `Prop` with a decision procedure, to be taken as an explicit
hypothesis by the correctness theorems that need selection to be deterministic.
A theorem that needs determinism and does not name one of these predicates is a
bug in that theorem. The measured consequence of the alternative was that
five of the nine frontend positives would stop being decodable.

One narrowing is recorded rather than hidden. `sendsResolveToMessageServers`
checks payload arity but not payload types, because a send carries expressions
rather than values and typing them needs a judgement this family deliberately
does not have. Send payload typing is not one of the eight; instance argument
typing is, and that one is checked, because arguments are values.
-/

namespace GeneralReactiveClass

/--
Every statement sequence a class contains, constructor body first.

Bodies are flat lists, so a whole-class traversal is `List.all` over this list of
lists. When branching and iteration arrive, this definition changes, and every
traversal built on it fails to compile rather than quietly skipping a nested
statement.
-/
def bodies
    (reactiveClass : DTR.GeneralReactiveClass) :
    List DTR.GeneralBody :=
  reactiveClass.constructor.body ::
    reactiveClass.messageServers.map
      (fun messageServer =>
        messageServer.body)

/--
A statement's send target, if it has one, is a known rebec this class declares.

A self-send needs nothing declared, which is why the two targets are not treated
uniformly here even though they share one statement constructor.
-/
def statementTargetDeclared
    (reactiveClass : DTR.GeneralReactiveClass)
    (statement : DTR.GeneralStmt) :
    Bool :=
  match statement with

  | .assign _ _ =>
      true

  | .send target _ _ _ =>
      match target with

      | .selfTarget =>
          true

      | .knownRebec knownRebec =>
          (reactiveClass.knownRebec? knownRebec).isSome

/--
One class satisfies D6: every external send it contains names a known rebec it
declares.
-/
def targetsDeclared
    (reactiveClass : DTR.GeneralReactiveClass) :
    Bool :=
  reactiveClass.bodies.all
    (fun body =>
      body.all
        (fun statement =>
          reactiveClass.statementTargetDeclared
            statement))

end GeneralReactiveClass

/--
D8 for one argument list: the arguments match the declared parameters in count
and in type.

Count and type agreement are one recursion rather than a length comparison
followed by a pairwise walk, so a length disagreement can never be reported as a
type disagreement. This check is possible without a typing judgement only
because instance arguments are values; send payloads are expressions, and they
are checked for arity alone.
-/
def argumentsMatchParameters :
    List DTR.GeneralValue →
    List DTR.GeneralTypedParameter →
    Bool

  | [], [] =>
      true

  | value :: remainingValues, parameter :: remainingParameters =>
      DTR.GeneralValue.hasType
          value
          parameter.declaredType &&
        argumentsMatchParameters
          remainingValues
          remainingParameters

  | _, _ =>
      false


namespace GeneralModel

/--
One instance's bindings agree with its class's declarations.

Two things are checked, and the second is what an arity check alone would miss.
The bound name sequence must equal the declared name sequence, order included:
the frontend emits bindings in declaration order and its own validator checks
that order, so agreeing here keeps one notion of matching across the two layers.
Then every bound actor must exist and must instantiate the class the declaration
names, which is the fact that makes a send's receiving class computable.
-/
def bindingsMatchClass
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance)
    (reactiveClass : DTR.GeneralReactiveClass) :
    Bool :=
  (Store.keys actor.bindings ==
      reactiveClass.knownRebecs.map
        (fun declaration =>
          declaration.name)) &&
    reactiveClass.knownRebecs.all
      (fun declaration =>
        match Store.lookup actor.bindings declaration.name with

        | none =>
            false

        | some target =>
            match model.classOfActor? target with

            | none =>
                false

            | some targetClass =>
                targetClass.name == declaration.className)

/--
Every instance instantiates a declared class and binds exactly what that class
declares.

The class of every instance existing is not stated separately. It is a
precondition of every other clause, so it is checked wherever a class is looked
up, and a missing class fails this one first.
-/
def bindingsMatchDeclarations
    (model : DTR.GeneralModel) :
    Bool :=
  model.instances.all
    (fun actor =>
      match model.class? actor.className with

      | none =>
          false

      | some reactiveClass =>
          model.bindingsMatchClass
            actor
            reactiveClass)

/--
Every instance's arguments match its class's constructor parameters.
-/
def argumentsMatchConstructor
    (model : DTR.GeneralModel) :
    Bool :=
  model.instances.all
    (fun actor =>
      match model.class? actor.className with

      | none =>
          false

      | some reactiveClass =>
          DTR.argumentsMatchParameters
            actor.arguments
            reactiveClass.constructor.parameters)

/--
D6 across the model.

This is the restriction that makes a message server's set of possible senders
statically computable, so it is load-bearing for the translation stages rather
than hygienic.
-/
def sendTargetsDeclared
    (model : DTR.GeneralModel) :
    Bool :=
  model.classes.all
    (fun reactiveClass =>
      reactiveClass.targetsDeclared)

/--
The class that receives a send issued inside a given class.

A self-send resolves to the sending class. An external send resolves through the
declared class of the named known rebec, not through any instance, so the answer
is a property of the classes alone.
-/
def receivingClass?
    (model : DTR.GeneralModel)
    (reactiveClass : DTR.GeneralReactiveClass)
    (target : DTR.GeneralSendTarget) :
    Option DTR.GeneralReactiveClass :=
  match target with

  | .selfTarget =>
      some reactiveClass

  | .knownRebec knownRebec =>
      match reactiveClass.knownRebec? knownRebec with

      | none =>
          none

      | some declaration =>
          model.class? declaration.className

/--
One statement's send, if it has one, names a message server the receiving class
declares, with a payload of the declared arity.
-/
def statementResolves
    (model : DTR.GeneralModel)
    (reactiveClass : DTR.GeneralReactiveClass)
    (statement : DTR.GeneralStmt) :
    Bool :=
  match statement with

  | .assign _ _ =>
      true

  | .send target messageName payload _ =>
      match model.receivingClass? reactiveClass target with

      | none =>
          false

      | some receivingClass =>
          match receivingClass.messageServer? messageName with

          | none =>
              false

          | some messageServer =>
              payload.length ==
                messageServer.parameters.length

/--
Every send in the model reaches a declared message server.

This is the one clause that cannot be checked class-locally, and it is possible
only because instance bindings are decoded: with the empty binding stores of the
earlier families there is no receiving class to look at.
-/
def sendsResolveToMessageServers
    (model : DTR.GeneralModel) :
    Bool :=
  model.classes.all
    (fun reactiveClass =>
      reactiveClass.bodies.all
        (fun body =>
          body.all
            (fun statement =>
              model.statementResolves
                reactiveClass
                statement)))


/--
Names that a lookup depends on are unique, and the names an actor topology must
supply are non-empty.

This clause is not one of the eight and was not in the approved design. It is
here because every lookup in `GeneralSyntax` returns the first match, so a
repeated class, instance, known-rebec or message-server name makes the model
mean something the frontend did not say; and because `ActorTopology.wellFormed`
requires `Store.KeysUnique` of the topology and non-empty actor and known-rebec
names, none of which deriving the topology supplies.

Uniqueness of the topology's keys is stated through `model.topology` rather than
through the instance names directly, so that it is literally the proposition the
existing topology predicate asks for. Parameter and state-variable names are
deliberately absent: their uniqueness is what makes a scope unambiguous, which
is the elaborator's concern and is reported as a diagnostic there.
-/
def namesUniqueAndValid
    (model : DTR.GeneralModel) :
    Bool :=
  decide
      (Store.KeysUnique
        model.topology) &&
    decide
      ((model.classes.map
        (fun reactiveClass =>
          reactiveClass.name)).Nodup) &&
    model.instances.all
      (fun actor =>
        actor.name.value != "") &&
    model.classes.all
      (fun reactiveClass =>
        (reactiveClass.name.value != "") &&
          decide
            ((reactiveClass.knownRebecs.map
              (fun declaration =>
                declaration.name)).Nodup) &&
          decide
            ((reactiveClass.messageServers.map
              (fun messageServer =>
                messageServer.name)).Nodup) &&
          reactiveClass.knownRebecs.all
            (fun declaration =>
              declaration.name.value != ""))


/--
A well-formed general model.

Priority is absent by decision: distinctness of priorities is a hypothesis of
those correctness theorems that need deterministic selection, rather than a
condition on being decodable at all.
-/
def wellFormed
    (model : DTR.GeneralModel) :
    Bool :=
  model.bindingsMatchDeclarations &&
    model.argumentsMatchConstructor &&
    model.sendTargetsDeclared &&
    model.sendsResolveToMessageServers &&
    model.namesUniqueAndValid


/-!
### Extraction

One lemma per clause, so a later stage consumes the clause it needs instead of
destructuring a conjunction at every use. There is deliberately no monolithic
`wellFormed = true ↔ …` theorem: it would buy nothing these five do not, at the
cost of a large proof.

Each proof is a Bool case analysis on its own clause rather than a projection out
of a conjunction, so that it does not depend on how `&&` associates. That is not
a matter of taste. A projection chain reads a fixed nesting shape, and under the
other associativity the same chain proves a different clause while still
compiling, which is the kind of error a build cannot report.
-/

theorem bindingsMatchDeclarations_of_wellFormed
    (model : DTR.GeneralModel)
    (hWellFormed :
      model.wellFormed =
        true) :
    model.bindingsMatchDeclarations =
      true := by
  revert hWellFormed
  unfold wellFormed
  cases model.bindingsMatchDeclarations <;> simp

theorem argumentsMatchConstructor_of_wellFormed
    (model : DTR.GeneralModel)
    (hWellFormed :
      model.wellFormed =
        true) :
    model.argumentsMatchConstructor =
      true := by
  revert hWellFormed
  unfold wellFormed
  cases model.argumentsMatchConstructor <;> simp

theorem sendTargetsDeclared_of_wellFormed
    (model : DTR.GeneralModel)
    (hWellFormed :
      model.wellFormed =
        true) :
    model.sendTargetsDeclared =
      true := by
  revert hWellFormed
  unfold wellFormed
  cases model.sendTargetsDeclared <;> simp

theorem sendsResolveToMessageServers_of_wellFormed
    (model : DTR.GeneralModel)
    (hWellFormed :
      model.wellFormed =
        true) :
    model.sendsResolveToMessageServers =
      true := by
  revert hWellFormed
  unfold wellFormed
  cases model.sendsResolveToMessageServers <;> simp

theorem namesUniqueAndValid_of_wellFormed
    (model : DTR.GeneralModel)
    (hWellFormed :
      model.wellFormed =
        true) :
    model.namesUniqueAndValid =
      true := by
  revert hWellFormed
  unfold wellFormed
  cases model.namesUniqueAndValid <;> simp

end GeneralModel


namespace GeneralMessageServers

/--
The general fragment forbids equal local priorities within a class.

Because an absent priority is itself a priority class, this condition also
permits at most one unannotated message server per class. It is stated over the
priority list rather than over the servers so that it is the same predicate the
earlier payload family already fixed, and so that the ordering it strengthens —
a total preorder in which every explicit priority precedes `none` — becomes a
strict total order exactly when it holds.
-/
def PrioritiesDistinct
    (messageServers :
      List DTR.GeneralMessageServer) :
    Prop :=
  (messageServers.map
    (fun messageServer =>
      messageServer.priority)).Nodup

/--
The condition is executable, because priority metadata has decidable equality.
-/
instance prioritiesDistinctDecidable
    (messageServers :
      List DTR.GeneralMessageServer) :
    Decidable
      (PrioritiesDistinct
        messageServers) := by
  unfold PrioritiesDistinct
  infer_instance

end GeneralMessageServers

namespace GeneralActorInstances

/--
Actor-level priorities are pairwise distinct.

This is the same condition one level up, and it is independent of the
message-server one: a model may satisfy either without the other.
-/
def PrioritiesDistinct
    (instances :
      List DTR.GeneralActorInstance) :
    Prop :=
  (instances.map
    (fun actor =>
      actor.priority)).Nodup

/--
Executable for the same reason.
-/
instance prioritiesDistinctDecidable
    (instances :
      List DTR.GeneralActorInstance) :
    Decidable
      (PrioritiesDistinct
        instances) := by
  unfold PrioritiesDistinct
  infer_instance

end GeneralActorInstances

namespace GeneralModel

/--
Every class orders its own message servers strictly.

Distinctness is per class, not model-wide: two classes may both annotate a server
`1`, because local priority orders the reactions of one actor.
-/
def MessageServerPrioritiesDistinct
    (model : DTR.GeneralModel) :
    Prop :=
  ∀ reactiveClass ∈ model.classes,
    DTR.GeneralMessageServers.PrioritiesDistinct
      reactiveClass.messageServers

/--
Decidable, so a fixture can settle it by computation.
-/
instance messageServerPrioritiesDistinctDecidable
    (model : DTR.GeneralModel) :
    Decidable
      (MessageServerPrioritiesDistinct
        model) := by
  unfold MessageServerPrioritiesDistinct
  infer_instance

/--
The model orders its actors strictly.

This is model-wide, unlike the message-server condition, because actor priority
orders actors against each other.
-/
def ActorPrioritiesDistinct
    (model : DTR.GeneralModel) :
    Prop :=
  DTR.GeneralActorInstances.PrioritiesDistinct
    model.instances

/--
Decidable for the same reason.
-/
instance actorPrioritiesDistinctDecidable
    (model : DTR.GeneralModel) :
    Decidable
      (ActorPrioritiesDistinct
        model) := by
  unfold ActorPrioritiesDistinct
  infer_instance

end GeneralModel


end DTR
end Relico
