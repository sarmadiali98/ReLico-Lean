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

/- `statementTargetDeclared` and `bodyTargetsDeclared` are a mutual pair as of stage I0, because a
conditional's branches are bodies. A `mutual` block cannot carry a docstring, so each definition
carries its own. -/
mutual

/--
A statement's send target, if it has one, is a known rebec this class declares.

A self-send needs nothing declared, which is why the two targets are not treated
uniformly here even though they share one statement constructor.

**`ifThenElse` is the recursive arm as of stage I0.** It was a `false` arm from stage H until then,
and the reason it was right to refuse is worth keeping, because it is the reason this arm is a
recursion and not a `true`. Stage H added the constructor to `DTR.GeneralStmt` before any of the
machinery that would make a branch meaningful, so refusing kept the accepted fragment exactly what it
had been: a `false` arm for a constructor that did not previously exist cannot change the verdict on
any model that could be written before, and it cannot let a branch through un-checked. **Returning
`true` was the permissive alternative and would have admitted a branch whose sends nothing checks**,
which is exactly what recursing avoids: `targetsDeclared` walks a list of bodies, so without this arm
descending, a send nested in a branch would never be visited by any clause.

The pair form is not a stylistic choice. `DTR.GeneralStmt` is a nested inductive, and a single
function that recursed from a statement into its branch bodies with `List.all` would hide the
recursive call inside a lambda and fall to well-founded recursion, which does not reduce; F89 records
that failure and its cost. `wellFormed` is a `Bool` that the frontend evaluates and that
`Relico/Tests/*` can `decide`, so reducibility here is load bearing.
-/
def statementTargetDeclared
    (reactiveClass : DTR.GeneralReactiveClass) :
    DTR.GeneralStmt →
    Bool

  | .assign _ _ =>
      true

  | .trace _ =>
      true

  | .send target _ _ _ =>
      match target with

      | .selfTarget =>
          true

      | .knownRebec knownRebec =>
          (reactiveClass.knownRebec? knownRebec).isSome

  | .ifThenElse _ thenBody elseBody =>
      reactiveClass.bodyTargetsDeclared thenBody &&
        reactiveClass.bodyTargetsDeclared elseBody

/--
Every statement of one body, at any nesting depth, has a declared send target.

An explicit traversal rather than `body.all`, for the reducibility reason on the statement-level
definition above.
-/
def bodyTargetsDeclared
    (reactiveClass : DTR.GeneralReactiveClass) :
    DTR.GeneralBody →
    Bool

  | [] =>
      true

  | statement :: remaining =>
      reactiveClass.statementTargetDeclared statement &&
        reactiveClass.bodyTargetsDeclared remaining

end

/--
One class satisfies D6: every external send it contains names a known rebec it
declares.

`bodies.all` stays at the outer level because a class's bodies are a list of bodies rather than a
nested structure; the descent into a body, including into any branch it contains, is
`bodyTargetsDeclared`'s.
-/
def targetsDeclared
    (reactiveClass : DTR.GeneralReactiveClass) :
    Bool :=
  reactiveClass.bodies.all
    (fun body =>
      reactiveClass.bodyTargetsDeclared body)

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

/- `statementResolves` and `bodyResolves` are a mutual pair as of stage I0, for the reason recorded on
`GeneralReactiveClass.statementTargetDeclared`. A `mutual` block cannot carry a docstring, so each
definition carries its own. -/
mutual

/--
One statement's send, if it has one, names a message server the receiving class
declares, with a payload of the declared arity.

**`ifThenElse` recurses as of stage I0.** It was `false` from stage H until then, and
`GeneralReactiveClass.statementTargetDeclared` records why that was right and why the replacement is a
recursion rather than a `true`: `sendsResolveToMessageServers` walks a list of bodies, so an arm that
answered `true` would let a send nested in a branch reach a message server nothing had checked.
-/
def statementResolves
    (model : DTR.GeneralModel)
    (reactiveClass : DTR.GeneralReactiveClass) :
    DTR.GeneralStmt →
    Bool

  | .assign _ _ =>
      true

  | .trace _ =>
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

  | .ifThenElse _ thenBody elseBody =>
      model.bodyResolves reactiveClass thenBody &&
        model.bodyResolves reactiveClass elseBody

/--
Every send of one body, at any nesting depth, reaches a declared message server.

An explicit traversal rather than `body.all`, for the reducibility reason on the statement-level
definition above.
-/
def bodyResolves
    (model : DTR.GeneralModel)
    (reactiveClass : DTR.GeneralReactiveClass) :
    DTR.GeneralBody →
    Bool

  | [] =>
      true

  | statement :: remaining =>
      model.statementResolves reactiveClass statement &&
        model.bodyResolves reactiveClass remaining

end

/--
Every send in the model reaches a declared message server.

This is the one clause that cannot be checked class-locally, and it is possible
only because instance bindings are decoded: with the empty binding stores of the
earlier families there is no receiving class to look at.

The two outer `all`s stay: a model's classes are a list and a class's bodies are a list of bodies.
Only the descent *into* a body is a recursion, and it is `bodyResolves`'s.
-/
def sendsResolveToMessageServers
    (model : DTR.GeneralModel) :
    Bool :=
  model.classes.all
    (fun reactiveClass =>
      reactiveClass.bodies.all
        (fun body =>
          model.bodyResolves
            reactiveClass
            body))

/--
A body's resolution yields the resolution of each statement the body lists.

The bridge between the two shapes callers want, and it is only a *shape* change: `bodyResolves` is
exactly the fold of `statementResolves` over the list, so the two directions are equivalent and
nothing is strengthened or weakened by moving between them. It exists because
`sendsResolveToMessageServers` now ends in a recursion rather than in `List.all`, and every consumer
that used to finish with `List.all_eq_true.mp` needs one step in its place.

Stated one way only. The converse holds by the same induction and no caller wants it, which is the
same judgement `generalStmtOrigin_of_mem_of_bodyOrigin` records.
-/
theorem statementResolves_of_mem_of_bodyResolves
    (model : DTR.GeneralModel)
    (reactiveClass : DTR.GeneralReactiveClass) :
    ∀ (body : DTR.GeneralBody),
      model.bodyResolves
          reactiveClass
          body =
        true →
      ∀ statement ∈ body,
        model.statementResolves
            reactiveClass
            statement =
          true := by

  intro body

  induction body with

  | nil =>
      intro _ statement hStatement
      cases hStatement

  | cons head remaining inductionHypothesis =>
      intro hBody statement hStatement

      simp only [
        DTR.GeneralModel.bodyResolves,
        Bool.and_eq_true
      ] at hBody

      rcases List.mem_cons.mp hStatement with
        hHere |
          hThere

      · rw [hHere]
        exact hBody.left

      · exact
          inductionHypothesis
            hBody.right
            statement
            hThere


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

/--
A well-formed model declares distinct message-server names in every class.

The per-class projection of `namesUniqueAndValid`'s classes conjunct, and one of the three
premises **F81** measured (2026-08-26) as having a decided source but no public route: the
fact is a conjunct of this clause, and no theorem anywhere concluded it. The consumer arrived
with the routing/resolution theorems of `Relico/Correctness/GeneralCorrespondence.lean`, so
the projection is stated here, beside the clause's own extraction lemma.

The extraction is two cases-steps rather than one projection, for the reason the extraction
section above records: a projection chain reads a fixed `&&` nesting and can silently prove a
different clause under the other associativity, while a `cases` on the wanted conjunct is
correct under both. The outer step isolates the `classes.all` conjunct of
`namesUniqueAndValid`; `List.all_eq_true` then instantiates it at the class the caller names;
the inner step is a `by_cases` on the conclusion itself, whose negation makes the instantiated
conjunction `false` and contradicts the `= true` the outer step produced.
-/
theorem messageServerNames_nodup_of_wellFormed
    {model : DTR.GeneralModel}
    (hWellFormed :
      model.wellFormed =
        true)
    {reactiveClass : DTR.GeneralReactiveClass}
    (hClass :
      reactiveClass ∈ model.classes) :
    (reactiveClass.messageServers.map
      (fun server =>
        server.name)).Nodup := by
  have hUnique :
      model.namesUniqueAndValid =
        true :=
    namesUniqueAndValid_of_wellFormed
      model
      hWellFormed

  have hClasses :
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
                declaration.name.value != "")) =
        true := by
    revert hUnique
    unfold namesUniqueAndValid
    cases
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
                declaration.name.value != "")) <;>
      simp

  have hBody :
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
                declaration.name.value != "")) reactiveClass =
        true :=
    List.all_eq_true.mp
      hClasses
      reactiveClass
      hClass

  by_cases hServers :
    (reactiveClass.messageServers.map
      (fun server =>
        server.name)).Nodup

  · exact hServers

  · exfalso

    simp [hServers] at hBody

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
