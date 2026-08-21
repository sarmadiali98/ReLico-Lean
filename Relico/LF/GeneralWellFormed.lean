import Relico.LF.GeneralSyntax

set_option autoImplicit false

namespace Relico
namespace LF

/-!
# Well-formedness for the general generated-LF family

One decidable `Bool` predicate per layer, so the whole thing is executable and
every conjunct is separately checkable. The program-level conjuncts are named
`def`s rather than inlined, for the reason the DTR side records: an extraction
lemma proved by case analysis on a *named* clause does not depend on how `&&`
associates, while a projection chain into an anonymous conjunction reads a fixed
nesting shape and, under the other associativity, proves a different clause while
still compiling.

Five things are deliberately not checked.

A declared port need not be connected. Measured: a model with an unconnected input
port compiles and runs, the reaction simply never fires. This is load-bearing
rather than tolerated — one reactor is shared by every instance of its class, so
its input-port set is the union over those instances, and requiring connectedness
would make the paper's own class-to-reactor mapping unrepresentable.

A connection may have the same source and target instance. A DTR known rebec may
be bound to the sending actor itself, and §III-E maps `r.m()` by what the statement
*is* rather than by who `r` turns out to name. The construct is safe because a
stage C connection always carries a delay, and that `after` breaking a cycle is
measured, not assumed.

Priority is not mentioned. Distinctness of priorities is a hypothesis of the
theorems that need deterministic selection, not a condition on being well-formed
at all.

Reaction names need not be unique. LF reactions are anonymous in concrete syntax,
so uniqueness would constrain an identifier the target language never sees.

Nothing here sorts anything. Declaration order is observable in the target, so a
sort inserted in this pipeline would be a silent semantic change.

A reaction may set the same output port twice. This is the fifth omission and the
newest, and it is not an oversight: setting one port twice in one reaction body loses
the first value, since a port holds one value per tag, so it is exactly the hazard
stage E was rewritten to remove. It is absent here because it is proved of the
*translation's output* rather than imposed on *arbitrary programs*
(`docs/STAGE_E_DESIGN.md` §10.2). Two reasons in that order. A hand-built LF program
setting one port twice is a faithful model of an LF program a person could write, and
this predicate's job is to say what `lfc` and its toolchain will accept, which such a
program is; and making it a conjunct here would let the translation discharge the
invariant by *checking* it, when what the design earned is an invariant that holds
because two sends in one body have two send sites and therefore two ports. A checked
version of that theorem would be strictly weaker while looking stronger.
-/

namespace GeneralTrigger

/--
Whether a trigger is the startup trigger.

Written out over all three constructors rather than with a wildcard, so that the
stage which adds a fourth trigger gets a build error here instead of a silent
`false`.
-/
def isStartup :
    LF.GeneralTrigger →
    Bool

  | .startup =>
      true

  | .logicalAction _ =>
      false

  | .inputPort _ =>
      false

end GeneralTrigger

namespace GeneralReactor

/--
Every name a reactor declares, as strings, in one list.

Parameters, ports, state variables and logical actions are five fields but **one** LF
name scope: `input v` and `state v` in the same reactor are two declarations of one
name. Uniqueness is therefore one check over this union rather than five per-list
checks, which would accept a program no LF compiler will.

Parameters joined this union in stage D, on the measured ground that a reactor
parameter is readable in a reaction body with no trigger and no local declaration —
it is a member exactly as a state variable is, so `reactor R(x: int) { state x: int
= 0 }` declares one name twice. Stage D wrote here that whether `lfc` rejects that
spelling was unverified, and that including parameters was the conservative side of
that uncertainty. **The uncertainty is gone.** Probe `param_state_name_collision`
in `tools/paper-measurements/lf_semantics_probe.sh`, run on 2026-08-20, put that
exact reactor through `lfc 0.11.0`: the validator **accepts** it, and the generated
C++ then fails to compile with `reference member 'x' binds to a temporary object`,
a diagnostic attributed to line 1 column 1 of the `.lf` file. So a reactor parameter
is emitted as a C++ reference member, the collision is fatal one layer *later* than
the validator, and this predicate is stricter than `lfc`'s validator and exactly as
strict as the toolchain behind it.

That is the sense in which `docs/STAGE_E_DESIGN.md` §9 calls this line conservative:
not hedging against an unknown, but declining to delegate a rejection to a diagnostic
that names neither the reactor nor the offending name and that no user could act on.
F32 rests on it — the guard stage E installs on the translation's own output refuses
such a program at this predicate rather than emitting LF that passes validation and
then will not build.
-/
def declaredNames
    (reactor : LF.GeneralReactor) :
    List String :=
  (reactor.parameters.map
    (fun parameter =>
      parameter.name.value)) ++
    (reactor.inputPorts.map
      (fun port =>
        port.name.value)) ++
    (reactor.outputPorts.map
      (fun port =>
        port.name.value)) ++
    (reactor.stateVariables.map
      (fun declaration =>
        declaration.name.value)) ++
    (reactor.logicalActions.map
      (fun action =>
        action.name.value))

/--
A trigger names something this reactor declares.
-/
def triggerWellFormed
    (reactor : LF.GeneralReactor) :
    LF.GeneralTrigger →
    Bool

  | .startup =>
      true

  | .logicalAction action =>
      reactor.logicalActions.any
        (fun declared =>
          declared.name == action)

  | .inputPort port =>
      reactor.inputPorts.any
        (fun declared =>
          declared.name == port)

/--
An expression resolves against this reactor's state and the enclosing reaction's
parameters.

This is **name resolution only**, and stage D deliberately left it that way even
though types now exist on both sides. Two reasons, in order of weight. First, the DTR
side does not type expressions either — `DTR/GeneralWellFormed.lean` places no
restriction on expressions at all — so a type check here would refuse programs this
repository's own frontend accepts, which is the same trap that killed the
domain-restriction option in `docs/STAGE_D_DESIGN.md` §3. Second, typing an expression
needs the types of the parameters in scope, and a reaction's parameters are bare
names by design, their types being fixed by the action that triggers the reaction.
The residual gap is the narrowed finding F28.

`.parameterVar` resolves against the enclosing reaction's parameter list and **not**
against the reactor's parameters, which is stricter than the target requires and
intentionally so. A reactor parameter is readable anywhere in generated C++, but a
Rebeca constructor's formals are not in scope in a message server, so admitting them
here would accept a translation of a source program that never existed. The startup
reaction reaches them because `compileGeneralConstructor` puts those very names into its
own parameter list, which is not left as a reading of that function:
`Translation.compileGeneralReactiveClass_startupParameters` states it.
-/
def exprWellFormed
    (reactor : LF.GeneralReactor)
    (parameters : List VarName) :
    LF.GeneralExpr →
    Bool

  | .intLiteral _ =>
      true

  | .boolLiteral _ =>
      true

  | .stateVar name =>
      reactor.stateVariables.any
        (fun declaration =>
          declaration.name == name)

  | .parameterVar name =>
      parameters.contains name

  | .binary _ left right =>
      exprWellFormed
          reactor
          parameters
          left &&
        exprWellFormed
          reactor
          parameters
          right

  | .unary _ operand =>
      exprWellFormed
        reactor
        parameters
        operand

/--
A statement resolves, and a scheduled action or a set port is given the arity it
declares.

`setPort` requires an **output** port. A statement naming a real port in the wrong
direction is one of the two mistakes this layer exists to catch.

Stage E gave `setPort` a list of expressions (`GeneralSyntax.lean`, the `setPort`
constructor), so the arity conjunct `.schedule` has carried since stage D now appears
on both arms. The port arm reads the number its payload carries from
`LF.GeneralPortPayload.arity` rather than open-coding the scalar case, which is why
that helper lives beside the payload type instead of here. The two arms then differ in
nothing but where the declared arity is stored, and that symmetry is the point: a port
and a typed logical action are the same payload question asked in two places, and
stage D answered it in only one of them.
-/
def stmtWellFormed
    (reactor : LF.GeneralReactor)
    (parameters : List VarName) :
    LF.GeneralStmt →
    Bool

  | .assign name value =>
      reactor.stateVariables.any
          (fun declaration =>
            declaration.name == name) &&
        reactor.exprWellFormed
          parameters
          value

  | .schedule action arguments _ =>
      reactor.logicalActions.any
          (fun declared =>
            (declared.name == action) &&
              (declared.parameters.length == arguments.length)) &&
        arguments.all
          (fun argument =>
            reactor.exprWellFormed
              parameters
              argument)

  | .setPort port arguments =>
      reactor.outputPorts.any
          (fun declared =>
            (declared.name == port) &&
              (declared.payload.arity == arguments.length)) &&
        arguments.all
          (fun argument =>
            reactor.exprWellFormed
              parameters
              argument)

/--
A reaction's trigger and body both resolve against its reactor, with its own
parameters in scope.
-/
def reactionWellFormed
    (reactor : LF.GeneralReactor)
    (reaction : LF.GeneralReaction) :
    Bool :=
  reactor.triggerWellFormed
      reaction.trigger &&
    reaction.body.all
      (fun statement =>
        reactor.stmtWellFormed
          reaction.parameters
          statement)

/--
A well-formed reactor.

The startup reaction's trigger *is* `startup` and no message reaction's trigger is:
the two lists are distinguished by role, and a trigger in the wrong list would make
the printer emit a reaction the source never asked for.
-/
def wellFormed
    (reactor : LF.GeneralReactor) :
    Bool :=
  (reactor.name.value != "") &&
    reactor.declaredNames.all
      (fun name =>
        name != "") &&
    decide
      (reactor.declaredNames.Nodup) &&
    reactor.startupReaction.trigger.isStartup &&
    reactor.messageReactions.all
      (fun reaction =>
        !reaction.trigger.isStartup) &&
    reactor.reactionWellFormed
      reactor.startupReaction &&
    reactor.messageReactions.all
      (fun reaction =>
        reactor.reactionWellFormed
          reaction)

end GeneralReactor

namespace GeneralProgram

/--
A connection resolves at both ends, in the right direction, and the two ends agree on
what they carry.

Each endpoint goes through the instance list and then through the reactor list,
because a connection names instances while ports are declared on reactors. The
source port must be one of the source reactor's **outputs** and the target port one
of the target reactor's **inputs**.

Stage E adds the third condition, which `lfc` has always enforced and which this
predicate previously had no way to express: connected ports must carry the same type.
Ports now store a `LF.GeneralPortPayload`, so agreement is decidable equality — and
both endpoints are found with `List.find?` rather than tested with `List.any`, because
what the check needs is now the declaration itself and not merely its existence.

Agreement is *checked* here rather than guaranteed by construction, and that is a real
weakening worth naming rather than hiding, recorded as F37. Stage D derived a payload
struct's name at the single site that used it, so two sites could not disagree; stage
E stores that name at both ends of a connection. The translation builds both ends from
one row of the routing table, so they cannot drift in practice — this conjunct is what
makes that a checked fact instead of a trusted one, and it is the conjunct the
acceptance-implies-well-formedness theorem of `docs/STAGE_E_DESIGN.md` §8 discharges
by construction.
-/
def connectionWellFormed
    (program : LF.GeneralProgram)
    (connection : LF.GeneralConnection) :
    Bool :=
  match program.reactorOfInstance? connection.sourceInstance with

  | none =>
      false

  | some sourceReactor =>
      match program.reactorOfInstance? connection.targetInstance with

      | none =>
          false

      | some targetReactor =>
          match
              sourceReactor.outputPorts.find?
                (fun declared =>
                  declared.name == connection.sourcePort)
          with
          | none =>
              false

          | some sourcePort =>
              match
                  targetReactor.inputPorts.find?
                    (fun declared =>
                      declared.name == connection.targetPort)
              with
              | none =>
                  false

              | some targetPort =>
                  sourcePort.payload == targetPort.payload

/--
At least one reactor is declared.

Fig. 5 rather than taste: `LFProgram ::= target Cpp; Reactor+ MainReactor` puts a
`+` on reactors.
-/
def reactorsNonEmpty
    (program : LF.GeneralProgram) :
    Bool :=
  !program.reactors.isEmpty

/--
At least one instance is declared.

`MainReactor ::= main reactor { InstDecl+ Connection* }` puts a `+` on instances and
a `*` only on connections.
-/
def instancesNonEmpty
    (program : LF.GeneralProgram) :
    Bool :=
  !program.instances.isEmpty

/--
Every declared reactor is well-formed.
-/
def reactorsWellFormed
    (program : LF.GeneralProgram) :
    Bool :=
  program.reactors.all
    (fun reactor =>
      reactor.wellFormed)

/--
Reactor names are unique, so `reactor?` is unambiguous.
-/
def reactorNamesUnique
    (program : LF.GeneralProgram) :
    Bool :=
  decide
    ((program.reactors.map
      (fun reactor =>
        reactor.name)).Nodup)

/--
Instance names are unique, so `instance?` is unambiguous.
-/
def instanceNamesUnique
    (program : LF.GeneralProgram) :
    Bool :=
  decide
    ((program.instances.map
      (fun reactorInstance =>
        reactorInstance.name)).Nodup)

/--
Every instance has a non-empty name and instantiates a declared reactor.
-/
def instancesResolve
    (program : LF.GeneralProgram) :
    Bool :=
  program.instances.all
    (fun reactorInstance =>
      (reactorInstance.name.value != "") &&
        (program.reactor?
          reactorInstance.reactorName).isSome)

end GeneralProgram

/--
One instance's arguments match one reactor's parameters, in count and in type.

Count and type agreement are **one** recursion rather than a length comparison
followed by a pairwise walk, mirroring `DTR.argumentsMatchParameters` exactly. The
reason is the one that side records: a length disagreement can then never be reported
as a type disagreement.

This check is possible at all only because instance arguments are *values*. Payload
arguments on a `schedule` are expressions, and they are checked for arity alone —
`stmtWellFormed` does that — since typing an expression would need the types of the
parameters in scope, which reactions deliberately do not carry.
-/
def argumentsMatchParameters :
    List LF.GeneralValue →
    List LF.GeneralTypedParameter →
    Bool

  | [], [] =>
      true

  | value :: remainingValues, parameter :: remainingParameters =>
      LF.GeneralValue.hasType
          value
          parameter.declaredType &&
        argumentsMatchParameters
          remainingValues
          remainingParameters

  | _, _ =>
      false

namespace GeneralProgram

/--
Every instance's arguments match the parameters of the reactor it instantiates.

The LF mirror of `DTR.GeneralModel.argumentsMatchConstructor`, and stage D's reason
for existing at this layer: before stage D a reactor had no parameters and an instance
had no arguments, so there was nothing to agree about.

An instance whose reactor does not resolve is **false** here rather than vacuously
true. `instancesResolve` already requires resolution, so a program failing that
conjunct fails this one too, and the redundancy is deliberate: a predicate that
returned `true` for an unresolvable instance would be one whose meaning depended on
another conjunct being checked first, and conjuncts get reordered.

Asserted in the bridge test main with a positive **and** a negative case. Stage B
found `PrioritiesDistinct` defined and never enforced anywhere, which is
indistinguishable from not having written it, and an unexercised predicate is the
same defect one step earlier.
-/
def instanceArgumentsMatch
    (program : LF.GeneralProgram) :
    Bool :=
  program.instances.all
    (fun reactorInstance =>
      match program.reactor? reactorInstance.reactorName with

      | none =>
          false

      | some reactor =>
          LF.argumentsMatchParameters
            reactorInstance.arguments
            reactor.parameters)

/--
Every connection resolves, and carries the same payload at both of its ends.
-/
def connectionsWellFormed
    (program : LF.GeneralProgram) :
    Bool :=
  program.connections.all
    (fun connection =>
      program.connectionWellFormed
        connection)

/--
Target endpoints are pairwise distinct.

This is the enforceable form of §III-B's *"each input port has a single source
(outputs may broadcast)"*. Note the asymmetry: there is deliberately **no**
condition on source endpoints, because broadcasting one output to several inputs is
legal and nothing in §III-D needs it forbidden.
-/
def targetEndpointsUnique
    (program : LF.GeneralProgram) :
    Bool :=
  decide
    ((program.connections.map
      (fun connection =>
        (
          connection.targetInstance,
          connection.targetPort
        ))).Nodup)

/--
A well-formed general LF program.
-/
def wellFormed
    (program : LF.GeneralProgram) :
    Bool :=
  program.reactorsNonEmpty &&
    program.instancesNonEmpty &&
    program.reactorsWellFormed &&
    program.reactorNamesUnique &&
    program.instanceNamesUnique &&
    program.instancesResolve &&
    program.instanceArgumentsMatch &&
    program.connectionsWellFormed &&
    program.targetEndpointsUnique

end GeneralProgram

/--
On a list whose image has no duplicates, the mapped function is injective between
members of that list.

Hand-rolled because this development depends on Lean core alone. The statement
needed here is injectivity *on the list*, which is weaker than
`Function.Injective` and so is not the existing `nodup_map_of_injective`: two
distinct connections may well agree under some other projection.
-/
private theorem eq_of_nodup_map
    {α β : Type}
    (function : α → β) :
    ∀ (values : List α),
      (values.map function).Nodup →
      ∀ (a b : α),
        a ∈ values →
        b ∈ values →
        function a = function b →
          a = b := by

  intro values
  induction values with

  | nil =>
      intro _ a b hMemberA _ _
      cases hMemberA

  | cons head remaining inductionHypothesis =>
      intro hNodup a b hMemberA hMemberB hEqual

      rw [List.map_cons] at hNodup

      cases hNodup with

      | cons hHead hTail =>

          cases List.mem_cons.mp hMemberA with

          | inl hA =>
              subst hA

              cases List.mem_cons.mp hMemberB with

              | inl hB =>
                  exact hB.symm

              | inr hB =>
                  exact
                    absurd
                      hEqual
                      (hHead
                        (function b)
                        (List.mem_map.mpr
                          ⟨b, hB, rfl⟩))

          | inr hA =>

              cases List.mem_cons.mp hMemberB with

              | inl hB =>
                  subst hB

                  exact
                    absurd
                      hEqual.symm
                      (hHead
                        (function a)
                        (List.mem_map.mpr
                          ⟨a, hA, rfl⟩))

              | inr hB =>
                  exact
                    inductionHypothesis
                      hTail
                      a
                      b
                      hA
                      hB
                      hEqual


namespace GeneralProgram

/-!
### Extraction

Two clauses are extracted, one per theorem below. Each proof is a `Bool` case
analysis on its own named clause rather than a projection out of a conjunction, so
that it does not depend on how `&&` associates — a projection chain reads a fixed
nesting shape, and under the other associativity the same chain proves a different
clause while still compiling, which is the kind of error a build cannot report.
-/

private theorem instancesResolve_of_wellFormed
    (program : LF.GeneralProgram)
    (hWellFormed :
      program.wellFormed =
        true) :
    program.instancesResolve =
      true := by
  revert hWellFormed
  unfold wellFormed
  cases program.instancesResolve <;> simp

private theorem targetEndpointsUnique_of_wellFormed
    (program : LF.GeneralProgram)
    (hWellFormed :
      program.wellFormed =
        true) :
    program.targetEndpointsUnique =
      true := by
  revert hWellFormed
  unfold wellFormed
  cases program.targetEndpointsUnique <;> simp

/--
Every instance of a well-formed program has a reactor.

Executable well-formedness already computes this, but the translation stages need it
as a fact about an arbitrary member of the instance list rather than about one
program they can run.
-/
theorem reactorOfInstance_isSome
    (program : LF.GeneralProgram)
    (reactorInstance : LF.GeneralReactorInstance)
    (hWellFormed :
      program.wellFormed =
        true)
    (hMember :
      reactorInstance ∈ program.instances) :
    (program.reactor?
      reactorInstance.reactorName).isSome =
      true := by

  have hResolve :
      program.instancesResolve =
        true :=
    instancesResolve_of_wellFormed
      program
      hWellFormed

  unfold instancesResolve at hResolve

  simp only [
    List.all_eq_true,
    Bool.and_eq_true
  ] at hResolve

  exact
    (hResolve
      reactorInstance
      hMember).right

/--
An input port determines its connection.

This is the formal content of *"each input port has a single source"*, and in a
stronger form than the phrase suggests: an input port does not merely have at most
one incoming connection, it *determines* that connection, so the source instance,
the source port and the delay of an arrival are all functions of where it arrived.
The external-send stages need exactly that to give a receiving reaction a
well-defined sender.
-/
theorem connection_determined_by_target
    (program : LF.GeneralProgram)
    (first second : LF.GeneralConnection)
    (hWellFormed :
      program.wellFormed =
        true)
    (hFirst :
      first ∈ program.connections)
    (hSecond :
      second ∈ program.connections)
    (hInstance :
      first.targetInstance =
        second.targetInstance)
    (hPort :
      first.targetPort =
        second.targetPort) :
    first = second := by

  have hUnique :
      program.targetEndpointsUnique =
        true :=
    targetEndpointsUnique_of_wellFormed
      program
      hWellFormed

  unfold targetEndpointsUnique at hUnique

  exact
    eq_of_nodup_map
      (fun connection =>
        (
          connection.targetInstance,
          connection.targetPort
        ))
      program.connections
      (of_decide_eq_true hUnique)
      first
      second
      hFirst
      hSecond
      (by
        simp only [
          hInstance,
          hPort
        ])

end GeneralProgram

end LF
end Relico
