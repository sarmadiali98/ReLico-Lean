import Relico.DTR.GeneralWellFormed
import Relico.Translation.GeneralBasic

set_option autoImplicit false

/-!
# Stage F: emitted reaction order realizes priority, at both levels

`docs/STAGE_F_DESIGN.md` §6 and §9.2. This module carries **both** of stage F's obligations. Level 1 is
§III-D's requirement that within one message server's group, that server's port reactions are ordered by
the **sending actor's** priority. Level 2 is Lemma 2's same-actor case one level out: whole per-server
groups, ordered by **message-server** priority.

Level 1 landed alone, in commit 1, and this paragraph then said level 2 was deliberately absent "so that
a build failure in either level is localizable to one file". The localization was real and is now spent;
the word was wrong. §10 of the design splits the two levels by **commit** and says level 2's forms are
"added to the same file in commit 2", so the split buys a blind diff small enough to name one level, not
a permanent file boundary.

## Why this is not a transcription of `Relico/Correctness/PriorityOrder.lean`

`PriorityOrder.lean` is the obvious blueprint and it does not port, for two measured reasons.

First, **the general family has no scheduling module on either side.** `PriorityOrder.lean`'s headline is
an iff between `DTR.PriorityServerNamePrecedesOrEqual` and `LF.ReactionActionPrecedesOrEqual`, and both
exist only for the restricted `DTR.MessageServer` / `LF.Reaction` family — `Relico/DTR/` and
`Relico/LF/` contain no general-family analogue of either. Defining them is not a small addition:
`LF.GeneralTrigger` has three constructors rather than two, so a general target-side order predicate
would have to scan `inputPort` names, and §9.1 of the design records why the blueprint's key does not
exist here at all — a message-server name identifies exactly one reaction in the restricted family,
whereas in the general family one *instance* contributes a whole block of port reactions.

Second, and more importantly, **the blueprint's iff is a preservation result, not a priority result.**
`Relico/DTR/MultiStorePriorityScheduling.lean:64` defines `PriorityServerNamePrecedesOrEqual` as a name
scan over `MessageServerPriority.normalize`'s *own output*. So the theorem says emitted reaction order
equals normalized declaration order — genuinely the harder half, and true — while saying nothing about
whether normalized order is priority order. Measured: no `List.Sorted`, `List.Pairwise` or `Chain'`
occurs anywhere in `Relico/`, and when that was measured on 2026-08-23 the only thing pinning any sort's
behaviour was a single `rfl` regression at one four-element input,
`Relico/Tests/MessageServerPriority.lean:104`. `Relico/Tests/GeneralPriority.lean` lands in this same
commit and pins both general instantiations.

That gap is closed in `Relico/DTR/GeneralPriority.lean` by `normalize_sorted` and the two append-split
consumers it feeds, and this module spends them. The consequence for how the results below read: they
are stated as **append splits** rather than as name orders, matching §9.2, because that is the shape
`assembleGeneralPortReactions_instanceDeclarationOrder` already has and the shape routing's own
`routesOf_split` produces.

## The two statements, per §6

§6 settles that `PrioritiesDistinct` is a **hypothesis** rather than a sixth `wellFormed` clause — it is
`(map priority).Nodup` over `List (Option Nat)`, so it forbids two *absent* priorities and would reject
`expressions.rebeca` and `control-flow.rebeca`, neither of which has a fan-in at all. So each level gets
an unconditional statement and a guard-relative one, and both appear below.
-/

namespace Relico
namespace Correctness

/-!
## Bridging the named guard to the sort's premise

`Relico/DTR/GeneralPriority.lean` states its distinctness premise as a raw `Nodup` on the mapped
priority projection, deliberately, so that the module keeps `Relico.DTR.GeneralSyntax` as its only
import. `Relico/DTR/GeneralWellFormed.lean` names the same condition twice over —
`GeneralActorInstances.PrioritiesDistinct` (`:484`) and its model-wide wrapper
`GeneralModel.ActorPrioritiesDistinct` (`:538`). This is the one place the two spellings meet.
-/

/--
The named model-wide actor guard is the sort's `Nodup` premise.

`GeneralModel.ActorPrioritiesDistinct` unfolds to
`(model.instances.map (fun actor => actor.priority)).Nodup`, and
`DTR.GeneralActorPriority.priorityOf` is `fun actor => actor.priority`, so the two are the same
proposition. Isolated into a lemma rather than inlined at each use site so that if the definitional
step ever stops holding — a field rename, a projection change — exactly one declaration reports it.
-/
theorem actorPrioritiesDistinct_map_priorityOf
    (model : DTR.GeneralModel)
    (hDistinct :
      DTR.GeneralModel.ActorPrioritiesDistinct
        model) :
    (model.instances.map
      DTR.GeneralActorPriority.priorityOf).Nodup :=
  hDistinct

/-!
## The walked instance order realizes actor priority

`Translation.priorityOrderedInstances` (`Relico/Translation/GeneralRouting.lean`) is
`DTR.GeneralActorPriority.normalize model.instances`, and `routesOf` walks it — that redefinition is
task #82, and §7.2 records why `routesOf` was taught to route the ordered list rather than gaining a
sorted twin: a twin would have left six pipeline theorems green and simultaneously vacuous.
-/

/--
Unconditional level 1: however the walked instance list splits, every instance in the earlier part
precedes or ties every instance in the later part.

No guard, so this holds of every model the pipeline accepts. Ties are possible and are resolved by
source declaration order, which is `normalize`'s stability and is what decision `0041` requires.
-/
theorem walkedInstances_precedes_of_split
    (model : DTR.GeneralModel)
    {earlier later :
      List DTR.GeneralActorInstance}
    (hInstances :
      Translation.priorityOrderedInstances
          model =
        earlier ++ later) :
    ∀ earlierInstance,
      earlierInstance ∈ earlier →
      ∀ laterInstance,
        laterInstance ∈ later →
        DTR.GeneralPriority.PrecedesOrEqual
          DTR.GeneralActorPriority.priorityOf
          earlierInstance
          laterInstance := by

  unfold
    Translation.priorityOrderedInstances at hInstances

  exact
    DTR.GeneralActorPriority.normalize_append_precedes
      hInstances

/--
Guard-relative level 1: with actor priorities distinct, the precedence across the split is strict, in
the sense that the two priorities cannot coincide.

This is the statement §6's decision buys. The premise is the named model guard rather than a raw
`Nodup`, so a caller works with `GeneralWellFormed`'s vocabulary.
-/
theorem walkedInstances_strict_of_split
    (model : DTR.GeneralModel)
    {earlier later :
      List DTR.GeneralActorInstance}
    (hInstances :
      Translation.priorityOrderedInstances
          model =
        earlier ++ later)
    (hDistinct :
      DTR.GeneralModel.ActorPrioritiesDistinct
        model) :
    ∀ earlierInstance,
      earlierInstance ∈ earlier →
      ∀ laterInstance,
        laterInstance ∈ later →
        DTR.GeneralPriority.PrecedesOrEqual
            DTR.GeneralActorPriority.priorityOf
            earlierInstance
            laterInstance ∧
          DTR.GeneralActorPriority.priorityOf
              earlierInstance ≠
            DTR.GeneralActorPriority.priorityOf
              laterInstance := by

  unfold
    Translation.priorityOrderedInstances at hInstances

  exact
    DTR.GeneralActorPriority.normalize_append_strict
      hInstances
      (actorPrioritiesDistinct_map_priorityOf
        model
        hDistinct)

/-!
## The payoff: emitted reaction order, tied to the priority that chose it

The two theorems above are about the *instance* list. What §III-D asks about is the emitted **reaction**
list. `Translation.assembleGeneralPortReactions_instanceDeclarationOrder` already carries the emission
half — that routing splits at the instance split and the reaction assembly distributes over that split —
and it was re-keyed onto `priorityOrderedInstances` by task #82. Composing the two gives the statement
stage F actually owes, in one place, so that a reader does not have to notice that two theorems in
different files share a hypothesis.
-/

/--
Level 1, complete: at any split of the walked instance list where routing succeeds on both halves, the
emitted port reactions split in exactly the same place, **and** that split respects actor priority
strictly.

The three conjuncts are, in order: routing returns the concatenated routes; reaction assembly
distributes over the concatenation, so emitted declaration order is earlier-then-later; and every
earlier instance strictly precedes every later one by priority. Read together they say the emitted
declaration order — which §2.1 measured to be the order that decides at one tag — is the actor-priority
order.

Scoped to one receiving reactor, per `P1`: LF's order *between* reactors comes from the dependency
graph, not from declaration order, so Lemma 2's different-actor case is out of scope and only the
same-actor case is claimed. `className`, `server` and `compiledBody` are the receiving reactor's
identity, which is what keeps the statement inside it.
-/
theorem portReactions_realizeActorPriority
    (model : DTR.GeneralModel)
    (earlier later :
      List DTR.GeneralActorInstance)
    (earlierRoutes laterRoutes :
      List Translation.GeneralRoute)
    (className : ClassName)
    (server :
      DTR.GeneralMessageServer)
    (compiledBody : LF.GeneralBody)
    (hInstances :
      Translation.priorityOrderedInstances
          model =
        earlier ++ later)
    (hEarlier :
      Translation.routesOfInstances
          model
          earlier =
        .ok earlierRoutes)
    (hLater :
      Translation.routesOfInstances
          model
          later =
        .ok laterRoutes)
    (hDistinct :
      DTR.GeneralModel.ActorPrioritiesDistinct
        model) :
    Translation.routesOf model =
        .ok
          (earlierRoutes ++
            laterRoutes) ∧
      Translation.assembleGeneralPortReactions
            className
            server
            compiledBody
            (earlierRoutes ++ laterRoutes) =
          Translation.assembleGeneralPortReactions
              className
              server
              compiledBody
              earlierRoutes ++
            Translation.assembleGeneralPortReactions
              className
              server
              compiledBody
              laterRoutes ∧
      ∀ earlierInstance,
        earlierInstance ∈ earlier →
        ∀ laterInstance,
          laterInstance ∈ later →
          DTR.GeneralPriority.PrecedesOrEqual
              DTR.GeneralActorPriority.priorityOf
              earlierInstance
              laterInstance ∧
            DTR.GeneralActorPriority.priorityOf
                earlierInstance ≠
              DTR.GeneralActorPriority.priorityOf
                laterInstance := by

  obtain ⟨hRoutes, hDistributes⟩ :=
    Translation.assembleGeneralPortReactions_instanceDeclarationOrder
      model
      earlier
      later
      earlierRoutes
      laterRoutes
      className
      server
      compiledBody
      hInstances
      hEarlier
      hLater

  exact
    ⟨hRoutes,
      hDistributes,
      walkedInstances_strict_of_split
        model
        hInstances
        hDistinct⟩

/-!
## Level 2: bridging a guard that is per class, not model-wide

Level 2's guard differs from level 1's in **shape**, not only in element type.
`GeneralModel.ActorPrioritiesDistinct` (`Relico/DTR/GeneralWellFormed.lean:538`) is one `Nodup` over
`model.instances`, which is why the bridge above is `hDistinct` itself.
`GeneralModel.MessageServerPrioritiesDistinct` (`:514`) is instead
`∀ reactiveClass ∈ model.classes, GeneralMessageServers.PrioritiesDistinct reactiveClass.messageServers`,
because two classes may both annotate a server `1` — local priority orders the reactions of one actor, so
distinctness is a per-class condition and model-wide distinctness would reject models the fragment
accepts.

So the bridge below takes a class and a membership proof. That extra argument is the only structural
difference between the two levels' guard handling, and it propagates: every guard-relative level-2
statement carries `model`, `reactiveClass` and `hMem` where level 1 carries `model` alone.
-/

/--
The named per-class message-server guard is the sort's `Nodup` premise, at one class.

`GeneralMessageServers.PrioritiesDistinct` unfolds to
`(reactiveClass.messageServers.map (fun messageServer => messageServer.priority)).Nodup`, and
`DTR.GeneralMessageServerPriority.priorityOf` is `fun messageServer => messageServer.priority`, so
instantiating the quantifier at `reactiveClass` lands on the sort's premise definitionally.

Isolated into a lemma for the reason `actorPrioritiesDistinct_map_priorityOf` gives — if the definitional
step ever stops holding, exactly one declaration reports it — and here it also names the membership step,
so a caller cannot silently take the guard to be model-wide.
-/
theorem messageServerPrioritiesDistinct_map_priorityOf
    (model : DTR.GeneralModel)
    (reactiveClass :
      DTR.GeneralReactiveClass)
    (hMem :
      reactiveClass ∈ model.classes)
    (hDistinct :
      DTR.GeneralModel.MessageServerPrioritiesDistinct
        model) :
    (reactiveClass.messageServers.map
      DTR.GeneralMessageServerPriority.priorityOf).Nodup :=
  hDistinct
    reactiveClass
    hMem

/-!
## The walked message-server order realizes message-server priority

`Translation.generalPriorityOrderedMessageServers` (`Relico/Translation/GeneralBasic.lean:1728`) is
`DTR.GeneralMessageServerPriority.normalize reactiveClass.messageServers`, and `compileGeneralReactiveClass`
hands it to `compileGeneralMessageServerReactions` in place of `reactiveClass.messageServers` — that
re-keying is task #94.

§9.2 records why the walk itself was left unsorted rather than sorting internally: it recurses on the
server list, so a sort inside it would re-decide the tail's order once per element. The sort therefore
sits exactly one level up, and these theorems are about the list that level produces.
-/

/--
Unconditional level 2: however the walked message-server list splits, every server in the earlier part
precedes or ties every server in the later part.

No guard, so this holds of every class the pipeline accepts — including a class with two unannotated
servers, which is a genuine tie resolved by source declaration order. Ties are commoner at this element
type than at level 1's, which is §6's reason for keeping distinctness a hypothesis instead of a
`wellFormed` clause.
-/
theorem walkedMessageServers_precedes_of_split
    (reactiveClass :
      DTR.GeneralReactiveClass)
    {earlier later :
      List DTR.GeneralMessageServer}
    (hServers :
      Translation.generalPriorityOrderedMessageServers
          reactiveClass =
        earlier ++ later) :
    ∀ earlierServer,
      earlierServer ∈ earlier →
      ∀ laterServer,
        laterServer ∈ later →
        DTR.GeneralPriority.PrecedesOrEqual
          DTR.GeneralMessageServerPriority.priorityOf
          earlierServer
          laterServer := by

  unfold
    Translation.generalPriorityOrderedMessageServers at hServers

  exact
    DTR.GeneralMessageServerPriority.normalize_append_precedes
      hServers

/--
Guard-relative level 2: with this class's message-server priorities distinct, the precedence across the
split is strict, in the sense that the two priorities cannot coincide.

The premise is the named model predicate plus a membership proof rather than a raw `Nodup`, so a caller
works in `GeneralWellFormed`'s vocabulary — level 1's convention, paid for at the extra argument the
per-class guard costs.
-/
theorem walkedMessageServers_strict_of_split
    (model : DTR.GeneralModel)
    (reactiveClass :
      DTR.GeneralReactiveClass)
    {earlier later :
      List DTR.GeneralMessageServer}
    (hMem :
      reactiveClass ∈ model.classes)
    (hServers :
      Translation.generalPriorityOrderedMessageServers
          reactiveClass =
        earlier ++ later)
    (hDistinct :
      DTR.GeneralModel.MessageServerPrioritiesDistinct
        model) :
    ∀ earlierServer,
      earlierServer ∈ earlier →
      ∀ laterServer,
        laterServer ∈ later →
        DTR.GeneralPriority.PrecedesOrEqual
            DTR.GeneralMessageServerPriority.priorityOf
            earlierServer
            laterServer ∧
          DTR.GeneralMessageServerPriority.priorityOf
              earlierServer ≠
            DTR.GeneralMessageServerPriority.priorityOf
              laterServer := by

  unfold
    Translation.generalPriorityOrderedMessageServers at hServers

  exact
    DTR.GeneralMessageServerPriority.normalize_append_strict
      hServers
      (messageServerPrioritiesDistinct_map_priorityOf
        model
        reactiveClass
        hMem
        hDistinct)

/-!
## The payoff: the compiled reaction list, in the order priority chose

`compileGeneralMessageServerReactions_append` (`Relico/Translation/GeneralBasic.lean:3435`) carries the
emission half — a class's reaction list splits where its server list splits, at an **arbitrary** cut
rather than only at the head. It was proved in level 2's first landing specifically to be this theorem's
consumer, and its docstring says so.

Composing it with the guard-relative form gives the statement level 2 owes. The composition rewrites by
the split hypothesis first, so the conclusion is keyed to the sorted list itself rather than to an
abstract `earlier ++ later` — which is the whole difference between an ordering claim and a distribution
claim, and the same move `portReactions_realizeActorPriority` makes at level 1 by taking `routesOf model`
as its first conjunct.
-/

/--
Level 2, complete: at any cut of one class's priority-ordered message-server list where compilation
succeeds on both halves, the class's compiled reaction list is the earlier half's reactions followed by
the later half's, **and** that cut respects message-server priority strictly.

The first conjunct is stated about `generalPriorityOrderedMessageServers reactiveClass`, not about
`earlier ++ later`. That is what makes it an ordering result: the list being walked is the sorted one, so
"earlier then later" reads as "higher priority then lower", and §2.1's measurement that reaction
declaration order is what decides at one tag is what makes emitted order the thing worth ordering.

Scoped to one class, which is also the scope of the guard. Order *between* reactors comes from LF's
dependency graph rather than from declaration order, per `P1`, so Lemma 2's different-actor case is out of
scope here exactly as it is at level 1. `env`, `selfSends`, `routes` and `className` are the compilation
context and are held fixed across the cut, which is what keeps both halves inside one reactor.
-/
theorem messageServerReactions_realizeMessageServerPriority
    (model : DTR.GeneralModel)
    (reactiveClass :
      DTR.GeneralReactiveClass)
    (env : Translation.GeneralOutputPortEnv)
    (selfSends :
      List Translation.GeneralSelfSend)
    (routes :
      List Translation.GeneralRoute)
    (className : ClassName)
    (earlier later :
      List DTR.GeneralMessageServer)
    (compiledEarlier compiledLater :
      List LF.GeneralReaction)
    (hMem :
      reactiveClass ∈ model.classes)
    (hServers :
      Translation.generalPriorityOrderedMessageServers
          reactiveClass =
        earlier ++ later)
    (hEarlier :
      Translation.compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          earlier =
        .ok compiledEarlier)
    (hLater :
      Translation.compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          later =
        .ok compiledLater)
    (hDistinct :
      DTR.GeneralModel.MessageServerPrioritiesDistinct
        model) :
    Translation.compileGeneralMessageServerReactions
          env
          selfSends
          routes
          className
          (Translation.generalPriorityOrderedMessageServers
            reactiveClass) =
        .ok
          (compiledEarlier ++
            compiledLater) ∧
      ∀ earlierServer,
        earlierServer ∈ earlier →
        ∀ laterServer,
          laterServer ∈ later →
          DTR.GeneralPriority.PrecedesOrEqual
              DTR.GeneralMessageServerPriority.priorityOf
              earlierServer
              laterServer ∧
            DTR.GeneralMessageServerPriority.priorityOf
                earlierServer ≠
              DTR.GeneralMessageServerPriority.priorityOf
                laterServer := by

  refine
    ⟨?_,
      walkedMessageServers_strict_of_split
        model
        reactiveClass
        hMem
        hServers
        hDistinct⟩

  rw [hServers]

  exact
    Translation.compileGeneralMessageServerReactions_append
      hEarlier
      hLater

end Correctness
end Relico
