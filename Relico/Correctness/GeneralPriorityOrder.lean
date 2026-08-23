import Relico.DTR.GeneralWellFormed
import Relico.Translation.GeneralBasic

set_option autoImplicit false

/-!
# Stage F level 1: emitted port-reaction order realizes actor priority

`docs/STAGE_F_DESIGN.md` §6 and §9.2. This module carries stage F's **level 1** obligation — §III-D's
requirement that within one message server's group, that server's port reactions are ordered by the
**sending actor's** priority. Level 2, which orders the per-server groups by message-server priority,
belongs with task #87 and is deliberately absent here so that a build failure in either level is
localizable to one file.

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

end Correctness
end Relico
