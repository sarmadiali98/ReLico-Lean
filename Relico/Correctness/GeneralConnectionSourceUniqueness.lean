/-
! # Source-endpoint uniqueness of emitted connections, and site-faithful `connectionFrom?`

The prerequisite the routed half of `Correctness.generalRoutedSend_forward` needs.
`LF.GeneralStep.setPort` follows `LF.connectionFrom? program.connections instanceName portName`,
which returns the **first** connection at that source endpoint, so a forward transfer of an external
send must know the connection found is the one emitted for that send site — otherwise its
`targetInstance`, `targetPort` and `delay` are some other site's.

## This does not contradict F48, and the difference is where the uniqueness comes from

F48 refutes injectivity of `Translation.outputPortNameFor` and nothing here claims it. Two channels
are measured: the separator is unescaped (`report`/`toHub` and `reportTo`/`hub` both give
`reportToToHub`), and `capitalizeName` folds case (`hub` and `Hub` give one name). Either channel
lets two send sites of one class name one output port.

What rules those out for an **accepted** program is the guard, and it does so at exactly the right
granularity. `LF.GeneralReactor.declaredNames` is
`parameters ++ inputPorts ++ outputPorts ++ stateVariables ++ logicalActions`, and
`decide reactor.declaredNames.Nodup` is a conjunct of `LF.GeneralReactor.wellFormed`. So the
generated output-port names are *in* the decided list: a class whose two send sites collide compiles
to a reactor with two equal entries in `outputPorts`, `declaredNames.Nodup` fails, and
`compileGeneralModel`'s guard refuses the program. The uniqueness below is therefore **inherited from
a decided guard clause**, never claimed by construction — the same shape F49 and F80 insist on, and
the same shape `generalRouteEndpoints_nodup` already has for target endpoints.

The asymmetry with target endpoints is worth stating because it looks backwards.
`LF.GeneralProgram.targetEndpointsUnique` is a *program-level* guard clause, so target-endpoint
uniqueness is decided directly. There is deliberately no source-endpoint clause — broadcast is legal
LF, and `LF.GeneralWellFormed`'s own docstring says so. Source-endpoint uniqueness is therefore not
decided; it is *derived*, per reactor, from `declaredNames`. That is why this module exists rather
than a one-line projection.

## What is proved, and what is deliberately not

Proved: for one instance's routes, and then for a whole accepted table, the source endpoints
`(senderInstance, outputPort)` are pairwise distinct; that this transfers to the emitted connections
definitionally; and that under it `LF.connectionFrom?` at a member connection's own endpoint returns
that connection.

Not proved and not needed: global route uniqueness, uniqueness of a connection by target, injectivity
of `outputPortNameFor`, or reconstruction of a send site from an *arbitrary* runtime connection —
that last is what F48 forbids and what the kind-origin layer routes around existentially.

The step from a **specific compiled send site** to its route is not here; see the closing section for
its exact remaining shape.
-/
import Relico.Translation.GeneralBasic
import Relico.LF.GeneralWellFormed
import Relico.LF.GeneralSemantics

set_option autoImplicit false

namespace Relico

namespace Translation

/-!
## The guard projection, output-port half

`Relico/Translation/GeneralBasic.lean` has `private` projections of `declaredNames.Nodup` for the
input-port and logical-action components; neither is de-privatised and no output-port twin exists,
so this is that twin, proved the same way — by contradiction on the clause, so the proof does not
depend on where in `wellFormed` the conjunct sits or how the `&&` chain associates.
-/

/--
A well-formed reactor declares distinct output port names.

The third component of `declaredNames`, extracted. This is the only place the guard is consulted, and
everything else in the module is combinatorics over it.
-/
theorem outputPortNames_nodup_of_reactorWellFormed
    {reactor : LF.GeneralReactor}
    (hWellFormed :
      reactor.wellFormed = true) :
    (reactor.outputPorts.map
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

  -- `declaredNames` is a left-associated append, so the output-port component is reached by
  -- peeling the two trailing lists and then taking the right half of what is left.
  obtain ⟨hThroughStateVars, _, _⟩ :=
    List.nodup_append.mp hNodup

  obtain ⟨hThroughOutputs, _, _⟩ :=
    List.nodup_append.mp hThroughStateVars

  obtain ⟨_, hOutput, _⟩ :=
    List.nodup_append.mp hThroughOutputs

  exact hOutput

/--
A compiled class's output-port environment has distinct port names.

The guard projection carried back to the environment the routes are built from.
`compileGeneralReactiveClass_outputPorts` identifies the compiled reactor's ports with
`generalOutputPortsOf env`, whose names are the entries' `outputPort` fields, so the decided `Nodup`
lands on exactly the projection the route combinatorics needs.
-/
theorem outputPortEnv_outputPortNames_nodup
    {classes : List DTR.GeneralReactiveClass}
    {routes : List GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    {env : GeneralOutputPortEnv}
    (hCompiled :
      compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (hWellFormed :
      reactor.wellFormed =
        true)
    (hEnv :
      outputPortEnvOf
          classes
          reactiveClass =
        .ok env) :
    (List.map
      (fun entry =>
        entry.outputPort.value)
      env).Nodup := by

  obtain ⟨reactorEnv, hReactorEnv, hPorts⟩ :=
    compileGeneralReactiveClass_outputPorts
      hCompiled

  -- The two environment equations resolve the same call, so the compiled reactor's ports are the
  -- caller's environment's ports. Substituted in this direction so that `env` survives into the
  -- conclusion rather than being replaced by the existential witness.
  have hSame :
      reactorEnv = env := by
    rw [
      hEnv
    ] at hReactorEnv

    exact
      Except.ok.inj
        hReactorEnv.symm

  subst hSame

  have hNames :
      reactor.outputPorts.map
          (fun port =>
            port.name.value) =
        List.map
          (fun entry =>
            entry.outputPort.value)
          reactorEnv := by
    rw [hPorts]

    unfold generalOutputPortsOf

    rw [List.map_map]

    rfl

  rw [
    ← hNames
  ]

  exact
    outputPortNames_nodup_of_reactorWellFormed
      hWellFormed

/-!
## Route source endpoints, one instance at a time

`routesOfEntries` walks one actor's environment and emits one route per entry, copying
`actor.name` into every route's `senderInstance` and `entry.outputPort` into its `outputPort`. So
within one instance the source endpoints are distinct exactly when the environment's port names are
— which the guard projection above supplies.

Stated on the *value* projection (`PortName.value`) rather than on `PortName`, because that is the
spelling `declaredNames` decides. A `PortName` collision reflects into a `String` collision because
`PortName.value` is a function, which is the direction `nodup_map_of_reflecting` runs.
-/

/--
A resolved actor carries the name it was resolved by.

A local copy of the `private` `findActor?_name` in `Relico/DTR/GeneralActorSelection.lean`; not
de-privatised, per the house preference for duplicating a short lemma over widening an interface.
-/
private theorem findActor?_name_local
    (instances : List DTR.GeneralActorInstance)
    (actorName : ActorName) :
    ∀ actor,
      DTR.findActor?
          instances
          actorName =
        some actor →
      actor.name = actorName := by

  induction instances with

  | nil =>
      intro actor hFound

      simp [
        DTR.findActor?
      ] at hFound

  | cons head remaining inductionHypothesis =>
      intro actor hFound

      by_cases hHead :
          head.name = actorName

      · rw [
          DTR.findActor?,
          if_pos hHead
        ] at hFound

        obtain rfl :=
          Option.some.inj hFound

        exact hHead

      · rw [
          DTR.findActor?,
          if_neg hHead
        ] at hFound

        exact
          inductionHypothesis
            actor
            hFound

/--
A route's receiver instance is what its entry's known rebec is bound to in the sending instance.

The fact routed-send transfer needs and that neither `generalRouteFor_sourceEndpoint` (source
endpoint) nor `generalRouteFor_receiverProvenance` (declared class and server) supplies: the
*identity* of the receiver, tied to the binding the source rule resolves through.
`Correctness.sendTargetActor?_knownRebec_eq_bindings` reduces the source side to exactly this
`Store.lookup`, so composing the two identifies the two receivers without any uniqueness assumption.

Definitional in the one success branch — `generalRouteFor` sets `receiverInstance := receiver.name`
where `receiver` is `model.actor?` of the bound instance name, and `DTR.GeneralActorInstance.name` of a
resolved actor is the name it was resolved by. The three refusal branches close as its own docstring
says: an unbound known rebec, an unresolvable receiver instance, or a receiver whose class disagrees
with the entry's.
-/
theorem generalRouteFor_receiverInstance
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    {entry : GeneralOutputPortEntry}
    {route : GeneralRoute}
    (hRoute :
      generalRouteFor
          model
          actor
          entry =
        .ok route) :
    Store.lookup
        actor.bindings
        entry.knownRebec =
      some route.receiverInstance := by

  cases hBinding :
      Store.lookup
        actor.bindings
        entry.knownRebec with

  | none =>
      simp [
        generalRouteFor,
        hBinding
      ] at hRoute

  | some receiverInstance =>

      cases hActor :
          model.actor? receiverInstance with

      | none =>
          simp [
            generalRouteFor,
            hBinding,
            hActor
          ] at hRoute

      | some receiver =>

          by_cases hClassMatch :
              receiver.className = entry.receiverClass

          · simp only [
              generalRouteFor,
              hBinding,
              hActor,
              hClassMatch,
              if_pos,
              Except.ok.injEq
            ] at hRoute

            subst hRoute

            dsimp only

            rw [
              findActor?_name_local
                model.instances
                receiverInstance
                receiver
                (by
                  unfold DTR.GeneralModel.actor? at hActor
                  exact hActor)
            ]

          · simp [
              generalRouteFor,
              hBinding,
              hActor,
              hClassMatch
            ] at hRoute

/--
A route's source endpoint is its sending actor's name and its entry's output port.

`generalRouteFor` copies `actor.name` and `entry.outputPort` verbatim into the route it builds, so
this is the definitional content of its one success branch. The three refusal branches close the way
its own docstring says: an unbound known rebec, an unresolvable receiver instance, or a receiver whose
class disagrees with the entry's.
-/
theorem generalRouteFor_sourceEndpoint
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    {entry : GeneralOutputPortEntry}
    {route : GeneralRoute}
    (hRoute :
      generalRouteFor
          model
          actor
          entry =
        .ok route) :
    route.senderInstance = actor.name ∧
      route.outputPort = entry.outputPort := by

  cases hBinding :
      Store.lookup
        actor.bindings
        entry.knownRebec with

  | none =>
      simp [
        generalRouteFor,
        hBinding
      ] at hRoute

  | some receiverInstance =>

      cases hActor :
          model.actor? receiverInstance with

      | none =>
          simp [
            generalRouteFor,
            hBinding,
            hActor
          ] at hRoute

      | some receiver =>

          by_cases hClassMatch :
              receiver.className = entry.receiverClass

          · simp only [
              generalRouteFor,
              hBinding,
              hActor,
              hClassMatch,
              if_pos,
              Except.ok.injEq
            ] at hRoute

            subst hRoute

            exact ⟨rfl, rfl⟩

          · simp [
              generalRouteFor,
              hBinding,
              hActor,
              hClassMatch
            ] at hRoute

/--
A route's delay is its entry's delay.

The middle link of the chain that carries a source send's own `after` into the generated event.
`LF.GeneralStmt.setPort` carries no delay at all — on the LF side a send's delay is a property of the
connection the value travels along, which is why stage E keys output ports by send site — so a routed
send's delay reaches the target's tag only by being copied entry to route to connection. This lemma is
the route step; `generalOutputPortEntryFor_delay` below is the entry step, and
`generalConnectionFrom?_siteFaithful` already returns the connection step.

Definitional in the one success branch, and the three refusals close exactly as this lemma's two
companions above close them: an unbound known rebec, an unresolvable receiver instance, or a receiver
whose class disagrees with the entry's.
-/
theorem generalRouteFor_delay
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    {entry : GeneralOutputPortEntry}
    {route : GeneralRoute}
    (hRoute :
      generalRouteFor
          model
          actor
          entry =
        .ok route) :
    route.delay = entry.delay := by

  cases hBinding :
      Store.lookup
        actor.bindings
        entry.knownRebec with

  | none =>
      simp [
        generalRouteFor,
        hBinding
      ] at hRoute

  | some receiverInstance =>

      cases hActor :
          model.actor? receiverInstance with

      | none =>
          simp [
            generalRouteFor,
            hBinding,
            hActor
          ] at hRoute

      | some receiver =>

          by_cases hClassMatch :
              receiver.className = entry.receiverClass

          · simp only [
              generalRouteFor,
              hBinding,
              hActor,
              hClassMatch,
              if_pos,
              Except.ok.injEq
            ] at hRoute

            subst hRoute

            rfl

          · simp [
              generalRouteFor,
              hBinding,
              hActor,
              hClassMatch
            ] at hRoute

/--
One instance's emitted routes carry its own name and their entries' ports.

The pointwise content of `routesOfEntries`, extracted as two list equations so the endpoint
combinatorics below never unfolds the traversal. Proved by the same induction
`mem_of_routesOfEntries` uses, with the three refusal branches closing the same way.
-/
theorem routesOfEntries_endpoints
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance) :
    ∀ (env : GeneralOutputPortEnv)
      (routes : List GeneralRoute),
      routesOfEntries
          model
          actor
          env =
        .ok routes →
      List.map
          (fun route =>
            (route.senderInstance, route.outputPort.value))
          routes =
        List.map
          (fun entry =>
            (actor.name, entry.outputPort.value))
          env := by

  intro env
  induction env with

  | nil =>
      intro routes hRoutes

      simp [
        routesOfEntries
      ] at hRoutes

      subst hRoutes

      rfl

  | cons entry remaining IH =>
      intro routes hRoutes

      cases hHead :
          generalRouteFor
            model
            actor
            entry with

      | error diagnostic =>
          simp [
            routesOfEntries,
            hHead
          ] at hRoutes

      | ok headRoute =>

          cases hTail :
              routesOfEntries
                model
                actor
                remaining with

          | error diagnostic =>
              simp [
                routesOfEntries,
                hHead,
                hTail
              ] at hRoutes

          | ok tailRoutes =>

              rw [
                show
                    routesOfEntries
                        model
                        actor
                        (entry :: remaining) =
                      .ok
                        (headRoute ::
                          tailRoutes) from by
                  simp [
                    routesOfEntries,
                    hHead,
                    hTail
                  ]
              ] at hRoutes

              obtain rfl :=
                Except.ok.inj
                  hRoutes.symm

              obtain ⟨hSender, hPort⟩ :=
                generalRouteFor_sourceEndpoint
                  hHead

              rw [
                List.map_cons,
                List.map_cons,
                IH
                  tailRoutes
                  hTail,
                hSender,
                hPort
              ]

/--
Emitted connections carry their routes' source endpoints.

`generalConnectionsOf` is `routes.map generalConnectionOf`, and `generalConnectionOf` sets
`sourceInstance := route.senderInstance` and `sourcePort := route.outputPort` definitionally, so the
source-endpoint projection of the connection list *is* the source-endpoint projection of the route
list. This is rung C, and it is a `map` composition and nothing else — the mirror of
`generalConnectionsOf_targetEndpoints`, which does the same for the other end.
-/
theorem generalConnectionsOf_sourceEndpoints :
    ∀ (routes : List GeneralRoute),
      List.map
          (fun connection =>
            (connection.sourceInstance, connection.sourcePort))
          (generalConnectionsOf routes) =
        List.map
          (fun route =>
            (route.senderInstance, route.outputPort))
          routes := by

  intro routes
  induction routes with

  | nil =>
      simp [
        generalConnectionsOf
      ]

  | cons route remaining IH =>
      simp only [
        generalConnectionsOf
      ] at IH ⊢

      simp [
        generalConnectionOf,
        IH
      ]

end Translation

namespace LF

/-!
## First-match resolution under source-endpoint uniqueness

Rung D, and the point of the whole module. `connectionFrom?` returns the first connection at a
source endpoint; under uniqueness of that projection there is only one, so "first" is "the one".

Deliberately **not** a generic lookup library: it is one lemma about one function, in the shape its
one consumer needs, following the convention `Relico/LF/GeneralKindOrigin.lean` records on
`connectionFrom?_mem_and_source` (the elimination direction of the same function — this is the
introduction direction, and the two together are all `connectionFrom?` has).
-/

/--
Under source-endpoint uniqueness, a member connection is what its own endpoint resolves to.

The hypothesis is `Nodup` of the **source**-endpoint projection, which is exactly the key
`connectionFrom?` searches on. Note what is *not* assumed: nothing about target endpoints, nothing
about the connection being unique in any other sense, and no injectivity of any naming function.

The head case needs the head's endpoint to differ from the sought one whenever the sought connection
is in the tail, and that is precisely what the `Nodup` head-freshness gives — via the endpoint
projection, so two connections differing in other fields but sharing an endpoint are excluded by
hypothesis rather than by wishful thinking.
-/
theorem connectionFrom?_eq_of_mem_of_sourceEndpoints_nodup :
    ∀ (connections : List GeneralConnection)
      (connection : GeneralConnection),
      connection ∈ connections →
      (List.map
        (fun candidate =>
          (candidate.sourceInstance, candidate.sourcePort))
        connections).Nodup →
      connectionFrom?
          connections
          connection.sourceInstance
          connection.sourcePort =
        some connection := by

  intro connections
  induction connections with

  | nil =>
      intro connection hMem _

      cases hMem

  | cons head remaining IH =>
      intro connection hMem hNodup

      rw [
        List.map_cons
      ] at hNodup

      obtain ⟨hHeadFresh, hTailNodup⟩ :=
        List.nodup_cons.mp hNodup

      rcases List.mem_cons.mp hMem with
        hHere | hThere

      · subst hHere

        simp [
          connectionFrom?
        ]

      · -- The head cannot share the sought endpoint: it would be a duplicate in the projection.
        have hEndpointNe :
            (head.sourceInstance, head.sourcePort) ≠
              (connection.sourceInstance,
                connection.sourcePort) := by
          intro hEqual

          apply hHeadFresh

          rw [hEqual]

          exact
            List.mem_map_of_mem
              hThere

        by_cases hInstance :
            head.sourceInstance =
              connection.sourceInstance

        · have hPort :
              head.sourcePort ≠
                connection.sourcePort := by
            intro hEqual

            exact
              hEndpointNe
                (by
                  rw [hInstance, hEqual])

          rw [
            connectionFrom?,
            if_pos hInstance,
            if_neg hPort
          ]

          exact
            IH
              connection
              hThere
              hTailNodup

        · rw [
            connectionFrom?,
            if_neg hInstance
          ]

          exact
            IH
              connection
              hThere
              hTailNodup

end LF

namespace Translation

/-!
## Site monotonicity and injectivity of the send walk

Two additive facts about `Translation.externalSendsFromIndex`, and then the one that matters: the
send a walk emits at a given site carries the known rebec of the statement at that position.

These are the prerequisites the routed-send transfer will need once the correspondence records
*where* in its declared body a reactor is executing. They are proved here, ahead of that change and
independently of it, because they are true of the walk alone — nothing below mentions a runtime
state, a correspondence, or an environment. If the position-carrying relation is never built, these
remain correct statements about the translation.

The walk stamps `site := ⟨bodyKey, index⟩` on each external send it emits and advances `index` by one
per statement whatever the statement is (`Relico/Translation/GeneralRouting.lean`, the five arms at
`externalSendsFromIndex`). So the index is strictly increasing along the emitted list, which is what
makes a site identify a send.
-/

/--
Every send a walk emits sits at this level's own address, at or after the index the walk started
from.

The monotonicity fact, and the whole content of injectivity below: a walk from `index` cannot emit
anything addressed earlier than `index`. Six arms rather than a wildcard, matching the definition's
own refusal to use one — the three non-external arms advance the index without emitting, the
external arm emits at exactly `index` before advancing, and the conditional arm walks both branches
one level down before resuming.

**Stage H split the conclusion into a position and a residue.** A send's site is
`levelPath ++ (position :: rest)`: `position` is the statement's index *in this level*, which is
what `index ≤ position` still compares, and `rest` is empty for a send at this level and carries a
side plus a deeper position for one inside a branch. The `Nat` comparison survived the move to
paths because what injectivity needs is that two sends of one level differ in the component that
level owns, and nesting below that component cannot change it.

The recursion is explicit rather than by `induction`, because the conditional arm applies this
statement at two deeper levels and a list induction offers a hypothesis for the tail only.
-/
private theorem site_index_ge_of_mem_externalSendsFromIndex
    (bodyKey : GeneralBodyKey)
    (levelPath : List Nat)
    (body : DTR.GeneralBody) :
    ∀ (index : Nat)
      (send : GeneralExternalSend),
      send ∈
        externalSendsFromIndex
          bodyKey
          levelPath
          index
          body →
      ∃ (position : Nat)
        (rest : List Nat),
        index ≤ position ∧
        send.site.index =
          levelPath ++
            (position :: rest) := by

  intro index send hMember

  cases body with

  | nil =>

      rw [
        externalSendsFromIndex_nil
      ] at hMember

      cases hMember

  | cons statement remaining =>

      cases statement with

      | assign target value =>
          rw [
            externalSendsFromIndex_assign
          ] at hMember

          obtain ⟨position, rest, hGe, hPath⟩ :=
            site_index_ge_of_mem_externalSendsFromIndex
              bodyKey
              levelPath
              remaining
              (index + 1)
              send
              hMember

          exact
            ⟨position,
             rest,
             by omega,
             hPath⟩

      | trace tag =>
          rw [
            externalSendsFromIndex_trace
          ] at hMember

          obtain ⟨position, rest, hGe, hPath⟩ :=
            site_index_ge_of_mem_externalSendsFromIndex
              bodyKey
              levelPath
              remaining
              (index + 1)
              send
              hMember

          exact
            ⟨position,
             rest,
             by omega,
             hPath⟩

      | send target message arguments delay =>

          cases target with

          | selfTarget =>
              rw [
                externalSendsFromIndex_send_selfTarget
              ] at hMember

              obtain ⟨position, rest, hGe, hPath⟩ :=
                site_index_ge_of_mem_externalSendsFromIndex
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  send
                  hMember

              exact
                ⟨position,
                 rest,
                 by omega,
                 hPath⟩

          | knownRebec knownRebec =>
              rw [
                externalSendsFromIndex_send_knownRebec,
                List.mem_cons
              ] at hMember

              cases hMember with

              | inl hHere =>
                  subst hHere

                  exact
                    ⟨index,
                     [],
                     Nat.le_refl index,
                     rfl⟩

              | inr hThere =>
                  obtain ⟨position, rest, hGe, hPath⟩ :=
                    site_index_ge_of_mem_externalSendsFromIndex
                      bodyKey
                      levelPath
                      remaining
                      (index + 1)
                      send
                      hThere

                  exact
                    ⟨position,
                     rest,
                     by omega,
                     hPath⟩

      | ifThenElse condition thenBody elseBody =>
          rw [
            externalSendsFromIndex_ifThenElse,
            List.mem_append,
            List.mem_append
          ] at hMember

          cases hMember with

          | inl hBranch =>

              cases hBranch with

              | inl hThen =>
                  obtain ⟨position, rest, _, hPath⟩ :=
                    site_index_ge_of_mem_externalSendsFromIndex
                      bodyKey
                      (levelPath ++
                        [index, 0])
                      thenBody
                      0
                      send
                      hThen

                  refine
                    ⟨index,
                     0 :: position :: rest,
                     Nat.le_refl index,
                     ?_⟩

                  simpa using hPath

              | inr hElse =>
                  obtain ⟨position, rest, _, hPath⟩ :=
                    site_index_ge_of_mem_externalSendsFromIndex
                      bodyKey
                      (levelPath ++
                        [index, 1])
                      elseBody
                      0
                      send
                      hElse

                  refine
                    ⟨index,
                     1 :: position :: rest,
                     Nat.le_refl index,
                     ?_⟩

                  simpa using hPath

          | inr hThere =>
              obtain ⟨position, rest, hGe, hPath⟩ :=
                site_index_ge_of_mem_externalSendsFromIndex
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  send
                  hThere

              exact
                ⟨position,
                 rest,
                 by omega,
                 hPath⟩

/--
Every send a walk emits is tagged with the walk's own body key.

The companion of monotonicity, and what lets a caller holding a site's *body* component decide which
half of `externalSendsOfClass` a send came from — the constructor's walk tags `.constructor`, a
message server's walk tags `.messageServer` of its own name, so the two halves are separated by this
projection alone. Same six arms, same reason for spelling them out.

The conditional arm is the reason this is quantified over `levelPath`: a branch is walked at a deeper
level and carries the *same* body key, which is precisely the fact that keeps this projection a
whole-body property under nesting. Nothing about the statement moved.
-/
theorem externalSendsFromIndex_site_body
    (bodyKey : GeneralBodyKey)
    (levelPath : List Nat)
    (body : DTR.GeneralBody) :
    ∀ (index : Nat)
      (send : GeneralExternalSend),
      send ∈
        externalSendsFromIndex
          bodyKey
          levelPath
          index
          body →
      send.site.body = bodyKey := by

  intro index send hMember

  cases body with

  | nil =>

      rw [
        externalSendsFromIndex_nil
      ] at hMember

      cases hMember

  | cons statement remaining =>

      cases statement with

      | assign target value =>
          rw [
            externalSendsFromIndex_assign
          ] at hMember

          exact
            externalSendsFromIndex_site_body
              bodyKey
              levelPath
              remaining
              (index + 1)
              send
              hMember

      | trace tag =>
          rw [
            externalSendsFromIndex_trace
          ] at hMember

          exact
            externalSendsFromIndex_site_body
              bodyKey
              levelPath
              remaining
              (index + 1)
              send
              hMember

      | send target message arguments delay =>

          cases target with

          | selfTarget =>
              rw [
                externalSendsFromIndex_send_selfTarget
              ] at hMember

              exact
                externalSendsFromIndex_site_body
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  send
                  hMember

          | knownRebec knownRebec =>
              rw [
                externalSendsFromIndex_send_knownRebec,
                List.mem_cons
              ] at hMember

              cases hMember with

              | inl hHere =>
                  subst hHere

                  rfl

              | inr hThere =>
                  exact
                    externalSendsFromIndex_site_body
                      bodyKey
                      levelPath
                      remaining
                      (index + 1)
                      send
                      hThere

      | ifThenElse condition thenBody elseBody =>
          rw [
            externalSendsFromIndex_ifThenElse,
            List.mem_append,
            List.mem_append
          ] at hMember

          cases hMember with

          | inl hBranch =>

              cases hBranch with

              | inl hThen =>
                  exact
                    externalSendsFromIndex_site_body
                      bodyKey
                      (levelPath ++
                        [index, 0])
                      thenBody
                      0
                      send
                      hThen

              | inr hElse =>
                  exact
                    externalSendsFromIndex_site_body
                      bodyKey
                      (levelPath ++
                        [index, 1])
                      elseBody
                      0
                      send
                      hElse

          | inr hThere =>
              exact
                externalSendsFromIndex_site_body
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  send
                  hThere

/--
A class's external send tagged with the constructor's body key came from the constructor's body.

The half-selection lemma. `externalSendsOfClass` is the constructor's walk appended to the message
servers'; every send of the second half is tagged `.messageServer` of some name, so a `.constructor`
tag places the send in the first half. Used by the initializer, which knows only that its site's body
component is `.constructor`.
-/
theorem mem_externalSendsOfBody_constructor_of_mem_externalSendsOfClass
    {reactiveClass : DTR.GeneralReactiveClass}
    {send : GeneralExternalSend}
    (hMember :
      send ∈
        externalSendsOfClass
          reactiveClass)
    (hBody :
      send.site.body = .constructor) :
    send ∈
      externalSendsOfBody
        .constructor
        reactiveClass.constructor.body := by

  unfold externalSendsOfClass at hMember

  rcases List.mem_append.mp hMember with
    hConstructor | hServers

  · exact hConstructor

  · -- A message server's walk tags `.messageServer`, contradicting the hypothesis.
    exfalso

    revert hServers

    induction reactiveClass.messageServers with

    | nil =>
        intro hServers

        simp [
          externalSendsOfMessageServers
        ] at hServers

    | cons server rest innerIH =>
        intro hServers

        unfold externalSendsOfMessageServers at hServers

        rcases List.mem_append.mp hServers with
          hHere | hThere

        · rw [
            externalSendsFromIndex_site_body
              (.messageServer server.name)
              []
              server.body
              0
              send
              hHere
          ] at hBody

          cases hBody

        · exact innerIH hThere

/--
**Site injectivity.** Within one walk, a site identifies its send.

Not a claim about routes, ports, or connections — and in particular not a weakening of **F48**, which
refutes injectivity of `outputPortNameFor`. This says only that the *addressing* the walk performs is
injective, which is true because the index strictly increases: at an external head the head sits at
`index` while everything the tail emits sits at `index + 1` or later, so the two cases of
`List.mem_cons` cannot collide.

**Under nesting the same sentence needs two disjointness facts instead of one**, and both are local
helpers of the proof. A send inside a branch is addressed under this level's `index`, so it cannot
collide with anything the enclosing level emits at `index + 1` or later; and the two branches of one
conditional differ in the side component, `0` against `1`, so a then-send cannot collide with an
else-send. Those are exactly the two properties the alternating encoding was chosen for, and this
theorem is where they are spent. Nothing about the statement moved except the level it is quantified
over.
-/
theorem externalSendsFromIndex_site_injective
    (bodyKey : GeneralBodyKey)
    (levelPath : List Nat)
    (body : DTR.GeneralBody) :
    ∀ (index : Nat)
      (first second : GeneralExternalSend),
      first ∈
        externalSendsFromIndex
          bodyKey
          levelPath
          index
          body →
      second ∈
        externalSendsFromIndex
          bodyKey
          levelPath
          index
          body →
      first.site = second.site →
      first = second := by

  intro index first second hFirst hSecond hSite

  cases body with

  | nil =>

      rw [
        externalSendsFromIndex_nil
      ] at hFirst

      cases hFirst

  | cons statement remaining =>

      cases statement with

      | assign target value =>
          rw [
            externalSendsFromIndex_assign
          ] at hFirst hSecond

          exact
            externalSendsFromIndex_site_injective
              bodyKey
              levelPath
              remaining
              (index + 1)
              first
              second
              hFirst
              hSecond
              hSite

      | trace tag =>
          rw [
            externalSendsFromIndex_trace
          ] at hFirst hSecond

          exact
            externalSendsFromIndex_site_injective
              bodyKey
              levelPath
              remaining
              (index + 1)
              first
              second
              hFirst
              hSecond
              hSite

      | send target message arguments delay =>

          cases target with

          | selfTarget =>
              rw [
                externalSendsFromIndex_send_selfTarget
              ] at hFirst hSecond

              exact
                externalSendsFromIndex_site_injective
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  first
                  second
                  hFirst
                  hSecond
                  hSite

          | knownRebec knownRebec =>
              rw [
                externalSendsFromIndex_send_knownRebec,
                List.mem_cons
              ] at hFirst hSecond

              cases hFirst with

              | inl hFirstHead =>

                  cases hSecond with

                  | inl hSecondHead =>
                      rw [hFirstHead, hSecondHead]

                  | inr hSecondTail =>
                      -- The head is at `index`; the tail starts at `index + 1`.
                      exfalso

                      obtain ⟨position, rest, hGe, hPath⟩ :=
                        site_index_ge_of_mem_externalSendsFromIndex
                          bodyKey
                          levelPath
                          remaining
                          (index + 1)
                          second
                          hSecondTail

                      rw [
                        hFirstHead
                      ] at hSite

                      rw [
                        ← hSite
                      ] at hPath

                      simp only at hPath

                      have hCons :
                          [index] =
                            position :: rest :=
                        List.append_cancel_left
                          hPath

                      injection hCons with hPosition _

                      omega

              | inr hFirstTail =>

                  cases hSecond with

                  | inl hSecondHead =>
                      exfalso

                      obtain ⟨position, rest, hGe, hPath⟩ :=
                        site_index_ge_of_mem_externalSendsFromIndex
                          bodyKey
                          levelPath
                          remaining
                          (index + 1)
                          first
                          hFirstTail

                      rw [
                        hSecondHead
                      ] at hSite

                      rw [
                        hSite
                      ] at hPath

                      simp only at hPath

                      have hCons :
                          [index] =
                            position :: rest :=
                        List.append_cancel_left
                          hPath

                      injection hCons with hPosition _

                      omega

                  | inr hSecondTail =>
                      exact
                        externalSendsFromIndex_site_injective
                          bodyKey
                          levelPath
                          remaining
                          (index + 1)
                          first
                          second
                          hFirstTail
                          hSecondTail
                          hSite

      | ifThenElse condition thenBody elseBody =>

          -- A branch's sends against the enclosing level's: the branch sits under this
          -- level's `index` and the tail sits at `index + 1` or later.
          have hBranchVsTail :
              ∀ (side : Nat)
                (branchBody : DTR.GeneralBody)
                (branchSend tailSend : GeneralExternalSend),
                branchSend ∈
                  externalSendsFromIndex
                    bodyKey
                    (levelPath ++
                      [index, side])
                    0
                    branchBody →
                tailSend ∈
                  externalSendsFromIndex
                    bodyKey
                    levelPath
                    (index + 1)
                    remaining →
                branchSend.site ≠ tailSend.site := by

            intro side branchBody branchSend tailSend hBranch hTail hEqual

            obtain ⟨branchPosition, branchRest, _, hBranchPath⟩ :=
              site_index_ge_of_mem_externalSendsFromIndex
                bodyKey
                (levelPath ++
                  [index, side])
                branchBody
                0
                branchSend
                hBranch

            obtain ⟨tailPosition, tailRest, hTailGe, hTailPath⟩ :=
              site_index_ge_of_mem_externalSendsFromIndex
                bodyKey
                levelPath
                remaining
                (index + 1)
                tailSend
                hTail

            rw [
              hEqual,
              hTailPath
            ] at hBranchPath

            simp only [
              List.append_assoc,
              List.cons_append,
              List.nil_append
            ] at hBranchPath

            have hCons :
                tailPosition :: tailRest =
                  index ::
                    side ::
                      branchPosition ::
                        branchRest :=
              List.append_cancel_left
                hBranchPath

            injection hCons with hPosition _

            omega

          -- The two branches against each other: same position, different side.
          have hThenVsElse :
              ∀ (thenSend elseSend : GeneralExternalSend),
                thenSend ∈
                  externalSendsFromIndex
                    bodyKey
                    (levelPath ++
                      [index, 0])
                    0
                    thenBody →
                elseSend ∈
                  externalSendsFromIndex
                    bodyKey
                    (levelPath ++
                      [index, 1])
                    0
                    elseBody →
                thenSend.site ≠ elseSend.site := by

            intro thenSend elseSend hThen hElse hEqual

            obtain ⟨thenPosition, thenRest, _, hThenPath⟩ :=
              site_index_ge_of_mem_externalSendsFromIndex
                bodyKey
                (levelPath ++
                  [index, 0])
                thenBody
                0
                thenSend
                hThen

            obtain ⟨elsePosition, elseRest, _, hElsePath⟩ :=
              site_index_ge_of_mem_externalSendsFromIndex
                bodyKey
                (levelPath ++
                  [index, 1])
                elseBody
                0
                elseSend
                hElse

            rw [
              hEqual,
              hElsePath
            ] at hThenPath

            simp only [
              List.append_assoc,
              List.cons_append,
              List.nil_append
            ] at hThenPath

            have hCons :
                index ::
                    1 ::
                      elsePosition ::
                        elseRest =
                  index ::
                    0 ::
                      thenPosition ::
                        thenRest :=
              List.append_cancel_left
                hThenPath

            simp at hCons

          rw [
            externalSendsFromIndex_ifThenElse,
            List.mem_append,
            List.mem_append
          ] at hFirst hSecond

          cases hFirst with

          | inl hFirstBranch =>

              cases hFirstBranch with

              | inl hFirstThen =>

                  cases hSecond with

                  | inl hSecondBranch =>

                      cases hSecondBranch with

                      | inl hSecondThen =>
                          exact
                            externalSendsFromIndex_site_injective
                              bodyKey
                              (levelPath ++
                                [index, 0])
                              thenBody
                              0
                              first
                              second
                              hFirstThen
                              hSecondThen
                              hSite

                      | inr hSecondElse =>
                          exact
                            absurd
                              hSite
                              (hThenVsElse
                                first
                                second
                                hFirstThen
                                hSecondElse)

                  | inr hSecondTail =>
                      exact
                        absurd
                          hSite
                          (hBranchVsTail
                            0
                            thenBody
                            first
                            second
                            hFirstThen
                            hSecondTail)

              | inr hFirstElse =>

                  cases hSecond with

                  | inl hSecondBranch =>

                      cases hSecondBranch with

                      | inl hSecondThen =>
                          exact
                            absurd
                              hSite.symm
                              (hThenVsElse
                                second
                                first
                                hSecondThen
                                hFirstElse)

                      | inr hSecondElse =>
                          exact
                            externalSendsFromIndex_site_injective
                              bodyKey
                              (levelPath ++
                                [index, 1])
                              elseBody
                              0
                              first
                              second
                              hFirstElse
                              hSecondElse
                              hSite

                  | inr hSecondTail =>
                      exact
                        absurd
                          hSite
                          (hBranchVsTail
                            1
                            elseBody
                            first
                            second
                            hFirstElse
                            hSecondTail)

          | inr hFirstTail =>

              cases hSecond with

              | inl hSecondBranch =>

                  cases hSecondBranch with

                  | inl hSecondThen =>
                      exact
                        absurd
                          hSite.symm
                          (hBranchVsTail
                            0
                            thenBody
                            second
                            first
                            hSecondThen
                            hFirstTail)

                  | inr hSecondElse =>
                      exact
                        absurd
                          hSite.symm
                          (hBranchVsTail
                            1
                            elseBody
                            second
                            first
                            hSecondElse
                            hFirstTail)

              | inr hSecondTail =>
                  exact
                    externalSendsFromIndex_site_injective
                      bodyKey
                      levelPath
                      remaining
                      (index + 1)
                      first
                      second
                      hFirstTail
                      hSecondTail
                      hSite

/--
**The chain payload.** The send a walk emits at a position carries the known rebec of the statement
at that position.

This is the lemma the routed-send transfer will call, and stating it now — quantified over a `drop`
rather than over a pinned index — is what makes it independent of the correspondence change. A caller
that knows its running suffix is `body.drop k` and whose head is an external send obtains the rebec
of the *emitted* send at `index + k`, which is what `entry.knownRebec` was copied from.

The induction generalises both `index` and `k`. At `k = 0` the head of the drop is the statement, so
the emitted head is the answer and monotonicity rules the tail out; at `k + 1` the drop moves into the
tail and every arm advances `index` in step, which is why the arithmetic `index + (k + 1) =
(index + 1) + k` closes each case.

No uniqueness of routes, ports, or connections is used or implied. Site injectivity above is about
the walk's own addressing, and this lemma consumes only monotonicity.

**Stage H reads the sought address as `levelPath ++ [index + k]`**, a position in *this* level rather
than a bare number, and that is what keeps the `drop` in the statement honest: `body.drop k` is a
suffix of this level's statement list, so the send it names is addressed at this level too. The
conditional arm is discharged rather than recursed into, and deliberately: a send inside a branch has
a longer path than any single-component address, so it cannot be the send the caller asked about. The
branch's own sends are reached by applying this lemma to the branch body, which is what a caller
holding a nested running suffix will do.
-/
theorem externalSendsFromIndex_knownRebec_of_drop
    (bodyKey : GeneralBodyKey)
    (levelPath : List Nat)
    (body : DTR.GeneralBody) :
    ∀ (index k : Nat)
      (rebec : KnownRebecName)
      (message : MsgName)
      (arguments : List DTR.GeneralExpr)
      (delay : Delay)
      (rest : DTR.GeneralBody)
      (send : GeneralExternalSend),
      body.drop k =
        DTR.GeneralStmt.send
            (.knownRebec rebec)
            message
            arguments
            delay ::
          rest →
      send ∈
        externalSendsFromIndex
          bodyKey
          levelPath
          index
          body →
      send.site.index =
        levelPath ++
          [index + k] →
      send.knownRebec = rebec := by

  intro index k rebec message arguments delay rest send hDrop hMember hSite

  cases body with

  | nil =>

      rw [
        List.drop_nil
      ] at hDrop

      cases hDrop

  | cons statement remaining =>

      cases k with

      | zero =>
          rw [
            List.drop_zero
          ] at hDrop

          injection hDrop with hHead _

          subst hHead

          rw [
            externalSendsFromIndex_send_knownRebec,
            List.mem_cons
          ] at hMember

          cases hMember with

          | inl hHere =>
              subst hHere

              rfl

          | inr hThere =>
              exfalso

              obtain ⟨position, tailRest, hGe, hPath⟩ :=
                site_index_ge_of_mem_externalSendsFromIndex
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  send
                  hThere

              rw [
                hSite
              ] at hPath

              have hCons :
                  [index + 0] =
                    position :: tailRest :=
                List.append_cancel_left
                  hPath

              injection hCons with hPosition _

              omega

      | succ k' =>
          rw [
            List.drop_succ_cons
          ] at hDrop

          have hArith :
              index + (k' + 1) =
                (index + 1) + k' := by
            omega

          cases statement with

          | assign target value =>
              rw [
                externalSendsFromIndex_assign
              ] at hMember

              exact
                externalSendsFromIndex_knownRebec_of_drop
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  k'
                  rebec
                  message
                  arguments
                  delay
                  rest
                  send
                  hDrop
                  hMember
                  (by
                    rw [hSite, hArith])

          | trace tag =>
              rw [
                externalSendsFromIndex_trace
              ] at hMember

              exact
                externalSendsFromIndex_knownRebec_of_drop
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  k'
                  rebec
                  message
                  arguments
                  delay
                  rest
                  send
                  hDrop
                  hMember
                  (by
                    rw [hSite, hArith])

          | send target headMessage headArguments headDelay =>

              cases target with

              | selfTarget =>
                  rw [
                    externalSendsFromIndex_send_selfTarget
                  ] at hMember

                  exact
                    externalSendsFromIndex_knownRebec_of_drop
                      bodyKey
                      levelPath
                      remaining
                      (index + 1)
                      k'
                      rebec
                      message
                      arguments
                      delay
                      rest
                      send
                      hDrop
                      hMember
                      (by
                        rw [hSite, hArith])

              | knownRebec headRebec =>
                  rw [
                    externalSendsFromIndex_send_knownRebec,
                    List.mem_cons
                  ] at hMember

                  cases hMember with

                  | inl hHere =>
                      -- The head sits at `index`, but the sought site is strictly later.
                      exfalso

                      subst hHere

                      simp only at hSite

                      have hCons :
                          levelPath ++
                              [index] =
                            levelPath ++
                              [index + (k' + 1)] :=
                        hSite

                      injection
                        List.append_cancel_left
                          hCons with hPosition _

                      omega

                  | inr hThere =>
                      exact
                        externalSendsFromIndex_knownRebec_of_drop
                          bodyKey
                          levelPath
                          remaining
                          (index + 1)
                          k'
                          rebec
                          message
                          arguments
                          delay
                          rest
                          send
                          hDrop
                          hThere
                          (by
                            rw [hSite, hArith])

          | ifThenElse condition thenBody elseBody =>
              rw [
                externalSendsFromIndex_ifThenElse,
                List.mem_append,
                List.mem_append
              ] at hMember

              cases hMember with

              | inl hBranch =>
                  -- A send inside a branch is addressed with a longer path than any
                  -- single position of this level, so it is not the send asked about.
                  exfalso

                  cases hBranch with

                  | inl hThen =>
                      obtain ⟨position, branchRest, _, hPath⟩ :=
                        site_index_ge_of_mem_externalSendsFromIndex
                          bodyKey
                          (levelPath ++
                            [index, 0])
                          thenBody
                          0
                          send
                          hThen

                      rw [
                        hSite
                      ] at hPath

                      simp only [
                        List.append_assoc,
                        List.cons_append,
                        List.nil_append
                      ] at hPath

                      have hCons :
                          [index + (k' + 1)] =
                            index ::
                              0 ::
                                position ::
                                  branchRest :=
                        List.append_cancel_left
                          hPath

                      simp at hCons

                  | inr hElse =>
                      obtain ⟨position, branchRest, _, hPath⟩ :=
                        site_index_ge_of_mem_externalSendsFromIndex
                          bodyKey
                          (levelPath ++
                            [index, 1])
                          elseBody
                          0
                          send
                          hElse

                      rw [
                        hSite
                      ] at hPath

                      simp only [
                        List.append_assoc,
                        List.cons_append,
                        List.nil_append
                      ] at hPath

                      have hCons :
                          [index + (k' + 1)] =
                            index ::
                              1 ::
                                position ::
                                  branchRest :=
                        List.append_cancel_left
                          hPath

                      simp at hCons

              | inr hThere =>
                  exact
                    externalSendsFromIndex_knownRebec_of_drop
                      bodyKey
                      levelPath
                      remaining
                      (index + 1)
                      k'
                      rebec
                      message
                      arguments
                      delay
                      rest
                      send
                      hDrop
                      hThere
                      (by
                        rw [hSite, hArith])

/--
A send of a statement's own walk is a send of the body that statement sits in.

The structural bridge stage H's nested addressing needs, and the only new induction it needs.
`externalSendsFromIndex_cons` holds whatever the head statement is, so walking down to
`body.drop position` costs one `List.mem_append` step per statement and no case analysis. The index
arithmetic is the flat lemmas' `index + (position + 1) = (index + 1) + position` in the other
direction.

Both nested consumers below run on this. For a `here` path the statement is an external send and its
own walk is a one-element list; for a branch path it is a conditional and its own walk is the two
branch walks appended, so a send found inside a branch injects into the enclosing body's walk without
anything being said about the *rest* of the enclosing body. That is what makes the nested case cheap:
no site-shape contradiction, no `Nodup`, no ordering.
-/
theorem mem_externalSendsFromIndex_of_mem_externalSendsFromStmt
    (bodyKey : GeneralBodyKey)
    (levelPath : List Nat)
    (body : DTR.GeneralBody) :
    ∀ (index position : Nat)
      (statement : DTR.GeneralStmt)
      (rest : DTR.GeneralBody)
      (send : GeneralExternalSend),
      body.drop position =
        statement :: rest →
      send ∈
        externalSendsFromStmt
          bodyKey
          levelPath
          (index + position)
          statement →
      send ∈
        externalSendsFromIndex
          bodyKey
          levelPath
          index
          body := by

  induction body with

  | nil =>
      intro index position statement rest send hDrop _

      rw [
        List.drop_nil
      ] at hDrop

      cases hDrop

  | cons head remaining inductionHypothesis =>
      intro index position statement rest send hDrop hMember

      cases position with

      | zero =>
          rw [
            List.drop_zero
          ] at hDrop

          injection hDrop with hHead _

          subst hHead

          rw [
            externalSendsFromIndex_cons
          ]

          refine
            List.mem_append.mpr
              (Or.inl ?_)

          simpa using hMember

      | succ position =>
          rw [
            List.drop_succ_cons
          ] at hDrop

          rw [
            externalSendsFromIndex_cons
          ]

          refine
            List.mem_append.mpr
              (Or.inr ?_)

          refine
            inductionHypothesis
              (index + 1)
              position
              statement
              rest
              send
              hDrop
              ?_

          rw [
            show
                index + 1 + position =
                  index + (position + 1) from by
              omega
          ]

          exact hMember

/--
A send witnessed at a path of a body is emitted by that body's walk, at that path's address.

The **positive** half of stage H's nested addressing: `GeneralSendAtPath` says a source
body has an external send at a path, and this says the routing walk emits a send there, carrying that
send's rebec and delay. It is what the two uniqueness lemmas below run on, and it is proved in the
easy direction — every case *constructs* a membership rather than refuting one.

Recursion on the derivation, one case per constructor:

* `here` reaches the statement with the bridge above and reads the emitted record off
  `externalSendsFromStmt`'s external-send arm.
* `thenBranch` and `elseBranch` apply this statement to the branch body at the branch's own level,
  `levelPath ++ [index + position, side]` from index `0`, and inject the result through the
  conditional arm and then through the bridge. The address arithmetic is
  `shiftHeadPath_zero` plus one `List.append_assoc`, because a branch counts its positions from zero.

No site-shape reasoning appears, which is the point: an earlier plan for this lemma went through
`site_index_ge_of_mem_externalSendsFromIndex` to *locate* a given send, and constructing the witness
instead makes the branch cases three lines each. Uniqueness is then a separate step and is already
committed as `externalSendsFromIndex_site_injective`.
-/
theorem exists_mem_externalSendsFromIndex_of_path
    (bodyKey : GeneralBodyKey)
    {body : DTR.GeneralBody}
    {path : List Nat}
    {rebec : KnownRebecName}
    {message : MsgName}
    {delay : Delay}
    (hPath :
      GeneralSendAtPath
        body
        path
        rebec
        message
        delay) :
    ∀ (levelPath : List Nat)
      (index : Nat),
      ∃ send ∈
          externalSendsFromIndex
            bodyKey
            levelPath
            index
            body,
        send.site.index =
            levelPath ++
              shiftHeadPath
                index
                path ∧
          send.knownRebec = rebec ∧
            send.delay = delay := by

  induction hPath with

  | @here body position rebec message arguments delay rest hDrop =>
      intro levelPath index

      refine
        ⟨{
           site :=
             {
               body :=
                 bodyKey

               index :=
                 levelPath ++
                   [index + position]
             }

           knownRebec :=
             rebec

           message :=
             message

           delay :=
             delay
         },
         ?_,
         rfl,
         rfl,
         rfl⟩

      refine
        mem_externalSendsFromIndex_of_mem_externalSendsFromStmt
          bodyKey
          levelPath
          body
          index
          position
          _
          rest
          _
          hDrop
          ?_

      simp [
        externalSendsFromStmt
      ]

  | @thenBranch body position condition thenBody elseBody rest path rebec message delay hDrop _ inductionHypothesis =>
      intro levelPath index

      obtain ⟨send, hMember, hSite, hRebec, hDelay⟩ :=
        inductionHypothesis
          (levelPath ++
            [index + position, 0])
          0

      refine
        ⟨send,
         ?_,
         ?_,
         hRebec,
         hDelay⟩

      · refine
          mem_externalSendsFromIndex_of_mem_externalSendsFromStmt
            bodyKey
            levelPath
            body
            index
            position
            _
            rest
            send
            hDrop
            ?_

        simp only [
          externalSendsFromStmt
        ]

        exact
          List.mem_append.mpr
            (Or.inl hMember)

      · -- The branch was walked from index `0`, so its own shift is the identity; only the
        -- enclosing level's head component moves.
        simp only [
          shiftHeadPath_zero
        ] at hSite

        simpa [
          shiftHeadPath
        ] using hSite

  | @elseBranch body position condition thenBody elseBody rest path rebec message delay hDrop _ inductionHypothesis =>
      intro levelPath index

      obtain ⟨send, hMember, hSite, hRebec, hDelay⟩ :=
        inductionHypothesis
          (levelPath ++
            [index + position, 1])
          0

      refine
        ⟨send,
         ?_,
         ?_,
         hRebec,
         hDelay⟩

      · refine
          mem_externalSendsFromIndex_of_mem_externalSendsFromStmt
            bodyKey
            levelPath
            body
            index
            position
            _
            rest
            send
            hDrop
            ?_

        simp only [
          externalSendsFromStmt
        ]

        exact
          List.mem_append.mpr
            (Or.inr hMember)

      · -- The branch was walked from index `0`, so its own shift is the identity; only the
        -- enclosing level's head component moves.
        simp only [
          shiftHeadPath_zero
        ] at hSite

        simpa [
          shiftHeadPath
        ] using hSite

/--
The send a walk emits at a nested path carries that path's known rebec.

The nested analogue of `externalSendsFromIndex_knownRebec_of_drop`, and the fact stage H's
correspondence establisher needs: a routing entry at a nested site describes the source send that
*is* at that path, branch or no branch.

Proved by uniqueness rather than by a second traversal. `exists_mem_externalSendsFromIndex_of_path`
emits a witness at the same address with the right rebec, `externalSendsFromIndex_site_body` puts both
sends' sites on the same body key, and `externalSendsFromIndex_site_injective` — the committed §4.3
claim — then forces the two sends equal. So this lemma spends injectivity instead of re-deriving it,
which is why it is short and why no site-shape reasoning appears.

Restricted to a one-component path this is the flat lemma: `shiftHeadPath index [k]` is
`[index + k]`.
-/
theorem externalSendsFromIndex_knownRebec_of_path
    (bodyKey : GeneralBodyKey)
    (levelPath : List Nat)
    {body : DTR.GeneralBody}
    {path : List Nat}
    {rebec : KnownRebecName}
    {message : MsgName}
    {delay : Delay}
    (index : Nat)
    {send : GeneralExternalSend}
    (hPath :
      GeneralSendAtPath
        body
        path
        rebec
        message
        delay)
    (hMember :
      send ∈
        externalSendsFromIndex
          bodyKey
          levelPath
          index
          body)
    (hSite :
      send.site.index =
        levelPath ++
          shiftHeadPath
            index
            path) :
    send.knownRebec = rebec ∧
      send.delay = delay := by

  obtain ⟨witness, hWitnessMember, hWitnessSite, hWitnessRebec, hWitnessDelay⟩ :=
    exists_mem_externalSendsFromIndex_of_path
      bodyKey
      hPath
      levelPath
      index

  have hSameSite :
      send.site = witness.site := by
    have hSendBody :
        send.site.body = bodyKey :=
      externalSendsFromIndex_site_body
        bodyKey
        levelPath
        body
        index
        send
        hMember

    have hWitnessBody :
        witness.site.body = bodyKey :=
      externalSendsFromIndex_site_body
        bodyKey
        levelPath
        body
        index
        witness
        hWitnessMember

    have hIndex :
        send.site.index =
          witness.site.index := by
      rw [
        hSite,
        hWitnessSite
      ]

    have hBody :
        send.site.body =
          witness.site.body := by
      rw [
        hSendBody,
        hWitnessBody
      ]

    cases hSendSite : send.site with
    | mk sendBody sendIndex =>
        cases hWitnessSite' : witness.site with
        | mk witnessBody witnessIndex =>
            rw [
              hSendSite,
              hWitnessSite'
            ] at hIndex hBody

            simp_all

  have hEqual :
      send = witness :=
    externalSendsFromIndex_site_injective
      bodyKey
      levelPath
      body
      index
      send
      witness
      hMember
      hWitnessMember
      hSameSite

  subst hEqual

  exact
    ⟨hWitnessRebec,
     hWitnessDelay⟩

/--
The send a walk emits at a statement's own position carries that statement's delay.

The delay companion of `externalSendsFromIndex_knownRebec_of_drop` above, proved by the same recursion
generalising both `index` and `k`: at `k = 0` the head of the drop is the statement and the emitted head
is the answer, with monotonicity ruling the tail out; at `k + 1` the drop moves into the tail and every
arm advances `index` in step, so `index + (k + 1) = (index + 1) + k` closes each case.

No uniqueness of routes, ports, or connections is used or implied; this consumes only monotonicity.

Stage H reads the address as `levelPath ++ [index + k]` here for the same reason it does above, and the
conditional arm is discharged the same way, by path length rather than by recursion. The two proofs
were near-copies before this change and remain near-copies after it, which is the shape this
development already chose: the sentences are different claims about the same walk and each is cited on
its own.
-/
theorem externalSendsFromIndex_delay_of_drop
    (bodyKey : GeneralBodyKey)
    (levelPath : List Nat)
    (body : DTR.GeneralBody) :
    ∀ (index k : Nat)
      (rebec : KnownRebecName)
      (message : MsgName)
      (arguments : List DTR.GeneralExpr)
      (delay : Delay)
      (rest : DTR.GeneralBody)
      (send : GeneralExternalSend),
      body.drop k =
        DTR.GeneralStmt.send
            (.knownRebec rebec)
            message
            arguments
            delay ::
          rest →
      send ∈
        externalSendsFromIndex
          bodyKey
          levelPath
          index
          body →
      send.site.index =
        levelPath ++
          [index + k] →
      send.delay = delay := by

  intro index k rebec message arguments delay rest send hDrop hMember hSite

  cases body with

  | nil =>

      rw [
        List.drop_nil
      ] at hDrop

      cases hDrop

  | cons statement remaining =>

      cases k with

      | zero =>
          rw [
            List.drop_zero
          ] at hDrop

          injection hDrop with hHead _

          subst hHead

          rw [
            externalSendsFromIndex_send_knownRebec,
            List.mem_cons
          ] at hMember

          cases hMember with

          | inl hHere =>
              subst hHere

              rfl

          | inr hThere =>
              exfalso

              obtain ⟨position, tailRest, hGe, hPath⟩ :=
                site_index_ge_of_mem_externalSendsFromIndex
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  send
                  hThere

              rw [
                hSite
              ] at hPath

              have hCons :
                  [index + 0] =
                    position :: tailRest :=
                List.append_cancel_left
                  hPath

              injection hCons with hPosition _

              omega

      | succ k' =>
          rw [
            List.drop_succ_cons
          ] at hDrop

          have hArith :
              index + (k' + 1) =
                (index + 1) + k' := by
            omega

          cases statement with

          | assign target value =>
              rw [
                externalSendsFromIndex_assign
              ] at hMember

              exact
                externalSendsFromIndex_delay_of_drop
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  k'
                  rebec
                  message
                  arguments
                  delay
                  rest
                  send
                  hDrop
                  hMember
                  (by
                    rw [hSite, hArith])

          | trace tag =>
              rw [
                externalSendsFromIndex_trace
              ] at hMember

              exact
                externalSendsFromIndex_delay_of_drop
                  bodyKey
                  levelPath
                  remaining
                  (index + 1)
                  k'
                  rebec
                  message
                  arguments
                  delay
                  rest
                  send
                  hDrop
                  hMember
                  (by
                    rw [hSite, hArith])

          | send target headMessage headArguments headDelay =>

              cases target with

              | selfTarget =>
                  rw [
                    externalSendsFromIndex_send_selfTarget
                  ] at hMember

                  exact
                    externalSendsFromIndex_delay_of_drop
                      bodyKey
                      levelPath
                      remaining
                      (index + 1)
                      k'
                      rebec
                      message
                      arguments
                      delay
                      rest
                      send
                      hDrop
                      hMember
                      (by
                        rw [hSite, hArith])

              | knownRebec headRebec =>
                  rw [
                    externalSendsFromIndex_send_knownRebec,
                    List.mem_cons
                  ] at hMember

                  cases hMember with

                  | inl hHere =>
                      -- The head sits at `index`, but the sought site is strictly later.
                      exfalso

                      subst hHere

                      simp only at hSite

                      have hCons :
                          levelPath ++
                              [index] =
                            levelPath ++
                              [index + (k' + 1)] :=
                        hSite

                      injection
                        List.append_cancel_left
                          hCons with hPosition _

                      omega

                  | inr hThere =>
                      exact
                        externalSendsFromIndex_delay_of_drop
                          bodyKey
                          levelPath
                          remaining
                          (index + 1)
                          k'
                          rebec
                          message
                          arguments
                          delay
                          rest
                          send
                          hDrop
                          hThere
                          (by
                            rw [hSite, hArith])

          | ifThenElse condition thenBody elseBody =>
              rw [
                externalSendsFromIndex_ifThenElse,
                List.mem_append,
                List.mem_append
              ] at hMember

              cases hMember with

              | inl hBranch =>
                  -- A send inside a branch is addressed with a longer path than any
                  -- single position of this level, so it is not the send asked about.
                  exfalso

                  cases hBranch with

                  | inl hThen =>
                      obtain ⟨position, branchRest, _, hPath⟩ :=
                        site_index_ge_of_mem_externalSendsFromIndex
                          bodyKey
                          (levelPath ++
                            [index, 0])
                          thenBody
                          0
                          send
                          hThen

                      rw [
                        hSite
                      ] at hPath

                      simp only [
                        List.append_assoc,
                        List.cons_append,
                        List.nil_append
                      ] at hPath

                      have hCons :
                          [index + (k' + 1)] =
                            index ::
                              0 ::
                                position ::
                                  branchRest :=
                        List.append_cancel_left
                          hPath

                      simp at hCons

                  | inr hElse =>
                      obtain ⟨position, branchRest, _, hPath⟩ :=
                        site_index_ge_of_mem_externalSendsFromIndex
                          bodyKey
                          (levelPath ++
                            [index, 1])
                          elseBody
                          0
                          send
                          hElse

                      rw [
                        hSite
                      ] at hPath

                      simp only [
                        List.append_assoc,
                        List.cons_append,
                        List.nil_append
                      ] at hPath

                      have hCons :
                          [index + (k' + 1)] =
                            index ::
                              1 ::
                                position ::
                                  branchRest :=
                        List.append_cancel_left
                          hPath

                      simp at hCons

              | inr hThere =>
                  exact
                    externalSendsFromIndex_delay_of_drop
                      bodyKey
                      levelPath
                      remaining
                      (index + 1)
                      k'
                      rebec
                      message
                      arguments
                      delay
                      rest
                      send
                      hDrop
                      hThere
                      (by
                        rw [hSite, hArith])

/-!
## The entry-to-send inversion

The converse of `outputPortEnvOf_sites`, and the lemma the routed-send transfer needs. Everything in
`Relico/Translation/GeneralRouting.lean` runs *sends to entries*: `outputPortEnvOf_sites` and
`generalOutputPortEntriesOf_sites` project the `site` field forwards, and
`exists_generalEntryAtSite?_of_mem_sends` looks an entry up from a send. Nothing ran the other way, so
an entry recovered from a compiled `.setPort` head carried no information about the *statement* it came
from — in particular not its known rebec, which is what decides where the message goes.

This section supplies that direction. Three rungs: the field equation for one resolved entry, the
traversal inversion, and the `outputPortEnvOf`-level composition its consumer calls.

**No uniqueness is introduced.** The inversion is existential in the send, and deliberately so: two
sites of one class may resolve to entries agreeing on every field, and nothing here or downstream
distinguishes them. What the consumer needs is a send whose `knownRebec` the entry copied, and *any*
such send serves, because the receiver is computed from the rebec rather than from the site.
-/

/--
A resolved entry copies its send's known rebec.

The companion of `generalOutputPortEntryFor_site`, proved the same way and for the same reason: the
statement compiler matches on `site` while the routing table reads `knownRebec`, and if the two could
come from different sends every emitted connection would still be well-formed while pointing at the
wrong receiver. Both fields are copied in the one success branch, so the content is the four-way case
split that rules the refusals out.
-/
theorem generalOutputPortEntryFor_knownRebec
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {entry : GeneralOutputPortEntry}
    (hResolved :
      generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry) :
    entry.knownRebec = send.knownRebec := by

  cases hKnown :
      sendingClass.knownRebec?
        send.knownRebec with

  | none =>
      simp [
        generalOutputPortEntryFor,
        hKnown
      ] at hResolved

  | some declaration =>

      cases hClass :
          DTR.findClass?
            classes
            declaration.className with

      | none =>
          simp [
            generalOutputPortEntryFor,
            hKnown,
            hClass
          ] at hResolved

      | some receivingClass =>

          cases hServer :
              receivingClass.messageServer?
                send.message with

          | none =>
              simp [
                generalOutputPortEntryFor,
                hKnown,
                hClass,
                hServer
              ] at hResolved

          | some receivingServer =>

              cases hPayload :
                  generalPortPayloadFor
                    receivingClass.name
                    send.message
                    receivingServer.parameters with

              | error diagnostic =>
                  simp [
                    generalOutputPortEntryFor,
                    hKnown,
                    hClass,
                    hServer,
                    hPayload
                  ] at hResolved

              | ok portPayload =>
                  simp only [
                    generalOutputPortEntryFor,
                    hKnown,
                    hClass,
                    hServer,
                    hPayload,
                    Except.ok.injEq
                  ] at hResolved

                  subst hResolved

                  rfl

/--
A resolved entry copies its send's delay.

The entry step of the delay chain, and the companion of `generalOutputPortEntryFor_knownRebec` above in
the same sense: both fields are copied verbatim in the one success branch, so the content of the lemma
is the four-way case split that rules the refusals out. Needed because the statement compiler emits a
`setPort` carrying no delay, so the *only* record of a routed statement's `after` in the generated
program is the entry this send resolved to, and from there the route and the connection.
-/
theorem generalOutputPortEntryFor_delay
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {entry : GeneralOutputPortEntry}
    (hResolved :
      generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry) :
    entry.delay = send.delay := by

  cases hKnown :
      sendingClass.knownRebec?
        send.knownRebec with

  | none =>
      simp [
        generalOutputPortEntryFor,
        hKnown
      ] at hResolved

  | some declaration =>

      cases hClass :
          DTR.findClass?
            classes
            declaration.className with

      | none =>
          simp [
            generalOutputPortEntryFor,
            hKnown,
            hClass
          ] at hResolved

      | some receivingClass =>

          cases hServer :
              receivingClass.messageServer?
                send.message with

          | none =>
              simp [
                generalOutputPortEntryFor,
                hKnown,
                hClass,
                hServer
              ] at hResolved

          | some receivingServer =>

              cases hPayload :
                  generalPortPayloadFor
                    receivingClass.name
                    send.message
                    receivingServer.parameters with

              | error diagnostic =>
                  simp [
                    generalOutputPortEntryFor,
                    hKnown,
                    hClass,
                    hServer,
                    hPayload
                  ] at hResolved

              | ok portPayload =>
                  simp only [
                    generalOutputPortEntryFor,
                    hKnown,
                    hClass,
                    hServer,
                    hPayload,
                    Except.ok.injEq
                  ] at hResolved

                  subst hResolved

                  rfl

/--
Every entry of a resolved environment was resolved from one of the numbered sends.

The traversal inversion. Structurally the same induction as
`generalOutputPortEntriesOf_receiverProvenance` above, but returning the *send* rather than the
receiver facts, so that a caller can read any field off it rather than a fixed list.
-/
private theorem exists_send_of_mem_generalOutputPortEntriesOf
    (classes : List DTR.GeneralReactiveClass)
    (sendingClass : DTR.GeneralReactiveClass)
    (allSends : List GeneralExternalSend) :
    ∀ (numbered : List (GeneralExternalSend × Nat))
      (env : GeneralOutputPortEnv),
      generalOutputPortEntriesOf
          classes
          sendingClass
          allSends
          numbered =
        .ok env →
      ∀ entry ∈ env,
        ∃ pair ∈ numbered,
          generalOutputPortEntryFor
              classes
              sendingClass
              allSends
              pair.1
              pair.2 =
            .ok entry := by

  intro numbered
  induction numbered with

  | nil =>
      intro env hEntries entry hMember

      simp [
        generalOutputPortEntriesOf
      ] at hEntries

      subst hEntries

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro env hEntries entry hMember

      rcases head with
        ⟨send, ordinal⟩

      cases hHead :
          generalOutputPortEntryFor
            classes
            sendingClass
            allSends
            send
            ordinal with

      | error diagnostic =>
          simp [
            generalOutputPortEntriesOf,
            hHead
          ] at hEntries

      | ok headEntry =>

          cases hTail :
              generalOutputPortEntriesOf
                classes
                sendingClass
                allSends
                remaining with

          | error diagnostic =>
              simp [
                generalOutputPortEntriesOf,
                hHead,
                hTail
              ] at hEntries

          | ok tailEntries =>

              rw [
                show
                    generalOutputPortEntriesOf
                        classes
                        sendingClass
                        allSends
                        ((send, ordinal) :: remaining) =
                      .ok
                        (headEntry ::
                          tailEntries) from by
                  simp [
                    generalOutputPortEntriesOf,
                    hHead,
                    hTail
                  ]
              ] at hEntries

              obtain rfl :=
                Except.ok.inj
                  hEntries.symm

              cases List.mem_cons.mp hMember with

              | inl hHere =>
                  subst hHere

                  exact
                    ⟨(send, ordinal),
                     List.mem_cons_self,
                     hHead⟩

              | inr hThere =>
                  obtain ⟨pair, hPairMem, hPair⟩ :=
                    inductionHypothesis
                      tailEntries
                      hTail
                      entry
                      hThere

                  exact
                    ⟨pair,
                     List.mem_cons_of_mem
                       _
                       hPairMem,
                     hPair⟩

/--
**The entry-to-send inversion, at the environment level.** Every entry of a class's resolved
output-port environment came from one of that class's external sends, and copies its known rebec, its
site and its delay.

The lemma `Correctness.generalActorCorresponds_constructorEntry` consumes.
`numberExternalSends_sends` is what turns membership in the *numbered* list into membership in
`externalSendsOfClass`, and it is why the ordinal never appears in the conclusion: the numbering exists
to disambiguate generated port names, and no field this lemma returns depends on it.

The delay component is returned for the same reason as the rebec: a compiled `LF.GeneralStmt.setPort`
carries no delay, so a routed statement's `after` survives into the generated program only through the
entry, and a caller holding an entry needs both fields tied back to a statement.

Existential in the send, and no uniqueness anywhere. Two sites may produce indistinguishable entries;
the consumer needs field equations against *some* originating send, not a unique origin.
-/
theorem exists_send_of_mem_outputPortEnv
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    {entry : GeneralOutputPortEntry}
    (hResolved :
      outputPortEnvOf
          classes
          sendingClass =
        .ok env)
    (hEntry :
      entry ∈ env) :
    ∃ send ∈
        externalSendsOfClass
          sendingClass,
      entry.knownRebec = send.knownRebec ∧
        entry.site = send.site ∧
          entry.delay = send.delay := by

  unfold outputPortEnvOf at hResolved

  obtain ⟨pair, hPairMem, hPair⟩ :=
    exists_send_of_mem_generalOutputPortEntriesOf
      classes
      sendingClass
      (externalSendsOfClass
        sendingClass)
      (numberedExternalSendsOfClass
        sendingClass)
      env
      hResolved
      entry
      hEntry

  refine
    ⟨pair.1,
     ?_,
     generalOutputPortEntryFor_knownRebec
       hPair,
     generalOutputPortEntryFor_site
       hPair,
     generalOutputPortEntryFor_delay
       hPair⟩

  -- The numbering is a `map`-preserving relabelling, so a numbered pair's send is one of the class's.
  have hSends :
      (numberedExternalSendsOfClass
          sendingClass).map
          (fun candidate =>
            candidate.1) =
        externalSendsOfClass
          sendingClass := by
    unfold numberedExternalSendsOfClass

    exact
      numberExternalSends_sends
        (externalSendsOfClass
          sendingClass)
        []

  rw [
    ← hSends
  ]

  exact
    List.mem_map_of_mem
      hPairMem

/-!
## Rung B, across instances

`routesOfInstances` concatenates one block per instance, so the assembly is `List.nodup_append`:
each block is `Nodup` by rung A composed with `routesOfEntries_endpoints`, and two blocks are
disjoint because every route of one block carries that block's own `actor.name` in the first
endpoint component.

The per-instance environment `Nodup` is a **hypothesis**, quantified over the instances being
walked. That is deliberate: it means the guard is consulted once at the call site, where the compiled
program is in hand, rather than re-derived per instance inside the induction — which would force this
module to reconstruct each instance's compiled reactor, and no theorem here needs to.
-/

/--
Every source endpoint of one instance's block names that instance.

The membership form of `routesOfEntries_endpoints`' first component, which is what the disjointness
argument below consumes: two blocks cannot share an endpoint because their first components are two
different instance names.
-/
private theorem senderInstance_of_mem_routesOfEntries
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    (hRoutes :
      routesOfEntries
          model
          actor
          env =
        .ok routes)
    {route : GeneralRoute}
    (hMem :
      route ∈ routes) :
    route.senderInstance = actor.name := by

  have hEndpoints :=
    routesOfEntries_endpoints
      model
      actor
      env
      routes
      hRoutes

  have hPairMem :
      (route.senderInstance, route.outputPort.value) ∈
        List.map
          (fun entry =>
            (actor.name, entry.outputPort.value))
          env := by
    rw [
      ← hEndpoints
    ]

    exact
      List.mem_map_of_mem
        hMem

  obtain ⟨_, _, hPair⟩ :=
    List.mem_map.mp hPairMem

  exact
    (Prod.mk.inj hPair).1.symm

/--
One instance's routes have pairwise-distinct source endpoints.

Rung A carried through the traversal equation: the block's endpoint projection *is* the environment's
port projection with the actor's name attached, and prefixing a constant to every pair preserves
duplicate freedom.
-/
private theorem routesOfEntries_sourceEndpoints_nodup
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    {env : GeneralOutputPortEnv}
    {routes : List GeneralRoute}
    (hRoutes :
      routesOfEntries
          model
          actor
          env =
        .ok routes)
    (hEnvNodup :
      (List.map
        (fun entry =>
          entry.outputPort.value)
        env).Nodup) :
    (List.map
      (fun route =>
        (route.senderInstance, route.outputPort.value))
      routes).Nodup := by

  rw [
    routesOfEntries_endpoints
      model
      actor
      env
      routes
      hRoutes
  ]

  -- Attaching one constant first component is injective on the second, so the environment's
  -- `Nodup` transfers. Proved by the generic reflecting-projection lemma rather than by a second
  -- induction over the environment.
  refine
    nodup_map_of_reflecting
      (fun entry =>
        entry.outputPort.value)
      (fun entry =>
        (actor.name, entry.outputPort.value))
      ?_
      env
      hEnvNodup

  intro first second hEqual

  exact
    (Prod.mk.inj hEqual).2

/--
Every route of a table names one of the walked instances as its sender.

The cross-block separation fact, standalone. Stated over the whole traversal rather than proved
inline inside the assembly below, because inline it would be an induction whose hypotheses mention
the outer instance list and would have to be generalized past them — the standalone form needs no
hypotheses at all beyond the traversal's success.
-/
private theorem senderInstance_mem_of_mem_routesOfInstances
    (model : DTR.GeneralModel) :
    ∀ (instances : List DTR.GeneralActorInstance)
      (routes : List GeneralRoute),
      routesOfInstances
          model
          instances =
        .ok routes →
      ∀ route ∈ routes,
        route.senderInstance ∈
          List.map
            (fun candidate =>
              candidate.name)
            instances := by

  intro instances
  induction instances with

  | nil =>
      intro routes hRoutes route hRoute

      simp [
        routesOfInstances
      ] at hRoutes

      subst hRoutes

      cases hRoute

  | cons candidate rest IH =>
      intro routes hRoutes route hRoute

      obtain
          ⟨_sendingClass,
           _env,
           headRoutes,
           tailRoutes,
           _hClass,
           _hEnv,
           hHead,
           hTail,
           hSplit⟩ :=
        routesOfInstances_cons_inv
          model
          candidate
          rest
          routes
          hRoutes

      subst hSplit

      rw [
        List.map_cons
      ]

      rcases List.mem_append.mp hRoute with
        hInHead | hInTail

      · rw [
          senderInstance_of_mem_routesOfEntries
            hHead
            hInHead
        ]

        exact List.mem_cons_self

      · exact
          List.mem_cons_of_mem
            _
            (IH
              tailRoutes
              hTail
              route
              hInTail)

/--
**Rung B, assembled.** The whole routing table of a model has pairwise-distinct source endpoints,
given that each walked instance's environment has distinct output-port names.

The induction is over the instance list, with `routesOfInstances_cons_inv` supplying the
`headRoutes ++ tailRoutes` split. The head block is `Nodup` by the lemma above; the tail is the
inductive hypothesis; and the cross-block disjointness is the whole content of the append case: a
shared endpoint would have first component both `actor.name` (by
`senderInstance_of_mem_routesOfEntries` on the head) and some *other* instance's name (same lemma,
applied inside the tail through a second `cons_inv` walk), contradicting the instance-name
distinctness hypothesis.

**Nothing here assumes output-port-name injectivity.** Within a block the separation comes from the
guard-decided environment `Nodup`; across blocks it comes from the first endpoint component. Those are
the two independent channels F34 and F42 could otherwise exploit, and both are closed without any
claim about `outputPortNameFor`.
-/
theorem routesOfInstances_sourceEndpoints_nodup
    (model : DTR.GeneralModel) :
    ∀ (instances : List DTR.GeneralActorInstance)
      (routes : List GeneralRoute),
      routesOfInstances
          model
          instances =
        .ok routes →
      (∀ actor ∈ instances,
        ∀ env : GeneralOutputPortEnv,
          (∃ sendingClass : DTR.GeneralReactiveClass,
            model.class? actor.className =
                some sendingClass ∧
              outputPortEnvOf
                  model.classes
                  sendingClass =
                .ok env) →
          (List.map
            (fun entry =>
              entry.outputPort.value)
            env).Nodup) →
      (List.map
        (fun actor =>
          actor.name)
        instances).Nodup →
      (List.map
        (fun route =>
          (route.senderInstance, route.outputPort.value))
        routes).Nodup := by

  intro instances
  induction instances with

  | nil =>
      intro routes hRoutes _ _

      simp [
        routesOfInstances
      ] at hRoutes

      subst hRoutes

      simp

  | cons actor remaining IH =>
      intro routes hRoutes hEnvNodup hNames

      obtain
          ⟨sendingClass,
           env,
           headRoutes,
           tailRoutes,
           hClass,
           hEnv,
           hHead,
           hTail,
           hSplit⟩ :=
        routesOfInstances_cons_inv
          model
          actor
          remaining
          routes
          hRoutes

      subst hSplit

      obtain ⟨hNameFresh, hNamesTail⟩ :=
        List.nodup_cons.mp
          (by
            rw [
              List.map_cons
            ] at hNames

            exact hNames)

      have hHeadNodup :
          (List.map
            (fun route =>
              (route.senderInstance, route.outputPort.value))
            headRoutes).Nodup :=
        routesOfEntries_sourceEndpoints_nodup
          hHead
          (hEnvNodup
            actor
            List.mem_cons_self
            env
            ⟨sendingClass, hClass, hEnv⟩)

      have hTailNodup :
          (List.map
            (fun route =>
              (route.senderInstance, route.outputPort.value))
            tailRoutes).Nodup :=
        IH
          tailRoutes
          hTail
          (fun candidate hCandidate =>
            hEnvNodup
              candidate
              (List.mem_cons_of_mem
                actor
                hCandidate))
          hNamesTail

      -- Every tail route's sender is one of `remaining`'s instance names, which `hNameFresh`
      -- separates from `actor.name`. This is the cross-block disjointness, and it is where the
      -- first endpoint component does the work that no port-name fact could.
      have hTailSender :
          ∀ route ∈ tailRoutes,
            route.senderInstance ∈
              List.map
                (fun candidate =>
                  candidate.name)
                remaining :=
        senderInstance_mem_of_mem_routesOfInstances
          model
          remaining
          tailRoutes
          hTail

      rw [
        List.map_append
      ]

      refine
        List.nodup_append.mpr
          ⟨hHeadNodup, hTailNodup, ?_⟩

      intro headEndpoint hHeadEndpoint tailEndpoint hTailEndpoint

      obtain ⟨headRoute, hHeadRoute, hHeadPair⟩ :=
        List.mem_map.mp hHeadEndpoint

      obtain ⟨tailRoute, hTailRoute, hTailPair⟩ :=
        List.mem_map.mp hTailEndpoint

      subst hHeadPair

      subst hTailPair

      intro hEqual

      apply hNameFresh

      rw [
        ← senderInstance_of_mem_routesOfEntries
            hHead
            hHeadRoute,
        (Prod.mk.inj hEqual).1
      ]

      exact
        hTailSender
          tailRoute
          hTailRoute

/--
**Rung B at the model level.** An accepted model's whole routing table has pairwise-distinct source
endpoints.

`routesOf` walks `priorityOrderedInstances`, which is a permutation of `model.instances`, so the two
hypotheses transfer: the environment hypothesis through `mem_priorityOrderedInstances_iff`, and the
name distinctness through `priorityOrderedInstances_names_perm`. Priority order is irrelevant to
uniqueness — it reorders the table and nothing more — which is exactly what those two permutation
lemmas exist to say.

The instance-name distinctness is spelled as a `Nodup` over `model.instances` rather than as
`model.wellFormed`, so a caller may supply it from `namesUniqueAndValid`'s topology conjunct or from
anywhere else. That keeps this theorem from taking a whole well-formedness premise for one clause.
-/
theorem routesOf_sourceEndpoints_nodup
    {model : DTR.GeneralModel}
    {routes : List GeneralRoute}
    (hRoutes :
      routesOf model =
        .ok routes)
    (hEnvNodup :
      ∀ actor ∈ model.instances,
        ∀ env : GeneralOutputPortEnv,
          (∃ sendingClass : DTR.GeneralReactiveClass,
            model.class? actor.className =
                some sendingClass ∧
              outputPortEnvOf
                  model.classes
                  sendingClass =
                .ok env) →
          (List.map
            (fun entry =>
              entry.outputPort.value)
            env).Nodup)
    (hNames :
      (List.map
        (fun actor =>
          actor.name)
        model.instances).Nodup) :
    (List.map
      (fun route =>
        (route.senderInstance, route.outputPort.value))
      routes).Nodup := by

  unfold routesOf at hRoutes

  refine
    routesOfInstances_sourceEndpoints_nodup
      model
      (priorityOrderedInstances
        model)
      routes
      hRoutes
      ?_
      ?_

  · intro actor hActor

    exact
      hEnvNodup
        actor
        ((mem_priorityOrderedInstances_iff
            model
            actor).mp
          hActor)

  · exact
      (priorityOrderedInstances_names_perm
          model).nodup_iff.mpr
        hNames

/--
**Rung C, in `Nodup` form.** An accepted model's emitted connections have pairwise-distinct source
endpoints.

The composition rung D consumes: `compileGeneralModel_connections` identifies the program's connection
list with `generalConnectionsOf` of the routing table, `generalConnectionsOf_sourceEndpoints` turns the
connection projection into the route projection, and `routesOf_sourceEndpoints_nodup` supplies the
`Nodup`.

Stated on the `PortName.value` projection because that is the spelling the guard decides. A caller
holding `Nodup` at `PortName` would be holding something stronger than `declaredNames` gives.
-/
theorem compileGeneralModel_sourceEndpoints_nodup
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      compileGeneralModel model =
        .ok program)
    (hEnvNodup :
      ∀ actor ∈ model.instances,
        ∀ env : GeneralOutputPortEnv,
          (∃ sendingClass : DTR.GeneralReactiveClass,
            model.class? actor.className =
                some sendingClass ∧
              outputPortEnvOf
                  model.classes
                  sendingClass =
                .ok env) →
          (List.map
            (fun entry =>
              entry.outputPort.value)
            env).Nodup)
    (hNames :
      (List.map
        (fun actor =>
          actor.name)
        model.instances).Nodup) :
    (List.map
      (fun connection =>
        (connection.sourceInstance, connection.sourcePort.value))
      program.connections).Nodup := by

  obtain ⟨routes, hRoutes, hConnections⟩ :=
    compileGeneralModel_connections
      hCompiled

  rw [
    hConnections
  ]

  -- The endpoint projection at `PortName` is available (rung C); composing `PortName.value` onto it
  -- is what makes the two sides line up with the guard's spelling.
  have hProjection :
      List.map
          (fun connection =>
            (connection.sourceInstance, connection.sourcePort.value))
          (generalConnectionsOf routes) =
        List.map
          (fun route =>
            (route.senderInstance, route.outputPort.value))
          routes := by
    rw [
      show
          (fun (connection : LF.GeneralConnection) =>
              (connection.sourceInstance, connection.sourcePort.value)) =
            (fun pair =>
                (pair.1, pair.2.value)) ∘
              (fun (connection : LF.GeneralConnection) =>
                (connection.sourceInstance, connection.sourcePort)) from
          rfl,
      show
          (fun (route : GeneralRoute) =>
              (route.senderInstance, route.outputPort.value)) =
            (fun pair =>
                (pair.1, pair.2.value)) ∘
              (fun (route : GeneralRoute) =>
                (route.senderInstance, route.outputPort)) from
          rfl,
      ← List.map_map,
      ← List.map_map,
      generalConnectionsOf_sourceEndpoints
        routes
    ]

  rw [hProjection]

  exact
    routesOf_sourceEndpoints_nodup
      hRoutes
      hEnvNodup
      hNames

/-!
## The site → entry → route → connection chain

**Direction matters here, and this is not the converse of the kind-origin theorem.**
`Translation.exists_route_of_connectionFrom?` runs *from* an arbitrary runtime connection and can
only produce *some* route, because F48 makes more impossible. This section runs the other way: from a
**concrete accepted send site**, whose entry the compiler looked up and whose route the compiler
emitted, to the connection `connectionFrom?` then selects. Nothing below claims that an arbitrary
connection determines a send site, and no theorem here is stated in that direction.

The site → entry hop already exists: `generalEntryAtSite?` is the function `compileGeneralStmt`
itself calls, `Translation.compileGeneralStmt_send_knownRebec_ok` says the statement at a site
compiles to `.setPort entry.outputPort …` for exactly the entry that lookup returns, and
`generalEntryAtSite?_mem` places that entry in the environment. So the missing hop was entry → route,
which is the lemma below.
-/

/--
Every entry of a resolved environment has a route emitted from it.

The introduction direction of `routesOfEntries`, and the converse of `mem_of_routesOfEntries` in
`Relico/LF/GeneralKindOrigin.lean` — that one runs from a route to its entry, this one from an entry
to its route. Both are needed and neither implies the other: the traversal is a `map`-like walk that
can refuse, so "every entry has a route" is a consequence of the walk *succeeding*, which is what
`hRoutes` says.
-/
theorem route_of_mem_outputPortEnv
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance) :
    ∀ (env : GeneralOutputPortEnv)
      (routes : List GeneralRoute),
      routesOfEntries
          model
          actor
          env =
        .ok routes →
      ∀ entry ∈ env,
        ∃ route ∈ routes,
          generalRouteFor
              model
              actor
              entry =
            .ok route := by

  intro env
  induction env with

  | nil =>
      intro routes hRoutes entry hEntry

      cases hEntry

  | cons candidate remaining IH =>
      intro routes hRoutes entry hEntry

      cases hHead :
          generalRouteFor
            model
            actor
            candidate with

      | error diagnostic =>
          simp [
            routesOfEntries,
            hHead
          ] at hRoutes

      | ok headRoute =>

          cases hTail :
              routesOfEntries
                model
                actor
                remaining with

          | error diagnostic =>
              simp [
                routesOfEntries,
                hHead,
                hTail
              ] at hRoutes

          | ok tailRoutes =>

              rw [
                show
                    routesOfEntries
                        model
                        actor
                        (candidate :: remaining) =
                      .ok
                        (headRoute ::
                          tailRoutes) from by
                  simp [
                    routesOfEntries,
                    hHead,
                    hTail
                  ]
              ] at hRoutes

              obtain rfl :=
                Except.ok.inj
                  hRoutes.symm

              rcases List.mem_cons.mp hEntry with
                hHere | hThere

              · subst hHere

                exact
                  ⟨headRoute,
                   List.mem_cons_self,
                   hHead⟩

              · obtain ⟨route, hRouteMem, hRoute⟩ :=
                  IH
                    tailRoutes
                    hTail
                    entry
                    hThere

                exact
                  ⟨route,
                   List.mem_cons_of_mem
                     _
                     hRouteMem,
                   hRoute⟩

/--
An instance's emitted routes are routes of the whole table.

The block-to-table hop, by induction over the walked instance list. Needed because
`route_of_mem_outputPortEnv` produces a route of one instance's block while the connection list is
built from the whole table. The three per-instance equations are taken as hypotheses in the spelling
`routesOfInstances_cons_inv` produces them, so the head case matches them up by rewriting rather than
by re-resolving the class and the environment.
-/
private theorem mem_routesOfInstances_of_mem_block
    (model : DTR.GeneralModel) :
    ∀ (instances : List DTR.GeneralActorInstance)
      (routes : List GeneralRoute),
      routesOfInstances
          model
          instances =
        .ok routes →
      ∀ (actor : DTR.GeneralActorInstance),
        actor ∈ instances →
        ∀ (sendingClass : DTR.GeneralReactiveClass)
          (env : GeneralOutputPortEnv)
          (blockRoutes : List GeneralRoute),
          model.class? actor.className =
            some sendingClass →
          outputPortEnvOf
              model.classes
              sendingClass =
            .ok env →
          routesOfEntries
              model
              actor
              env =
            .ok blockRoutes →
          ∀ route ∈ blockRoutes,
            route ∈ routes := by

  intro instances
  induction instances with

  | nil =>
      intro routes _ actor hActor

      cases hActor

  | cons candidate rest IH =>
      intro routes hRoutes actor hActor sendingClass env blockRoutes hClass hEnv hBlock route hRoute

      obtain
          ⟨candidateClass,
           candidateEnv,
           headRoutes,
           tailRoutes,
           hCandidateClass,
           hCandidateEnv,
           hHead,
           hTail,
           hSplit⟩ :=
        routesOfInstances_cons_inv
          model
          candidate
          rest
          routes
          hRoutes

      subst hSplit

      rcases List.mem_cons.mp hActor with
        hHere | hThere

      · subst hHere

        -- The caller's class and environment are the same two resolutions the traversal made, so
        -- the caller's block is the traversal's head block.
        have hClassSame :
            candidateClass = sendingClass := by
          rw [
            hCandidateClass
          ] at hClass

          exact
            Option.some.inj
              hClass

        subst hClassSame

        have hEnvSame :
            candidateEnv = env := by
          rw [
            hCandidateEnv
          ] at hEnv

          exact
            Except.ok.inj
              hEnv

        subst hEnvSame

        rw [
          hBlock
        ] at hHead

        obtain rfl :=
          Except.ok.inj
            hHead

        exact
          List.mem_append.mpr
            (Or.inl hRoute)

      · exact
          List.mem_append.mpr
            (Or.inr
              (IH
                tailRoutes
                hTail
                actor
                hThere
                sendingClass
                env
                blockRoutes
                hClass
                hEnv
                hBlock
                route
                hRoute))

/--
A walked instance's own route block exists whenever the whole table does.

The positive form, proved from `routesOfInstances_cons_inv`'s successes rather than by propagating a
refusal through the traversal: the inversion already hands back each instance's block, so the head case
only has to identify the caller's class and environment resolutions with the inversion's.
-/
private theorem block_of_mem_routesOfInstances
    (model : DTR.GeneralModel) :
    ∀ (instances : List DTR.GeneralActorInstance)
      (routes : List GeneralRoute),
      routesOfInstances
          model
          instances =
        .ok routes →
      ∀ (actor : DTR.GeneralActorInstance),
        actor ∈ instances →
        ∀ (sendingClass : DTR.GeneralReactiveClass)
          (env : GeneralOutputPortEnv),
          model.class? actor.className =
            some sendingClass →
          outputPortEnvOf
              model.classes
              sendingClass =
            .ok env →
          ∃ blockRoutes : List GeneralRoute,
            routesOfEntries
                model
                actor
                env =
              .ok blockRoutes := by

  intro instances
  induction instances with

  | nil =>
      intro routes _ actor hActor

      cases hActor

  | cons candidate rest IH =>
      intro routes hRoutes actor hActor sendingClass env hClass hEnv

      obtain
          ⟨candidateClass,
           candidateEnv,
           headRoutes,
           tailRoutes,
           hCandidateClass,
           hCandidateEnv,
           hHead,
           hTail,
           _hSplit⟩ :=
        routesOfInstances_cons_inv
          model
          candidate
          rest
          routes
          hRoutes

      rcases List.mem_cons.mp hActor with
        hHere | hThere

      · subst hHere

        have hClassSame :
            candidateClass = sendingClass := by
          rw [
            hCandidateClass
          ] at hClass

          exact
            Option.some.inj
              hClass

        subst hClassSame

        have hEnvSame :
            candidateEnv = env := by
          rw [
            hCandidateEnv
          ] at hEnv

          exact
            Except.ok.inj
              hEnv

        subst hEnvSame

        exact ⟨headRoutes, hHead⟩

      · exact
          IH
            tailRoutes
            hTail
            actor
            hThere
            sendingClass
            env
            hClass
            hEnv

/--
The `PortName`-level source-endpoint `Nodup`, from the guard's string-level one.

`connectionFrom?` compares `PortName`s, while `declaredNames` decides `String`s, so the two
projections have to be bridged. The direction is the easy one — a `PortName` collision reflects into
a `String` collision because `PortName.value` is a function — which is exactly what
`nodup_map_of_reflecting` runs.
-/
private theorem sourceEndpoints_nodup_portName
    {connections : List LF.GeneralConnection}
    (hNodup :
      (List.map
        (fun connection =>
          (connection.sourceInstance, connection.sourcePort.value))
        connections).Nodup) :
    (List.map
      (fun connection =>
        (connection.sourceInstance, connection.sourcePort))
      connections).Nodup := by

  refine
    nodup_map_of_reflecting
      (fun connection =>
        (connection.sourceInstance, connection.sourcePort.value))
      (fun connection =>
        (connection.sourceInstance, connection.sourcePort))
      ?_
      connections
      hNodup

  intro first second hEqual

  obtain ⟨hInstance, hPort⟩ :=
    Prod.mk.inj hEqual

  rw [hInstance, hPort]

/--
**The headline theorem: `connectionFrom?` resolves a compiled send site to that site's own
connection.**

Given an accepted compilation and one of its instances' output-port entries — the entry
`compileGeneralStmt` looked up at a concrete external send site, so `entry.outputPort` is exactly the
port the emitted `.setPort` carries — the runtime lookup at `(actor.name, entry.outputPort)` returns
the connection emitted from *that* entry's route, and the route is exhibited.

Everything a routed-send forward transfer needs is recoverable from the returned route by
`generalConnectionOf`'s definitional fields: `targetInstance = route.receiverInstance`,
`targetPort = generalInputPortOfRoute route`, `delay = route.delay`, and the source endpoint is
`(actor.name, entry.outputPort)` by construction. Those five equations are returned rather than left
to the caller to unfold, because a caller that had to unfold `generalConnectionOf` would be reaching
past this theorem's interface for facts it already knows.

**This is not the converse of `Translation.exists_route_of_connectionFrom?`.** That theorem starts
from an arbitrary runtime connection and can only produce *some* route, because F48 makes more
impossible. This one starts from a concrete accepted send site whose route the compiler emitted, and
concludes about the lookup. No theorem in this module claims that an arbitrary connection determines
a send site.

The two `Nodup` hypotheses are the accepted-program facts: per-instance output-port distinctness
(from `outputPortEnv_outputPortNames_nodup`, i.e. from `declaredNames.Nodup`) and instance-name
distinctness (from `namesUniqueAndValid`). Neither is a new guard clause and neither is target-endpoint
uniqueness.
-/
theorem generalConnectionFrom?_siteFaithful
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List GeneralRoute}
    {actor : DTR.GeneralActorInstance}
    {sendingClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    {entry : GeneralOutputPortEntry}
    (hCompiled :
      compileGeneralModel model =
        .ok program)
    (hRoutes :
      routesOf model =
        .ok routes)
    (hActor :
      actor ∈ model.instances)
    (hClass :
      model.class? actor.className =
        some sendingClass)
    (hEnv :
      outputPortEnvOf
          model.classes
          sendingClass =
        .ok env)
    (hEntry :
      entry ∈ env)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              outputPortEnvOf
                  model.classes
                  candidateClass =
                .ok candidateEnv) →
          (List.map
            (fun candidateEntry =>
              candidateEntry.outputPort.value)
            candidateEnv).Nodup)
    (hNames :
      (List.map
        (fun candidate =>
          candidate.name)
        model.instances).Nodup) :
    ∃ route : GeneralRoute,
      generalRouteFor
          model
          actor
          entry =
        .ok route ∧
      route ∈ routes ∧
      LF.connectionFrom?
          program.connections
          actor.name
          entry.outputPort =
        some
          (generalConnectionOf
            route) ∧
      (generalConnectionOf route).sourceInstance = actor.name ∧
      (generalConnectionOf route).sourcePort = entry.outputPort ∧
      (generalConnectionOf route).targetInstance = route.receiverInstance ∧
      (generalConnectionOf route).targetPort =
        generalInputPortOfRoute route ∧
      (generalConnectionOf route).delay = route.delay := by

  -- The routing table walks the priority order, which is a permutation of the declared order.
  have hActorWalked :
      actor ∈
        priorityOrderedInstances
          model :=
    (mem_priorityOrderedInstances_iff
        model
        actor).mpr
      hActor

  obtain ⟨blockRoutes, hBlock⟩ :=
    block_of_mem_routesOfInstances
      model
      (priorityOrderedInstances
        model)
      routes
      (by
        unfold routesOf at hRoutes

        exact hRoutes)
      actor
      hActorWalked
      sendingClass
      env
      hClass
      hEnv

  obtain ⟨route, hRouteBlock, hRoute⟩ :=
    route_of_mem_outputPortEnv
      model
      actor
      env
      blockRoutes
      hBlock
      entry
      hEntry

  have hRouteTable :
      route ∈ routes := by
    unfold routesOf at hRoutes

    exact
      mem_routesOfInstances_of_mem_block
        model
        (priorityOrderedInstances
          model)
        routes
        hRoutes
        actor
        hActorWalked
        sendingClass
        env
        blockRoutes
        hClass
        hEnv
        hBlock
        route
        hRouteBlock

  obtain ⟨hSender, hPort⟩ :=
    generalRouteFor_sourceEndpoint
      hRoute

  obtain ⟨tableRoutes, hTableRoutes, hConnections⟩ :=
    compileGeneralModel_connections
      hCompiled

  rw [
    hRoutes
  ] at hTableRoutes

  obtain rfl :=
    Except.ok.inj
      hTableRoutes.symm

  have hConnectionMem :
      generalConnectionOf route ∈
        program.connections := by
    rw [
      hConnections
    ]

    unfold generalConnectionsOf

    exact
      List.mem_map_of_mem
        hRouteTable

  have hLookup :
      LF.connectionFrom?
          program.connections
          (generalConnectionOf route).sourceInstance
          (generalConnectionOf route).sourcePort =
        some
          (generalConnectionOf
            route) :=
    LF.connectionFrom?_eq_of_mem_of_sourceEndpoints_nodup
      program.connections
      (generalConnectionOf route)
      hConnectionMem
      (sourceEndpoints_nodup_portName
        (compileGeneralModel_sourceEndpoints_nodup
          hCompiled
          hEnvNodup
          hNames))

  refine
    ⟨route,
     hRoute,
     hRouteTable,
     ?_,
     ?_,
     ?_,
     rfl,
     rfl,
     rfl⟩

  · rw [
      show
          actor.name =
            (generalConnectionOf route).sourceInstance from by
        show
          actor.name = route.senderInstance

        rw [hSender],
      show
          entry.outputPort =
            (generalConnectionOf route).sourcePort from by
        show
          entry.outputPort = route.outputPort

        rw [hPort]
    ]

    exact hLookup

  · show
      route.senderInstance = actor.name

    exact hSender

  · show
      route.outputPort = entry.outputPort

    exact hPort

end Translation

end Relico
