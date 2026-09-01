/-
! # Forward transfer of the source's internal statement steps, general family

The prerequisite the forward instant-block wrapper turned out to need. A source instant block is
`Common.WeakSteps (DTR.GeneralStep model) DTR.GeneralLabel.isTau`, and `Common.WeakStep.visible`
carries a `TauSteps` prefix and suffix around every visible label, so a block is literally
`τ* · consume · τ* · … · τ*`. `Correctness.generalConsume_forward_weak_of_fireRepresentative`
crosses the consumes; **nothing crossed the τ segments**, and every other family in the tree has
that theorem (`concreteDetailed_statement_forward_weak` and its three siblings) while the general
family did not. This module is that theorem for the general family, plus the closure the wrapper
actually calls.

`DTR.GeneralStep` has five constructors. `take` is the visible `.consume` and `timeProgress` the
visible `.timeAdvance`; both already have their own machinery. The three τ rules are `assign`,
`trace` and `send`, and all three are covered here.

## Why the store premises are here, and why they are not new

Each theorem takes `DTR.GeneralStoreKeyUnique config` and `LF.GeneralStoreKeyUnique state`. The
reason is structural rather than incidental: `GeneralStateCorrespondence` pairs actors and reactors
by **membership**, while every step rule resolves its actor through **`Store.lookup`**. Going from
the correspondence's membership to a rule's lookup, and back again after the update, needs to know
the key occurs once — occurrence-exactly, which is what `Store.KeysUnique` says and what
`Store.lookup` cannot see (F74: a shadowed second binding agrees under every lookup). Those two
premises are exactly the landed reachable invariants of
`Relico/Correctness/GeneralStoreKeyUniqueness.lean`, so a caller holding reachability has them for
free, and the closure theorem at the end threads them through the induction rather than asking for
them again at each step.

This is also why no premise is weakened to lookup agreement: the post-state correspondence has to
rule out a *stale* binding at the updated key, and only occurrence uniqueness does that.

## Target semantics: raw steps, lifted late

Every target answer built here is a **raw** `LF.GeneralStep`, and the lift to
`LF.GeneralStepModulo` happens once, at the closure, through
`LF.GeneralStepModulo.tauSteps_of_raw`. No α representative is constructed and none is needed: the
four target rules involved (`assign`, `trace`, `schedule`, `setPort`) resolve their reactor by
lookup and consult no scheduler, so there is nothing for a queue reordering to help with. Keeping
the per-statement theorems raw is what lets the landed target invariants —
`LF.generalNoPastPending_of_step`, `LF.generalKindOrigin_of_step`,
`LF.generalStoreKeyUnique_of_step` and their `TauSteps` closures — apply to these steps directly,
with no bridge. **Store-key uniqueness is never transported through
`LF.generalStateAlphaEquiv`**, which would be unsound (its reactor conjuncts cannot see occurrence
multiplicity).

## F78, and where the event kind comes from

The `send` case does **not** map a message to a kind. The kind is read off the *compiled statement*:
`Translation.compileGeneralStmt_send_selfTarget` says a self-send compiles to a `.schedule` carrying
`generalActionNameAtSite …`, and the target rule then builds `.logicalAction` of that name;
`Translation.compileGeneralStmt_send_knownRebec_ok` says an external send compiles to a `.setPort`
at a resolved port, and the target rule reads the kind off the connection it follows. In both cases
the kind is whatever the compiled body and the runtime produced, never a function of the payload,
and the pending-agreement addition lemma below takes the event as given rather than constructing it
from a message. That is F78's discipline: the same DTR message from two sites yields two kinds, so
no such function exists.

## Self-sends

`DTR.GeneralStep.send` updates the sender and then the receiver, reading the receiver out of the
**already-updated** store, and the two may be the same actor. Nothing here adds a distinctness
premise: the double update is handled by the same two-step store reasoning whether or not the names
coincide, and the self-send case is where F56 once lost a message, so it is the case worth keeping
honest.
-/
import Relico.Correctness.GeneralCorrespondence
import Relico.Correctness.GeneralStoreKeyUniqueness

set_option autoImplicit false

namespace Relico

namespace Store

/-!
## Membership and lookup, under key uniqueness

Four small facts. `Relico/Correctness/GeneralWeakBisimulation.lean` has `private` copies of the
last two under different names (`store_mem_update_of_ne`, `store_mem_update_self`); they are not
de-privatised, per the house preference for duplicating a short lemma over widening an interface.
The first two are new: the tree had `Store.mem_of_lookup` but nothing in the other direction,
because until now nothing needed to turn a correspondence's membership into a step rule's lookup.
-/

/--
Under key uniqueness, a member binding is what the lookup returns.

The converse of `Store.mem_of_lookup`, and false without the hypothesis — a shadowed binding is a
member that no lookup ever returns. This is the bridge from `GeneralStateCorrespondence`'s
membership-shaped fields to a step rule's `Store.lookup` premise, and the reason every theorem in
this module carries the two key-uniqueness premises.
-/
theorem lookup_of_mem_of_keysUnique
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {key : Key}
    {value : Value} :
    ∀ (store : Store Key Value),
      Store.KeysUnique store →
      (key, value) ∈ store →
      Store.lookup store key =
        some value := by

  intro store
  induction store with

  | nil =>
      intro _ hMem

      cases hMem

  | cons head remaining IH =>
      intro hUnique hMem

      rcases head with
        ⟨candidate, currentValue⟩

      obtain ⟨hHeadNotMem, hTailUnique⟩ :=
        (Store.keysUnique_cons
            candidate
            currentValue
            remaining).mp
          hUnique

      rcases List.mem_cons.mp hMem with
        hHere | hThere

      · obtain ⟨hName, hValue⟩ :=
          Prod.mk.inj hHere

        subst hName

        subst hValue

        simp [Store.lookup]

      · have hCandidateNe :
            candidate ≠ key := by
          intro hEqual

          apply hHeadNotMem

          rw [hEqual]

          exact
            List.mem_map_of_mem
              hThere

        rw [
          Store.lookup,
          if_neg hCandidateNe
        ]

        exact
          IH
            hTailUnique
            hThere

/--
Under key uniqueness, a member binding at a resolved key carries the resolved value.

The fact that rules out a **stale** binding at the key a step updates. Without it the post-state
correspondence would owe a pairing for an entry the step never touched, which is the shadowed-binding
defect class in its exact form.
-/
theorem eq_of_mem_of_lookup_of_keysUnique
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {key : Key}
    {value resolved : Value}
    (hUnique :
      Store.KeysUnique store)
    (hMem :
      (key, value) ∈ store)
    (hLookup :
      Store.lookup store key =
        some resolved) :
    value = resolved := by

  rw [
    lookup_of_mem_of_keysUnique
      store
      hUnique
      hMem
  ] at hLookup

  exact
    Option.some.inj hLookup

/--
The updated binding is a member of the updated store.
-/
theorem mem_update_self
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key)
    (value : Value) :
    (key, value) ∈
      Store.update
        store
        key
        value := by

  induction store with

  | nil =>
      simp [Store.update]

  | cons head remaining IH =>
      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · subst hCandidate

        rw [
          Store.update,
          if_pos rfl
        ]

        exact List.mem_cons_self

      · rw [
          Store.update,
          if_neg hCandidate
        ]

        exact
          List.mem_cons_of_mem
            _
            IH

/--
A binding at another key survives an update.
-/
theorem mem_update_of_ne
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {name : Key}
    {value : Value}
    {key : Key}
    {newValue : Value}
    (hMem :
      (name, value) ∈ store)
    (hNe :
      name ≠ key) :
    (name, value) ∈
      Store.update
        store
        key
        newValue := by

  induction store with

  | nil =>
      cases hMem

  | cons head remaining IH =>
      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · subst hCandidate

        rw [
          Store.update,
          if_pos rfl
        ]

        rcases List.mem_cons.mp hMem with
          hHere | hThere

        · exact
            absurd
              (Prod.mk.inj hHere).1
              hNe

        · exact
            List.mem_cons_of_mem
              _
              hThere

      · rw [
          Store.update,
          if_neg hCandidate
        ]

        rcases List.mem_cons.mp hMem with
          hHere | hThere

        · rw [hHere]

          exact List.mem_cons_self

        · exact
            List.mem_cons_of_mem
              _
              (IH hThere)

/--
Under key uniqueness, two bindings at one key are the same binding.

The occurrence-exact "no shadowing" fact, in the form the update case analysis needs.
-/
theorem eq_of_mem_mem_of_keysUnique
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {key : Key}
    {left right : Value}
    (hUnique :
      Store.KeysUnique store)
    (hLeft :
      (key, left) ∈ store)
    (hRight :
      (key, right) ∈ store) :
    left = right :=
  eq_of_mem_of_lookup_of_keysUnique
    hUnique
    hLeft
    (lookup_of_mem_of_keysUnique
      store
      hUnique
      hRight)

/--
Every binding of an updated store is the new binding or an old one.

A local copy of the pair-level split that exists in `Relico/LF/GeneralKindOrigin.lean` as
`Store.mem_update`; that module is not on this one's import path (and importing the whole
kind-origin layer for a five-line list fact would be the wrong dependency), so the lemma is proved
again here. Duplicating a short lemma over widening or lengthening an import closure is the house
preference, and `update_cons_eq`/`update_cons_ne` already exist in three copies for the same reason.
-/
private theorem mem_update_split
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (key : Key)
    (value : Value) :
    ∀ (store : Store Key Value)
      (binding : Key × Value),
      binding ∈
        Store.update
          store
          key
          value →
      binding = (key, value) ∨
        binding ∈ store := by

  intro store
  induction store with

  | nil =>
      intro binding hMem

      simp [Store.update] at hMem

      exact Or.inl hMem

  | cons head remaining IH =>
      intro binding hMem

      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · subst hCandidate

        rw [
          Store.update,
          if_pos rfl
        ] at hMem

        rcases List.mem_cons.mp hMem with
          hHere | hThere

        · exact Or.inl hHere

        · exact
            Or.inr
              (List.mem_cons_of_mem
                _
                hThere)

      · rw [
          Store.update,
          if_neg hCandidate
        ] at hMem

        rcases List.mem_cons.mp hMem with
          hHere | hThere

        · subst hHere

          exact
            Or.inr
              List.mem_cons_self

        · rcases IH binding hThere with
            hNew | hOld

          · exact Or.inl hNew

          · exact
              Or.inr
                (List.mem_cons_of_mem
                  _
                  hOld)

/--
Under key uniqueness, a binding of an updated store is the new binding or an untouched old one.

Sharper than the plain split above, which cannot rule out the **stale** old binding at the updated
key. That sharpening is the whole reason the theorems below carry key-uniqueness premises: without
it the post-state correspondence would owe a pairing for an entry the step replaced.
-/
theorem mem_update_cases_of_keysUnique
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {key : Key}
    {newValue : Value}
    {name : Key}
    {value : Value}
    (hUnique :
      Store.KeysUnique store)
    (hMem :
      (name, value) ∈
        Store.update
          store
          key
          newValue) :
    (name = key ∧ value = newValue) ∨
      ((name, value) ∈ store ∧ name ≠ key) := by

  by_cases hName :
      name = key

  · subst hName

    refine
      Or.inl
        ⟨rfl, ?_⟩

    exact
      eq_of_mem_mem_of_keysUnique
        (Store.keysUnique_update
          hUnique)
        hMem
        (mem_update_self
          store
          name
          newValue)

  · rcases
        mem_update_split
          key
          newValue
          store
          (name, value)
          hMem with
      hNew | hOld

    · exact
        absurd
          (Prod.mk.inj hNew).1
          hName

    · exact
        Or.inr
          ⟨hOld, hName⟩

/--
Two updates at one key collapse to the second.

The self-send collapse. `DTR.GeneralStep.send` writes the sender and then the receiver, and when an
actor sends to itself both writes land on one key — so the post-state is the second write alone. The
rule reads the receiver out of the already-updated store precisely so that this is the *advanced*
record rather than a stale one (F56 lost a message there once), and this lemma is what lets the
self-send proof use the single-update correspondence helper without a distinctness premise.
-/
theorem update_update_same
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (key : Key)
    (first second : Value) :
    ∀ (store : Store Key Value),
      Store.update
          (Store.update
            store
            key
            first)
          key
          second =
        Store.update
          store
          key
          second := by

  intro store
  induction store with

  | nil =>
      simp [Store.update]

  | cons head remaining IH =>
      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · subst hCandidate

        simp [Store.update]

      · rw [
          Store.update,
          if_neg hCandidate,
          Store.update,
          if_neg hCandidate,
          Store.update,
          if_neg hCandidate,
          IH
        ]

end Store

namespace Correctness

/-!
## The paired store update

Both τ rules that touch a single actor — `assign` and `trace` — change the source and target stores
in the same shape: one entry replaced at one key, the pending queue untouched. This lemma is that
shape, so neither statement theorem re-derives the three correspondence fields.

It is stated on projections rather than on the rules' literal post-states, following
`generalCorrespondence_advance`'s reason for the same choice: an inversion-driven caller holds
equations rather than definitional identities.
-/

/--
Replacing one corresponding actor/reactor pair preserves the state correspondence.

The two key-uniqueness premises are what make the `reactorOfActor` and `actorOfReactor` directions
go through: a member of the updated store is either the new entry or an old entry at a *different*
key, and only occurrence uniqueness rules out the stale third case.

`pendingTargeted` survives because the queue is unchanged and the update neither adds nor removes a
key: an event targeting the updated actor is answered by the new entry, and one targeting any other
actor by that actor's surviving entry.
-/
theorem generalCorrespondence_updatePair
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (name : ActorName)
    (env : Translation.GeneralOutputPortEnv)
    (hEnv :
      outputPortEnvOfActorName model name =
        some env)
    (actor' : DTR.GeneralActorRuntime)
    (reactor' : LF.GeneralReactorRuntime)
    (hPair :
      GeneralActorCorresponds
        env
        name
        actor'
        reactor'
        state.pending) :
    GeneralStateCorrespondence
      model
      {
        now := config.now

        actors :=
          Store.update
            config.actors
            name
            actor'
      }
      {
        currentTag := state.currentTag

        reactors :=
          Store.update
            state.reactors
            name
            reactor'

        pending := state.pending
      } := by

  refine
    {
      logicalTime :=
        hCorrespondence.logicalTime
      reactorOfActor := ?_
      actorOfReactor := ?_
      pendingTargeted := ?_
    }

  · intro other actor hMem

    dsimp only at hMem ⊢

    rcases
        Store.mem_update_cases_of_keysUnique
          hUniqueS
          hMem with
      ⟨hName, hValue⟩ | ⟨hOld, hNe⟩

    · subst hName

      subst hValue

      exact
        ⟨env,
         reactor',
         hEnv,
         Store.mem_update_self
           state.reactors
           other
           reactor',
         hPair⟩

    · obtain ⟨envReactor, reactor, hEnvReactor, hReactorMem, hCorresponds⟩ :=
        hCorrespondence.reactorOfActor
          other
          actor
          hOld

      exact
        ⟨envReactor,
         reactor,
         hEnvReactor,
         Store.mem_update_of_ne
           hReactorMem
           hNe,
         hCorresponds⟩

  · intro other reactor hMem

    dsimp only at hMem ⊢

    rcases
        Store.mem_update_cases_of_keysUnique
          hUniqueT
          hMem with
      ⟨hName, hValue⟩ | ⟨hOld, hNe⟩

    · subst hName

      subst hValue

      exact
        ⟨env,
         actor',
         hEnv,
         Store.mem_update_self
           config.actors
           other
           actor',
         hPair⟩

    · obtain ⟨envActor, actor, hEnvActor, hActorMem, hCorresponds⟩ :=
        hCorrespondence.actorOfReactor
          other
          reactor
          hOld

      exact
        ⟨envActor,
         actor,
         hEnvActor,
         Store.mem_update_of_ne
           hActorMem
           hNe,
         hCorresponds⟩

  · intro event hMem

    dsimp only at hMem ⊢

    obtain ⟨actor, hActorMem⟩ :=
      hCorrespondence.pendingTargeted
        event
        hMem

    by_cases hTarget :
        event.target = name

    · subst hTarget

      exact
        ⟨actor',
         Store.mem_update_self
           config.actors
           event.target
           actor'⟩

    · exact
        ⟨actor,
         Store.mem_update_of_ne
           hActorMem
           hTarget⟩

/-!
## Continuation head inversions

`generalContinuationCompiles_trace_tail` takes the target's head shape as a hypothesis, because its
caller (`generalActorCorresponds_trace_tail`) already had it. A *forward* transfer does not: it holds
the source's head and has to **discover** the target's. These two lemmas are that discovery, and they
are the only continuation lemmas this milestone adds.

Both go through `Translation.compileGeneralBody_cons_ok_inversion` plus the statement's own
compilation equation, which is unconditional in each case (`compileGeneralStmt_trace`,
`compileGeneralStmt_assign` — neither can refuse).
-/

/--
A compiled body whose source head is a trace has a trace head, and its tail compiles.
-/
theorem generalContinuationCompiles_trace_head
    {env : Translation.GeneralOutputPortEnv}
    {tag : String}
    {sourceRemaining : DTR.GeneralBody}
    {target : LF.GeneralBody}
    (hCompiles :
      GeneralContinuationCompiles
        env
        (.trace tag :: sourceRemaining)
        target) :
    ∃ targetRemaining : LF.GeneralBody,
      target =
          LF.GeneralStmt.trace tag ::
            targetRemaining ∧
        GeneralContinuationCompiles
          env
          sourceRemaining
          targetRemaining := by

  obtain ⟨context, index, hCompiled, hSites⟩ :=
    hCompiles

  obtain
      ⟨compiledStatement,
       compiledRemaining,
       hStatement,
       hRemaining,
       hShape⟩ :=
    Translation.compileGeneralBody_cons_ok_inversion
      hCompiled

  rw [
    Translation.compileGeneralStmt_trace
  ] at hStatement

  injection hStatement with hStatement

  subst hStatement

  exact
    ⟨compiledRemaining,
     hShape,
     ⟨context,
      index + 1,
      hRemaining,
      by
        intro k rebec message arguments delay rest hDrop entry hEntry

        refine
          hSites
            (k + 1)
            rebec
            message
            arguments
            delay
            rest
            ?_
            entry
            ?_

        · rw [
            List.drop_succ_cons
          ]

          exact hDrop

        · rw [
            show
                index + (k + 1) =
                  index + 1 + k from by
              omega
          ]

          exact hEntry⟩⟩

/--
A compiled body whose source head is an assignment has the compiled assignment as its head, and its
tail compiles.

The target head is pinned to `Translation.compileGeneralExpr` of the source expression, which is
exactly what the assign transfer needs in order to evaluate the target side by
`compileGeneralExpr_preserves_evaluation`.
-/
theorem generalContinuationCompiles_assign_head
    {env : Translation.GeneralOutputPortEnv}
    {target : VarName}
    {expression : DTR.GeneralExpr}
    {sourceRemaining : DTR.GeneralBody}
    {targetBody : LF.GeneralBody}
    (hCompiles :
      GeneralContinuationCompiles
        env
        (.assign target expression :: sourceRemaining)
        targetBody) :
    ∃ targetRemaining : LF.GeneralBody,
      targetBody =
          LF.GeneralStmt.assign
              target
              (Translation.compileGeneralExpr
                expression) ::
            targetRemaining ∧
        GeneralContinuationCompiles
          env
          sourceRemaining
          targetRemaining := by

  obtain ⟨context, index, hCompiled, hSites⟩ :=
    hCompiles

  obtain
      ⟨compiledStatement,
       compiledRemaining,
       hStatement,
       hRemaining,
       hShape⟩ :=
    Translation.compileGeneralBody_cons_ok_inversion
      hCompiled

  rw [
    Translation.compileGeneralStmt_assign
  ] at hStatement

  injection hStatement with hStatement

  subst hStatement

  exact
    ⟨compiledRemaining,
     hShape,
     ⟨context,
      index + 1,
      hRemaining,
      by
        intro k rebec message arguments delay rest hDrop entry hEntry

        refine
          hSites
            (k + 1)
            rebec
            message
            arguments
            delay
            rest
            ?_
            entry
            ?_

        · rw [
            List.drop_succ_cons
          ]

          exact hDrop

        · rw [
            show
                index + (k + 1) =
                  index + 1 + k from by
              omega
          ]

          exact hEntry⟩⟩

/-!
## Trace

The cheapest case, and the one that fixes the proof pattern the other two follow: read the actor's
reactor out of the correspondence, turn its membership into the lookup the target rule wants, discover
the target's head by inversion, fire the matching target rule, and rebuild the correspondence with
`generalCorrespondence_updatePair`.
-/

/--
A source `trace` step is answered by a target `trace` step, preserving the correspondence.

Nothing observable moves on either side: the source keeps `actor.state` whole and the target keeps
`reactor.valuation` and `state.pending`, so the valuation and message fields of the actor
correspondence transfer unchanged and only the continuation advances.
-/
theorem generalTrace_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {actorName : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {tag : String}
    {remaining : DTR.GeneralBody}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hActor :
      Store.lookup config.actors actorName =
        some actor)
    (hBody :
      actor.activeBody =
        DTR.GeneralStmt.trace tag :: remaining) :
    ∃ state' : LF.GeneralRuntimeState,
      LF.GeneralStep
          program
          state
          LF.GeneralLabel.tau
          state' ∧
        GeneralStateCorrespondence
          model
          {
            now := config.now

            actors :=
              Store.update
                config.actors
                actorName
                {
                  state := actor.state
                  activeBody := remaining
                }
          }
          state' := by

  obtain ⟨env, reactor, hEnv, hReactorMem, hPair⟩ :=
    hCorrespondence.reactorOfActor
      actorName
      actor
      (Store.mem_of_lookup
        config.actors
        actorName
        actor
        hActor)

  obtain ⟨targetRemaining, hTargetBody, hTailCompiles⟩ :=
    generalContinuationCompiles_trace_head
      (by
        rw [← hBody]

        exact hPair.continuation)

  refine
    ⟨_,
     LF.GeneralStep.trace
       (Store.lookup_of_mem_of_keysUnique
         state.reactors
         hUniqueT
         hReactorMem)
       hTargetBody,
     ?_⟩

  exact
    generalCorrespondence_updatePair
      hCorrespondence
      hUniqueS
      hUniqueT
      actorName
      env
      hEnv
      {
        state := actor.state
        activeBody := remaining
      }
      {
        valuation := reactor.valuation
        activeBody := targetRemaining
      }
      {
        valuation := hPair.valuation
        messages := hPair.messages
        continuation := hTailCompiles
      }

/-!
## The weak lift, at the statement level

`generalTrace_forward` concludes a **raw** `LF.GeneralStep`. The architecture the paper states is a *weak*
bisimulation over the light within-tag quotient, so a consumer working at that level needs the same fact as a
`Common.WeakStep` of `LF.GeneralStepModulo`. This section supplies it for `trace`.

**What this adds over routing through `generalTauSteps_forward`, which is the question worth answering.**
The closure theorem already covers all three τ statement forms, so a caller *could* reach a weak step through
it — but only by supplying four accepted-program premises (`hCompiled`, `hRoutes`, `hEnvNodup`, `hNames`) that
a `trace` step does not need. `generalTrace_forward` needs **none** of them: tracing consults no routing
table, no output-port environment and no instance list. So the lift below is strictly premise-lighter than the
closure route, and that is its whole justification. A caller holding only a correspondence and a body can use
it; a caller going through the closure cannot.

**The direction of the quotient lift is the permitted one.** `LF.GeneralStepModulo.of_raw` embeds a raw step
into the quotient by reflexivity on both ends. Nothing here inverts the quotient, and no modulo-to-raw lemma
is added or needed.

The label is `LF.GeneralLabel.tau` on both sides. On the source side that is forced rather than chosen: the
source has no `trace` label at all — `DTR.GeneralLabel` has exactly `tau`, `timeAdvance` and `consume` — so a
`trace` statement step is internal by construction, and the statement itself is pinned by `hBody` rather than
by the label.
-/

/--
A source `trace` step is answered by a **weak** target step of the quotient system, preserving the
correspondence.

The weak form of `generalTrace_forward`, and the shape a weak-bisimulation consumer reads. Same premises as
the raw version — in particular **no** accepted-program premises, since tracing consults no routing
machinery — so this is usable where the τ closure route is not.

The τ padding is **empty at both ends**, and that is the content rather than a shortcut: `TauSteps.refl` on
each side says the source's trace is matched by *exactly one* target step with no administrative traffic
around it, which is stronger than a padded statement. Genuine padding is owed only where P24 measured a
divergence, and `trace` is not such a place — the compiled `LF.GeneralStmt.trace` is one statement for the
source's one statement.

Built through `Common.WeakStep.tau` and `Common.TauSteps.single` rather than through
`Common.WeakStep.of_step`, deliberately, for the reason `generalTimeAdvance_forward_weak`'s docstring records
about its own construction: `of_step` splits on `isTau label` with `classical` `by_cases` and so elaborates
whatever the τ classification says, which would make the statement invariant under the very classification
that decides whether a trace is observable. `LF.GeneralLabel.isTau_tau` is discharged explicitly instead, so
a τ set that stopped containing `tau` would fail here.
-/
theorem generalTrace_forward_weak
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {actorName : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {tag : String}
    {remaining : DTR.GeneralBody}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hActor :
      Store.lookup config.actors actorName =
        some actor)
    (hBody :
      actor.activeBody =
        DTR.GeneralStmt.trace tag :: remaining) :
    ∃ state' : LF.GeneralRuntimeState,
      Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          LF.GeneralLabel.tau
          state' ∧
        GeneralStateCorrespondence
          model
          {
            now := config.now

            actors :=
              Store.update
                config.actors
                actorName
                {
                  state := actor.state
                  activeBody := remaining
                }
          }
          state' := by

  obtain ⟨state', hRawStep, hNextCorrespondence⟩ :=
    generalTrace_forward
      hCorrespondence
      hUniqueS
      hUniqueT
      hActor
      hBody

  exact
    ⟨state',
     Common.WeakStep.tau
       LF.GeneralLabel.isTau_tau
       (Common.TauSteps.single
         (LF.GeneralStepModulo.of_raw
           hRawStep)
         LF.GeneralLabel.isTau_tau),
     hNextCorrespondence⟩

/-!
## Assign

The same pattern, plus the evaluation half. The target's expression is
`Translation.compileGeneralExpr` of the source's — pinned by the head inversion — and
`compileGeneralExpr_preserves_evaluation` at the actor correspondence's own `valuation` field turns
the source's successful evaluation into the target's, with the value being the compiled source value.
`generalValuationAgrees_update` then re-establishes the valuation field across the paired update, at
exactly the shape it was written for.
-/

/--
A source `assign` step is answered by a target `assign` step, preserving the correspondence.

The target's value is not chosen: it is `Translation.compileGeneralValue` of the source's, forced by
`compileGeneralExpr_preserves_evaluation`. That is what makes `generalValuationAgrees_update`
applicable without a side condition — its statement is precisely a source update paired with a target
update at the same name carrying the compiled value.

The `messages` field transfers unchanged (the bag and the queue are both untouched) and the
continuation advances by the head inversion's tail.
-/
theorem generalAssign_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {actorName : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {target : VarName}
    {expression : DTR.GeneralExpr}
    {remaining : DTR.GeneralBody}
    {value : DTR.GeneralValue}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hActor :
      Store.lookup config.actors actorName =
        some actor)
    (hBody :
      actor.activeBody =
        DTR.GeneralStmt.assign target expression :: remaining)
    (hEvaluate :
      DTR.GeneralExpr.evaluate
          actor.state.valuation
          expression =
        some value) :
    ∃ state' : LF.GeneralRuntimeState,
      LF.GeneralStep
          program
          state
          LF.GeneralLabel.tau
          state' ∧
        GeneralStateCorrespondence
          model
          {
            now := config.now

            actors :=
              Store.update
                config.actors
                actorName
                {
                  state :=
                    {
                      valuation :=
                        Store.update
                          actor.state.valuation
                          target
                          value

                      bag := actor.state.bag
                    }

                  activeBody := remaining
                }
          }
          state' := by

  obtain ⟨env, reactor, hEnv, hReactorMem, hPair⟩ :=
    hCorrespondence.reactorOfActor
      actorName
      actor
      (Store.mem_of_lookup
        config.actors
        actorName
        actor
        hActor)

  obtain ⟨targetRemaining, hTargetBody, hTailCompiles⟩ :=
    generalContinuationCompiles_assign_head
      (by
        rw [← hBody]

        exact hPair.continuation)

  have hTargetEvaluate :
      LF.GeneralExpr.evaluate
          reactor.valuation
          (Translation.compileGeneralExpr
            expression) =
        some
          (Translation.compileGeneralValue
            value) := by
    rw [
      compileGeneralExpr_preserves_evaluation
        hPair.valuation
        expression,
      hEvaluate
    ]

    rfl

  refine
    ⟨_,
     LF.GeneralStep.assign
       (Store.lookup_of_mem_of_keysUnique
         state.reactors
         hUniqueT
         hReactorMem)
       hTargetBody
       hTargetEvaluate,
     ?_⟩

  exact
    generalCorrespondence_updatePair
      hCorrespondence
      hUniqueS
      hUniqueT
      actorName
      env
      hEnv
      {
        state :=
          {
            valuation :=
              Store.update
                actor.state.valuation
                target
                value

            bag := actor.state.bag
          }

        activeBody := remaining
      }
      {
        valuation :=
          Store.update
            reactor.valuation
            target
            (Translation.compileGeneralValue
              value)

        activeBody := targetRemaining
      }
      {
        valuation :=
          generalValuationAgrees_update
            actor.state.valuation
            reactor.valuation
            target
            value
            hPair.valuation

        messages := hPair.messages
        continuation := hTailCompiles
      }

/-!
## Pending agreement, in the addition direction

`GeneralPendingAgrees` had six lemmas and every one of them **removed** or **transported**:
`_empty`, `_event_of_message`, `_message_of_event`, `_removeOne`, `_of_queue_perm`,
`_of_queue_drop`. A source `send` appends a message to the receiver's bag while the target appends an
event to the queue, so the send case needs the direction nothing covered. These two lemmas are it.

Occurrence-safe by construction. The witness pair list gains exactly one pair, so multiplicity is
preserved on the nose: appending the same message twice demands two events, and two identical
messages remain two pairs. No `Nodup` on messages or events is assumed anywhere, and neither lemma
constructs an event from a message — the event is taken as given, with `GeneralConsumeMatch` as the
only link. That is F78's discipline: the kind is a property of the event the target actually
enqueued, and there is no function from a message to a kind.
-/

/--
Appending a matched message/event pair preserves one actor's pending agreement.

The pair list gains `(message, event)` at the end, so both permutation conjuncts extend by
`List.map_append`, and the queue conjunct works because the appended event passes this actor's filter
— which is exactly `GeneralConsumeMatch`'s target conjunct.
-/
theorem generalPendingAgrees_append_matched
    {name : ActorName}
    {bag : DTR.GeneralMessageBag}
    {pending : LF.GeneralEventQueue}
    {message : DTR.GeneralMessage}
    {event : LF.GeneralPendingEvent}
    (hAgrees :
      GeneralPendingAgrees
        name
        bag
        pending)
    (hMatch :
      GeneralConsumeMatch
        name
        message
        event) :
    GeneralPendingAgrees
      name
      (bag ++ [message])
      (pending ++ [event]) := by

  obtain ⟨pairs, hPairsMatch, hBagPerm, hQueuePerm⟩ :=
    hAgrees

  refine
    ⟨pairs ++ [(message, event)],
     ?_,
     ?_,
     ?_⟩

  · intro pair hPair

    rcases List.mem_append.mp hPair with
      hOld | hNew

    · exact
        hPairsMatch
          pair
          hOld

    · rw [
        List.mem_singleton.mp hNew
      ]

      exact hMatch

  · rw [
      List.map_append
    ]

    exact
      hBagPerm.append_right
        _

  · have hFilter :
        (pending ++ [event]).filter
            (fun candidate =>
              decide (candidate.target = name)) =
          pending.filter
              (fun candidate =>
                decide (candidate.target = name)) ++
            [event] := by
      rw [
        List.filter_append,
        List.filter_cons_of_pos
          (p := fun candidate =>
            decide (candidate.target = name))
          (a := event)
          (by
            rw [hMatch.1]

            exact decide_eq_true rfl)
      ]

      rfl

    rw [
      hFilter,
      List.map_append
    ]

    exact
      hQueuePerm.append_right
        _

/--
Appending an event aimed elsewhere leaves a bystander actor's pending agreement intact.

The queue conjunct filters by target, so an event for another actor is invisible to it — the same
argument `generalPendingAgrees_of_queue_drop` makes for removal, run forwards. This is the half of one
send that belongs to every actor other than the receiver.
-/
theorem generalPendingAgrees_append_other
    {name : ActorName}
    {bag : DTR.GeneralMessageBag}
    {pending : LF.GeneralEventQueue}
    {event : LF.GeneralPendingEvent}
    (hAgrees :
      GeneralPendingAgrees
        name
        bag
        pending)
    (hOther :
      event.target ≠ name) :
    GeneralPendingAgrees
      name
      bag
      (pending ++ [event]) := by

  obtain ⟨pairs, hPairsMatch, hBagPerm, hQueuePerm⟩ :=
    hAgrees

  refine
    ⟨pairs,
     hPairsMatch,
     hBagPerm,
     ?_⟩

  have hFilter :
      (pending ++ [event]).filter
          (fun candidate =>
            decide (candidate.target = name)) =
        pending.filter
          (fun candidate =>
            decide (candidate.target = name)) := by
    rw [
      List.filter_append,
      List.filter_cons_of_neg
        (p := fun candidate =>
          decide (candidate.target = name))
        (a := event)
        (by
          intro hEqual

          exact
            hOther
              (decide_eq_true_iff.mp
                hEqual))
    ]

    simp

  rw [hFilter]

  exact hQueuePerm

/-!
## Delivery: appending one matched message/event pair

The per-state form of the two append lemmas. A source `send` writes the receiver's bag and the target
appends to the global queue, so **every** actor's `messages` conjunct is touched — the receiver's by
`generalPendingAgrees_append_matched`, everyone else's by `..._append_other`. That is why delivery
needs its own state-level helper rather than reusing `generalCorrespondence_updatePair`: the queue is
not fixed.

`pendingTargeted` needs the new event's target to name a declared actor, and the caller has that:
the source rule resolved a receiver, and the receiver is in the store the delivery writes.
-/

/--
Appending a matched pair at one receiver preserves the state correspondence.

The receiver's own pairing gains the new occurrence; every other actor is a bystander whose queue
projection is unchanged, because the filter is by target. Multiplicity is exact — one message in, one
event in, one pair in — so two identical sends produce two pairs and demand two events.

`hMatch` is stated at the *receiver's* name, and the event's `target` field is what ties it there;
nothing infers the kind from the message, and the kind is not mentioned at all. That is F78's
discipline: the event is whatever the target rule enqueued.
-/
theorem generalCorrespondence_deliver
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (receiverName : ActorName)
    (env : Translation.GeneralOutputPortEnv)
    (hEnv :
      outputPortEnvOfActorName model receiverName =
        some env)
    (receiver : DTR.GeneralActorRuntime)
    (targetReceiver : LF.GeneralReactorRuntime)
    (message : DTR.GeneralMessage)
    (event : LF.GeneralPendingEvent)
    (hReceiverMem :
      (receiverName, receiver) ∈ config.actors)
    (hTargetReceiverMem :
      (receiverName, targetReceiver) ∈ state.reactors)
    (hReceiverPair :
      GeneralActorCorresponds
        env
        receiverName
        receiver
        targetReceiver
        state.pending)
    (hMatch :
      GeneralConsumeMatch
        receiverName
        message
        event)
    (hEventTarget :
      event.target = receiverName) :
    GeneralStateCorrespondence
      model
      {
        now := config.now

        actors :=
          Store.update
            config.actors
            receiverName
            {
              state :=
                {
                  valuation := receiver.state.valuation

                  bag :=
                    receiver.state.bag ++ [message]
                }

              activeBody := receiver.activeBody
            }
      }
      {
        currentTag := state.currentTag

        reactors := state.reactors

        pending :=
          state.pending ++ [event]
      } := by

  refine
    {
      logicalTime :=
        hCorrespondence.logicalTime
      reactorOfActor := ?_
      actorOfReactor := ?_
      pendingTargeted := ?_
    }

  · intro other actor hMem

    dsimp only at hMem ⊢

    rcases
        Store.mem_update_cases_of_keysUnique
          hUniqueS
          hMem with
      ⟨hName, hValue⟩ | ⟨hOld, hNe⟩

    · subst hName

      subst hValue

      exact
        ⟨env,
         targetReceiver,
         hEnv,
         hTargetReceiverMem,
         {
           valuation := hReceiverPair.valuation

           messages :=
             generalPendingAgrees_append_matched
               hReceiverPair.messages
               hMatch

           continuation := hReceiverPair.continuation
         }⟩

    · obtain ⟨envReactor, reactor, hEnvReactor, hReactorMem, hPair⟩ :=
        hCorrespondence.reactorOfActor
          other
          actor
          hOld

      refine
        ⟨envReactor,
         reactor,
         hEnvReactor,
         hReactorMem,
         {
           valuation := hPair.valuation

           messages :=
             generalPendingAgrees_append_other
               hPair.messages
               ?_

           continuation := hPair.continuation
         }⟩

      rw [hEventTarget]

      exact Ne.symm hNe

  · intro other reactor hMem

    dsimp only at hMem ⊢

    obtain ⟨envActor, actor, hEnvActor, hActorMem, hPair⟩ :=
      hCorrespondence.actorOfReactor
        other
        reactor
        hMem

    by_cases hOther :
        other = receiverName

    · subst hOther

      -- The reactor at the receiver's name is the receiver's, so the pairing to extend is the
      -- receiver's own. Store uniqueness is what rules out a second, stale entry here.
      obtain rfl :=
        Store.eq_of_mem_mem_of_keysUnique
          hUniqueT
          hMem
          hTargetReceiverMem

      exact
        ⟨env,
         {
           state :=
             {
               valuation := receiver.state.valuation

               bag :=
                 receiver.state.bag ++ [message]
             }

           activeBody := receiver.activeBody
         },
         hEnv,
         Store.mem_update_self
           config.actors
           other
           _,
         {
           valuation := hReceiverPair.valuation

           messages :=
             generalPendingAgrees_append_matched
               hReceiverPair.messages
               hMatch

           continuation := hReceiverPair.continuation
         }⟩

    · refine
        ⟨envActor,
         actor,
         hEnvActor,
         Store.mem_update_of_ne
           hActorMem
           hOther,
         {
           valuation := hPair.valuation

           messages :=
             generalPendingAgrees_append_other
               hPair.messages
               ?_

           continuation := hPair.continuation
         }⟩

      rw [hEventTarget]

      exact Ne.symm hOther

  · intro candidate hMem

    dsimp only at hMem ⊢

    rcases List.mem_append.mp hMem with
      hOld | hNew

    · obtain ⟨actor, hActorMem⟩ :=
        hCorrespondence.pendingTargeted
          candidate
          hOld

      by_cases hTarget :
          candidate.target = receiverName

      · rw [hTarget]

        exact
          ⟨_,
           Store.mem_update_self
             config.actors
             receiverName
             _⟩

      · exact
          ⟨actor,
           Store.mem_update_of_ne
             hActorMem
             hTarget⟩

    · obtain rfl :=
        List.mem_singleton.mp hNew

      rw [hEventTarget]

      exact
        ⟨_,
         Store.mem_update_self
           config.actors
           receiverName
           _⟩

/-!
## The send-shaped correspondence step

`DTR.GeneralStep.send` writes **two** source keys — sender then receiver, the receiver read out of
the already-updated store — while the target writes one reactor and appends one event. Neither
`generalCorrespondence_updatePair` nor `generalCorrespondence_deliver` fits alone, so this helper is
their combination at exactly the send rules' post-state shape.

**No `senderName ≠ receiverName` premise, and none would be sound.** A `.selfTarget` send has them
equal by construction, and a `.knownRebec` send may too, since `ActorTopology.resolve` can bind a
known rebec to the sending instance. The helper therefore takes the receiver's post-state target
reactor as an argument, which the caller instantiates with the *updated sender* reactor when the names
coincide and with the untouched receiver reactor when they do not. One theorem serves both halves and
both coincidence cases, instead of four theorems or a false distinctness hypothesis.
-/

/--
The correspondence step shared by both send halves.

Three source cases, from two applications of `Store.mem_update_cases_of_keysUnique`: the receiver's
new record, the sender's new record (reachable only when the names differ), and an untouched old
record. Each is answered by one of the three pair hypotheses.

`hSenderPost` and `hReceiverPost` are stated against `pending ++ [event]`, after the append, so the
caller performs the one `generalPendingAgrees_append_matched` / `..._append_other` step where it knows
which side of the delivery it is on. Everything else here is store bookkeeping.
-/
theorem generalCorrespondence_send
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (senderName receiverName : ActorName)
    (envSender envReceiver : Translation.GeneralOutputPortEnv)
    (hEnvSender :
      outputPortEnvOfActorName model senderName =
        some envSender)
    (hEnvReceiver :
      outputPortEnvOfActorName model receiverName =
        some envReceiver)
    (senderPost receiverPost : DTR.GeneralActorRuntime)
    (targetSender targetReceiver : LF.GeneralReactorRuntime)
    (event : LF.GeneralPendingEvent)
    (hTargetSenderMem :
      (senderName, targetSender) ∈
        Store.update
          state.reactors
          senderName
          targetSender)
    (hTargetReceiverMem :
      (receiverName, targetReceiver) ∈
        Store.update
          state.reactors
          senderName
          targetSender)
    (hSenderPost :
      senderName ≠ receiverName →
      GeneralActorCorresponds
        envSender
        senderName
        senderPost
        targetSender
        (state.pending ++ [event]))
    (hReceiverPost :
      GeneralActorCorresponds
        envReceiver
        receiverName
        receiverPost
        targetReceiver
        (state.pending ++ [event]))
    (hOther :
      ∀ (name : ActorName)
        (envOther : Translation.GeneralOutputPortEnv)
        (actor : DTR.GeneralActorRuntime)
        (reactor : LF.GeneralReactorRuntime),
        name ≠ senderName →
        name ≠ receiverName →
        GeneralActorCorresponds
          envOther
          name
          actor
          reactor
          state.pending →
        GeneralActorCorresponds
          envOther
          name
          actor
          reactor
          (state.pending ++ [event]))
    (hEventTarget :
      ∃ actor : DTR.GeneralActorRuntime,
        (event.target, actor) ∈
          Store.update
            (Store.update
              config.actors
              senderName
              senderPost)
            receiverName
            receiverPost) :
    GeneralStateCorrespondence
      model
      {
        now := config.now

        actors :=
          Store.update
            (Store.update
              config.actors
              senderName
              senderPost)
            receiverName
            receiverPost
      }
      {
        currentTag := state.currentTag

        reactors :=
          Store.update
            state.reactors
            senderName
            targetSender

        pending :=
          state.pending ++ [event]
      } := by

  have hUniqueSenderStore :
      Store.KeysUnique
        (Store.update
          config.actors
          senderName
          senderPost) :=
    Store.keysUnique_update
      hUniqueS

  refine
    {
      logicalTime :=
        hCorrespondence.logicalTime
      reactorOfActor := ?_
      actorOfReactor := ?_
      pendingTargeted := ?_
    }

  · intro name actor hMem

    dsimp only at hMem ⊢

    rcases
        Store.mem_update_cases_of_keysUnique
          hUniqueSenderStore
          hMem with
      ⟨hName, hValue⟩ | ⟨hMidMem, hNotReceiver⟩

    · subst hName

      subst hValue

      exact
        ⟨envReceiver,
         targetReceiver,
         hEnvReceiver,
         hTargetReceiverMem,
         hReceiverPost⟩

    · rcases
          Store.mem_update_cases_of_keysUnique
            hUniqueS
            hMidMem with
        ⟨hName, hValue⟩ | ⟨hOldMem, hNotSender⟩

      · subst hName

        subst hValue

        exact
          ⟨envSender,
           targetSender,
           hEnvSender,
           hTargetSenderMem,
           hSenderPost hNotReceiver⟩

      · obtain ⟨envReactor, reactor, hEnvReactor, hReactorMem, hPair⟩ :=
          hCorrespondence.reactorOfActor
            name
            actor
            hOldMem

        exact
          ⟨envReactor,
           reactor,
           hEnvReactor,
           Store.mem_update_of_ne
             hReactorMem
             hNotSender,
           hOther
             name
             envReactor
             actor
             reactor
             hNotSender
             hNotReceiver
             hPair⟩

  · intro name reactor hMem

    dsimp only at hMem ⊢

    by_cases hIsReceiver :
        name = receiverName

    · subst hIsReceiver

      -- Store uniqueness on the updated target store: the reactor at this key is the one the caller
      -- named, not a stale second entry.
      obtain rfl :=
        Store.eq_of_mem_mem_of_keysUnique
          (Store.keysUnique_update
            hUniqueT)
          hMem
          hTargetReceiverMem

      exact
        ⟨envReceiver,
         receiverPost,
         hEnvReceiver,
         Store.mem_update_self
           _
           name
           receiverPost,
         hReceiverPost⟩

    · by_cases hIsSender :
          name = senderName

      · subst hIsSender

        obtain rfl :=
          Store.eq_of_mem_mem_of_keysUnique
            (Store.keysUnique_update
              hUniqueT)
            hMem
            hTargetSenderMem

        exact
          ⟨envSender,
           senderPost,
           hEnvSender,
           Store.mem_update_of_ne
             (Store.mem_update_self
               config.actors
               name
               senderPost)
             hIsReceiver,
           hSenderPost hIsReceiver⟩

      · rcases
            Store.mem_update_cases_of_keysUnique
              hUniqueT
              hMem with
          ⟨hName, _⟩ | ⟨hOldMem, _⟩

        · exact
            absurd hName hIsSender

        · obtain ⟨envActor, actor, hEnvActor, hActorMem, hPair⟩ :=
            hCorrespondence.actorOfReactor
              name
              reactor
              hOldMem

          exact
            ⟨envActor,
             actor,
             hEnvActor,
             Store.mem_update_of_ne
               (Store.mem_update_of_ne
                 hActorMem
                 hIsSender)
               hIsReceiver,
             hOther
               name
               envActor
               actor
               reactor
               hIsSender
               hIsReceiver
               hPair⟩

  · intro candidate hMem

    dsimp only at hMem ⊢

    rcases List.mem_append.mp hMem with
      hOld | hNew

    · obtain ⟨actor, hActorMem⟩ :=
        hCorrespondence.pendingTargeted
          candidate
          hOld

      by_cases hIsReceiver :
          candidate.target = receiverName

      · rw [hIsReceiver]

        exact
          ⟨receiverPost,
           Store.mem_update_self
             _
             receiverName
             receiverPost⟩

      · by_cases hIsSender :
            candidate.target = senderName

        · rw [hIsSender]

          exact
            ⟨senderPost,
             Store.mem_update_of_ne
               (Store.mem_update_self
                 config.actors
                 senderName
                 senderPost)
               (by
                 rw [← hIsSender]
                 exact hIsReceiver)⟩

        · exact
            ⟨actor,
             Store.mem_update_of_ne
               (Store.mem_update_of_ne
                 hActorMem
                 hIsSender)
               hIsReceiver⟩

    · obtain rfl :=
        List.mem_singleton.mp hNew

      exact hEventTarget

/-!
## Send head inversions

The two remaining continuation-head discoveries, one per send shape. The self-send arm is
unconditional; the external arm needs the environment lookup, and returns the **entry**, which is the
object `Translation.generalConnectionFrom?_siteFaithful` consumes — so the routed-send proof never
re-derives which port the statement writes.
-/

/--
A compiled body whose source head is a self-send has the compiled `schedule` as its head.

The action name is existentially quantified rather than spelled out: it is
`generalActionNameAtSite` at the statement's own index, and the self-send proof needs only that the
target statement *is* a `schedule` carrying the compiled arguments and the source delay. Quantifying
keeps the site context out of this lemma's statement, where it would be an unused parameter.

That the name is site-derived rather than message-derived is F78's discipline, and the reason F56 gave
each site its own action; nothing here or downstream maps a message to a kind.
-/
theorem generalContinuationCompiles_selfSend_head
    {env : Translation.GeneralOutputPortEnv}
    {message : MsgName}
    {arguments : List DTR.GeneralExpr}
    {delay : Delay}
    {sourceRemaining : DTR.GeneralBody}
    {targetBody : LF.GeneralBody}
    (hCompiles :
      GeneralContinuationCompiles
        env
        (.send .selfTarget message arguments delay :: sourceRemaining)
        targetBody) :
    ∃ (actionName : ActionName)
      (targetRemaining : LF.GeneralBody),
      targetBody =
          LF.GeneralStmt.schedule
              actionName
              (arguments.map
                Translation.compileGeneralExpr)
              delay ::
            targetRemaining ∧
        GeneralContinuationCompiles
          env
          sourceRemaining
          targetRemaining := by

  obtain ⟨context, index, hCompiled, hSites⟩ :=
    hCompiles

  obtain
      ⟨compiledStatement,
       compiledRemaining,
       hStatement,
       hRemaining,
       hShape⟩ :=
    Translation.compileGeneralBody_cons_ok_inversion
      hCompiled

  rw [
    Translation.compileGeneralStmt_send_selfTarget
  ] at hStatement

  injection hStatement with hStatement

  subst hStatement

  exact
    ⟨_,
     compiledRemaining,
     hShape,
     ⟨context,
      index + 1,
      hRemaining,
      by
        intro k rebec message arguments delay rest hDrop entry hEntry

        refine
          hSites
            (k + 1)
            rebec
            message
            arguments
            delay
            rest
            ?_
            entry
            ?_

        · rw [
            List.drop_succ_cons
          ]

          exact hDrop

        · rw [
            show
                index + (k + 1) =
                  index + 1 + k from by
              omega
          ]

          exact hEntry⟩⟩

/--
A compiled body whose source head is an external send has the compiled `setPort` as its head, at the
entry the compiler resolved — and that entry's known rebec and delay are the statement's own.

The entry comes back as a member of its environment, which is exactly the shape
`generalConnectionFrom?_siteFaithful` takes. The `none` branch is the compiler's own refusal, so a
successful compilation rules it out.

**The two field equations are read straight off the relation's site conjunct at `k = 0`**, not
recomputed here. That is the whole reason the conjunct exists: the compiled `setPort` carries neither a
rebec nor a delay — the rebec became an output-port name and the delay became a property of the
connection — so a caller inverting a `setPort` head has no way back to the statement except through the
relation. `Translation.generalRouteFor_receiverInstance` turns the rebec into the route's receiver and
`Translation.generalRouteFor_delay` turns the delay into the route's delay, so these two equations are
exactly what a routed-send transfer needs and no more.
-/
theorem generalContinuationCompiles_routedSend_head
    {env : Translation.GeneralOutputPortEnv}
    {rebec : KnownRebecName}
    {message : MsgName}
    {arguments : List DTR.GeneralExpr}
    {delay : Delay}
    {sourceRemaining : DTR.GeneralBody}
    {targetBody : LF.GeneralBody}
    (hCompiles :
      GeneralContinuationCompiles
        env
        (.send (.knownRebec rebec) message arguments delay :: sourceRemaining)
        targetBody) :
    ∃ (entry : Translation.GeneralOutputPortEntry)
      (targetRemaining : LF.GeneralBody),
      entry ∈ env ∧
        entry.knownRebec = rebec ∧
        entry.delay = delay ∧
        targetBody =
          LF.GeneralStmt.setPort
              entry.outputPort
              (arguments.map
                Translation.compileGeneralExpr) ::
            targetRemaining ∧
        GeneralContinuationCompiles
          env
          sourceRemaining
          targetRemaining := by

  obtain ⟨context, index, hCompiled, hSites⟩ :=
    hCompiles

  obtain
      ⟨compiledStatement,
       compiledRemaining,
       hStatement,
       hRemaining,
       hShape⟩ :=
    Translation.compileGeneralBody_cons_ok_inversion
      hCompiled

  cases hEntry :
      Translation.generalEntryAtSite?
        env
        {
          body :=
            context.bodyKey

          index :=
            index
        } with

  | none =>
      simp [
        Translation.compileGeneralStmt,
        hEntry
      ] at hStatement

  | some entry =>

      rw [
        Translation.compileGeneralStmt_send_knownRebec_ok
          env
          context
          index
          rebec
          message
          arguments
          delay
          hEntry
      ] at hStatement

      injection hStatement with hStatement

      subst hStatement

      -- The two field equations, read straight off the relation's own site invariant at `k = 0`: the
      -- statement being compiled *is* the head of `source.drop 0`, and the entry the compiler looked
      -- up sits at that statement's own site. This is precisely the fact the relation carries, and the
      -- reason the routed half was blocked before it carried it.
      have hFields :
          entry.knownRebec = rebec ∧
            entry.delay = delay := by
        refine
          hSites
            0
            rebec
            message
            arguments
            delay
            sourceRemaining
            ?_
            entry
            ?_

        · rw [
            List.drop_zero
          ]

        · rw [
            show
                index + 0 = index from by
              omega
          ]

          exact hEntry

      exact
        ⟨entry,
         compiledRemaining,
         Translation.generalEntryAtSite?_mem
           env
           _
           entry
           hEntry,
         hFields.1,
         hFields.2,
         hShape,
         ⟨context,
      index + 1,
      hRemaining,
      by
        intro k tailRebec message arguments delay rest hDrop entry hEntry

        refine
          hSites
            (k + 1)
            tailRebec
            message
            arguments
            delay
            rest
            ?_
            entry
            ?_

        · rw [
            List.drop_succ_cons
          ]

          exact hDrop

        · rw [
            show
                index + (k + 1) =
                  index + 1 + k from by
              omega
          ]

          exact hEntry⟩⟩

/-!
## Self-send forward transfer

The first of the two send halves. `sendTargetActor?` returns the sender for `.selfTarget`, so the two
written keys coincide â and the proof leans on that rather than excluding it. The receiver record the
rule reads back is therefore the *already-advanced* sender record, which `Store.lookup_update_eq`
supplies and which is what F56's repair was about.
-/

/--
A source self-send is answered by a target `schedule`, preserving the correspondence.

**No `sender ≠ receiver` premise, and the proof needs the opposite.** `hTarget` forces
`receiverName = senderName`, so `hReceiver` resolves through `Store.lookup_update_eq` to the sender's
own advanced record, and `generalCorrespondence_send` is instantiated with one name and one target
reactor, its `hSenderPost` discharged vacuously â that hypothesis' `senderName ≠ receiverName`
premise is unsatisfiable here, which is exactly why it was made conditional.

The three `GeneralConsumeMatch` conjuncts: the event targets the sending reactor by construction; its
tag time is `LogicalTime.after state.currentTag.time delay` by `LF.Tag.schedule_time`, equal to the
source's `LogicalTime.after config.now delay` through the correspondence's `logicalTime`; and its
payload is the compiled source payload by `compileGeneralExpr_preserves_evaluateArguments`.

The event's kind is `.logicalAction` of the name the *compiled statement* carries â read off the
statement, never derived from the message. F78.
-/
theorem generalSelfSend_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {senderName receiverName : ActorName}
    {sender receiver : DTR.GeneralActorRuntime}
    {message : MsgName}
    {arguments : List DTR.GeneralExpr}
    {delay : Delay}
    {remaining : DTR.GeneralBody}
    {payload : DTR.GeneralPayload}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hSender :
      Store.lookup config.actors senderName =
        some sender)
    (hBody :
      sender.activeBody =
        DTR.GeneralStmt.send .selfTarget message arguments delay :: remaining)
    (hArguments :
      DTR.GeneralExpr.evaluateArguments
          sender.state.valuation
          arguments =
        some payload)
    (hTarget :
      DTR.sendTargetActor?
          model
          senderName
          .selfTarget =
        some receiverName)
    (hReceiver :
      Store.lookup
          (Store.update
            config.actors
            senderName
            {
              state := sender.state
              activeBody := remaining
            })
          receiverName =
        some receiver) :
    ∃ state' : LF.GeneralRuntimeState,
      LF.GeneralStep
          program
          state
          LF.GeneralLabel.tau
          state' ∧
        GeneralStateCorrespondence
          model
          {
            now := config.now

            actors :=
              Store.update
                (Store.update
                  config.actors
                  senderName
                  {
                    state := sender.state
                    activeBody := remaining
                  })
                receiverName
                {
                  state :=
                    {
                      valuation := receiver.state.valuation

                      bag :=
                        receiver.state.bag ++
                          [{
                            sender := senderName
                            messageName := message
                            payload := payload
                            arrival :=
                              LogicalTime.after
                                config.now
                                delay
                          }]
                    }

                  activeBody := receiver.activeBody
                }
          }
          state' := by

  -- `.selfTarget` resolves to the sender, so the two written keys are one key.
  have hSame :
      receiverName = senderName := by
    unfold DTR.sendTargetActor? at hTarget

    exact
      (Option.some.inj hTarget).symm

  subst hSame

  -- Therefore the record the rule reads back is the sender's own advanced record.
  obtain rfl :
      receiver =
        {
          state := sender.state
          activeBody := remaining
        } := by
    rw [
      Store.lookup_update_eq
    ] at hReceiver

    exact
      (Option.some.inj hReceiver).symm

  obtain ⟨env, reactor, hEnv, hReactorMem, hPair⟩ :=
    hCorrespondence.reactorOfActor
      receiverName
      sender
      (Store.mem_of_lookup
        config.actors
        receiverName
        sender
        hSender)

  obtain ⟨actionName, targetRemaining, hTargetBody, hTailCompiles⟩ :=
    generalContinuationCompiles_selfSend_head
      (by
        rw [← hBody]

        exact hPair.continuation)

  have hTargetArguments :
      LF.GeneralExpr.evaluateArguments
          reactor.valuation
          (arguments.map
            Translation.compileGeneralExpr) =
        some
          (payload.map
            Translation.compileGeneralValue) := by
    rw [
      compileGeneralExpr_preserves_evaluateArguments
        hPair.valuation
        arguments,
      hArguments
    ]

    rfl

  refine
    ⟨_,
     LF.GeneralStep.schedule
       (Store.lookup_of_mem_of_keysUnique
         state.reactors
         hUniqueT
         hReactorMem)
       hTargetBody
       hTargetArguments,
     ?_⟩

  refine
    generalCorrespondence_send
      hCorrespondence
      hUniqueS
      hUniqueT
      receiverName
      receiverName
      env
      env
      hEnv
      hEnv
      {
        state := sender.state
        activeBody := remaining
      }
      _
      {
        valuation := reactor.valuation
        activeBody := targetRemaining
      }
      {
        valuation := reactor.valuation
        activeBody := targetRemaining
      }
      _
      (Store.mem_update_self
        state.reactors
        receiverName
        _)
      (Store.mem_update_self
        state.reactors
        receiverName
        _)
      (fun hNe =>
        absurd rfl hNe)
      ?_
      ?_
      ?_

  · refine
      {
        valuation := hPair.valuation

        messages :=
          generalPendingAgrees_append_matched
            hPair.messages
            ?_

        continuation := hTailCompiles
      }

    refine
      ⟨rfl, ?_, ?_⟩

    · show
        (LF.Tag.schedule
            state.currentTag
            delay).time =
          LogicalTime.after
            config.now
            delay

      rw [
        LF.Tag.schedule_time,
        hCorrespondence.logicalTime
      ]

    · rfl

  · intro name envOther actor candidateReactor hNotSender _ hCandidatePair

    refine
      {
        valuation := hCandidatePair.valuation

        messages :=
          generalPendingAgrees_append_other
            hCandidatePair.messages
            ?_

        continuation := hCandidatePair.continuation
      }

    show
      receiverName ≠ name

    exact Ne.symm hNotSender

  · exact
      ⟨_,
       Store.mem_update_self
         _
         receiverName
         _⟩

/-!
## The topology/bindings bridge for routed sends

The one step the previous session flagged as unmeasured, and it is small. The source resolves a
routed receiver through `ActorTopology.resolve model.topology senderName rebec`, which looks the
*sender* up in `model.topology` and then the rebec up in the bindings found there. The routing
construction instead uses `Store.lookup actor.bindings entry.knownRebec` at the instance record
itself. `DTR.GeneralModel.topology` is `model.instances.map (fun actor => (actor.name, actor.bindings))`,
so the two agree as soon as the instance's name resolves to the instance's own bindings â which needs
instance-name distinctness and nothing else.
-/

/--
An instance's bindings are what its name resolves to in the derived topology.

Instance-name `Nodup` is the whole hypothesis, and it is not optional: `Store.lookup` returns the
first match, so a model with two instances of one name would resolve the name to the wrong bindings.
It is the same accepted-program fact `DTR.generalStoreKeyUnique_initial` and
`Translation.routesOf_sourceEndpoints_nodup` consume, spelled as a `Nodup` over instance names rather
than as a whole `wellFormed` premise.
-/
theorem lookup_topology_of_mem_instances
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    (hActor :
      actor ∈ model.instances)
    (hNames :
      (List.map
        (fun candidate =>
          candidate.name)
        model.instances).Nodup) :
    Store.lookup
        model.topology
        actor.name =
      some actor.bindings := by

  refine
    Store.lookup_of_mem_of_keysUnique
      model.topology
      ?_
      ?_

  · show
      (Store.keys
        (DTR.GeneralModel.topology model)).Nodup

    unfold DTR.GeneralModel.topology

    unfold Store.keys

    rw [List.map_map]

    exact hNames

  · unfold DTR.GeneralModel.topology

    exact
      List.mem_map_of_mem
        hActor

/--
A routed send's resolved receiver is the sender instance's own binding for that known rebec.

The bridge in the form the routed-send proof consumes: it turns the source rule's `hTarget` premise,
which is about the derived topology, into a `Store.lookup` on the instance record that
`Translation.generalRouteFor` reads. Both halves are the same lookup once
`lookup_topology_of_mem_instances` has identified the bindings.
-/
theorem sendTargetActor?_knownRebec_eq_bindings
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    {rebec : KnownRebecName}
    (hActor :
      actor ∈ model.instances)
    (hNames :
      (List.map
        (fun candidate =>
          candidate.name)
        model.instances).Nodup) :
    DTR.sendTargetActor?
        model
        actor.name
        (.knownRebec rebec) =
      Store.lookup
        actor.bindings
        rebec := by

  unfold DTR.sendTargetActor?

  unfold ActorTopology.resolve

  rw [
    lookup_topology_of_mem_instances
      hActor
      hNames
  ]

/-!
## Routed-send forward transfer

The second send half, and the last statement rule. The target answer is `LF.GeneralStep.setPort`, and
its `hConnection` premise is discharged by `Translation.generalConnectionFrom?_siteFaithful` — the
site-faithful lookup, not an existential route.

**The link that made this provable** is the migrated relation's site conjunct: instantiated at
`k = 0` inside `generalContinuationCompiles_routedSend_head`, it yields
`entry.knownRebec = rebec`, tying the entry the compiler resolved to the statement being executed.
Composing that with `Translation.generalRouteFor_receiverInstance` and
`sendTargetActor?_knownRebec_eq_bindings` identifies the source's resolved receiver with the
connection's target instance. Before the migration this equation was unavailable and the routed half
was blocked on it for three sessions.

**No distinctness premise, and both coincidence cases are live.** A `.knownRebec` may resolve to the
sending instance, since `ActorTopology.resolve` can bind a rebec to its own actor. The proof therefore
splits on `senderName = receiverName`: when they coincide the receiver record the rule reads back is
the sender's own advanced record and one target reactor serves both roles; when they differ the
receiver is untouched in both stores. `generalCorrespondence_send` was written to tolerate exactly
this, which is why its `hSenderPost` hypothesis is conditional.
-/

/--
A source routed send is answered by a target `setPort`, preserving the correspondence.

The premises beyond the statement rule's own are the ordinary eligibility assumptions that
`Translation.generalConnectionFrom?_siteFaithful` takes — a successful compilation, its routing table,
the sending instance and its class, and the two accepted-program `Nodup` facts. **None of them is a
routed-send-specific assumption**, and in particular nothing here assumes route uniqueness, target
uniqueness, or injectivity of `outputPortNameFor`.

The `GeneralConsumeMatch` conjuncts are read off the *selected connection*: its target instance is the
route's receiver, which the bridge identifies with the source's; its input port is the route's; and its
delay is the route's, which is where the source send's own delay enters the tag through
`LF.Tag.schedule_time` and the correspondence's `logicalTime`. The event kind is `.inputPort` of the
connection's target port — whatever the runtime followed, never a function of the message. F78.
-/
theorem generalRoutedSend_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {senderInstance : DTR.GeneralActorInstance}
    {sendingClass : DTR.GeneralReactiveClass}
    {senderEnv : Translation.GeneralOutputPortEnv}
    {receiverName : ActorName}
    {sender receiver : DTR.GeneralActorRuntime}
    {rebec : KnownRebecName}
    {message : MsgName}
    {arguments : List DTR.GeneralExpr}
    {delay : Delay}
    {remaining : DTR.GeneralBody}
    {payload : DTR.GeneralPayload}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hInstance :
      senderInstance ∈ model.instances)
    (hClass :
      model.class? senderInstance.className =
        some sendingClass)
    (hSenderEnv :
      Translation.outputPortEnvOf
          model.classes
          sendingClass =
        .ok senderEnv)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
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
        model.instances).Nodup)
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hSender :
      Store.lookup config.actors senderInstance.name =
        some sender)
    (hBody :
      sender.activeBody =
        DTR.GeneralStmt.send
            (.knownRebec rebec)
            message
            arguments
            delay ::
          remaining)
    (hArguments :
      DTR.GeneralExpr.evaluateArguments
          sender.state.valuation
          arguments =
        some payload)
    (hTarget :
      DTR.sendTargetActor?
          model
          senderInstance.name
          (.knownRebec rebec) =
        some receiverName)
    (hReceiver :
      Store.lookup
          (Store.update
            config.actors
            senderInstance.name
            {
              state := sender.state
              activeBody := remaining
            })
          receiverName =
        some receiver) :
    ∃ state' : LF.GeneralRuntimeState,
      LF.GeneralStep
          program
          state
          LF.GeneralLabel.tau
          state' ∧
        GeneralStateCorrespondence
          model
          {
            now := config.now

            actors :=
              Store.update
                (Store.update
                  config.actors
                  senderInstance.name
                  {
                    state := sender.state
                    activeBody := remaining
                  })
                receiverName
                {
                  state :=
                    {
                      valuation := receiver.state.valuation

                      bag :=
                        receiver.state.bag ++
                          [{
                            sender := senderInstance.name
                            messageName := message
                            payload := payload
                            arrival :=
                              LogicalTime.after
                                config.now
                                delay
                          }]
                    }

                  activeBody := receiver.activeBody
                }
          }
          state' := by

  -- The sender's own pairing, at the environment the correspondence pins for it.
  obtain ⟨senderEnvAt, reactor, hEnvSenderAt, hReactorMem, hPair⟩ :=
    hCorrespondence.reactorOfActor
      senderInstance.name
      sender
      (Store.mem_of_lookup
        config.actors
        senderInstance.name
        sender
        hSender)

  -- The correspondence's environment for this actor is the class's. Derived, not assumed: the
  -- instance is declared and instance names are duplicate-free, so `classOfActor?` at its name
  -- resolves to its own class.
  have hEnvSenderName :
      outputPortEnvOfActorName model senderInstance.name =
        some senderEnv :=
    outputPortEnvOfActorName_eq_of_mem_instances
      hInstance
      hNames
      hClass
      hSenderEnv

  obtain rfl :
      senderEnv = senderEnvAt := by
    rw [
      hEnvSenderName
    ] at hEnvSenderAt

    exact
      (Option.some.inj hEnvSenderAt)

  -- Step 2: the routed head inversion, which also returns the rebec and delay equations.
  obtain ⟨entry, targetRemaining, hEntryMem, hEntryRebec, hEntryDelay, hTargetBody, hTailCompiles⟩ :=
    generalContinuationCompiles_routedSend_head
      (by
        rw [← hBody]

        exact hPair.continuation)

  -- Step 3: the compiled payload.
  have hTargetArguments :
      LF.GeneralExpr.evaluateArguments
          reactor.valuation
          (arguments.map
            Translation.compileGeneralExpr) =
        some
          (payload.map
            Translation.compileGeneralValue) := by
    rw [
      compileGeneralExpr_preserves_evaluateArguments
        hPair.valuation
        arguments,
      hArguments
    ]

    rfl

  -- Step 4: the site-faithful connection the runtime will follow.
  obtain
      ⟨route,
       hRoute,
       hRouteMem,
       hLookup,
       hSourceInstance,
       hSourcePort,
       hTargetInstance,
       hTargetPort,
       hDelay⟩ :=
    Translation.generalConnectionFrom?_siteFaithful
      hCompiled
      hRoutes
      hInstance
      hClass
      hSenderEnv
      hEntryMem
      hEnvNodup
      hNames

  -- Step 5: the source's resolved receiver is the route's receiver, hence the connection's target.
  have hReceiverIsTarget :
      receiverName =
        (Translation.generalConnectionOf route).targetInstance := by
    rw [
      hTargetInstance
    ]

    have hBindings :
        Store.lookup
            senderInstance.bindings
            rebec =
          some route.receiverInstance := by
      rw [
        ← hEntryRebec
      ]

      exact
        Translation.generalRouteFor_receiverInstance
          hRoute

    rw [
      sendTargetActor?_knownRebec_eq_bindings
        hInstance
        hNames,
      hBindings
    ] at hTarget

    exact
      (Option.some.inj hTarget).symm

  -- The target step. `hConnection` is the site-faithful lookup, rewritten to the port the compiled
  -- `.setPort` actually carries.
  refine
    ⟨_,
     LF.GeneralStep.setPort
       (Store.lookup_of_mem_of_keysUnique
         state.reactors
         hUniqueT
         hReactorMem)
       hTargetBody
       hTargetArguments
       hLookup,
     ?_⟩

  -- Step 6: the connection's delay *is* the source statement's delay. Three links, none of which the
  -- routing table could supply on its own: the relation's site conjunct ties the entry to the
  -- statement, and the two routing lemmas carry it entry → route → connection. This is where a
  -- routed send's `after` reaches the target's tag, since `setPort` carries no delay at all.
  have hConnectionDelay :
      (Translation.generalConnectionOf route).delay =
        delay := by
    rw [
      hDelay,
      Translation.generalRouteFor_delay
        hRoute,
      hEntryDelay
    ]

  rw [
    ← hReceiverIsTarget,
    hConnectionDelay
  ]

  -- The matched pair. Target by the bridge of step 5; tag time from `LF.Tag.schedule_time` against
  -- the source's `LogicalTime.after config.now delay` through the correspondence's `logicalTime`,
  -- now that the connection's delay has been identified with the statement's; payload from step 3.
  have hMatch :
      GeneralConsumeMatch
        receiverName
        {
          sender := senderInstance.name
          messageName := message
          payload := payload
          arrival :=
            LogicalTime.after
              config.now
              delay
        }
        {
          target :=
            receiverName

          kind :=
            LF.GeneralEventKind.inputPort
              (Translation.generalConnectionOf route).targetPort

          tag :=
            LF.Tag.schedule
              state.currentTag
              delay

          payload :=
            payload.map
              Translation.compileGeneralValue
        } := by
    refine
      ⟨rfl, ?_, rfl⟩

    show
      (LF.Tag.schedule
          state.currentTag
          delay).time =
        LogicalTime.after
          config.now
          delay

    rw [
      LF.Tag.schedule_time,
      hCorrespondence.logicalTime
    ]

  -- The two written source keys may coincide. `ActorTopology.resolve` can bind a known rebec to the
  -- sending instance, so a *routed* send can be a self-send in every respect except its syntax, and
  -- excluding that with a distinctness premise would silently narrow the theorem. Both cases are
  -- handled, and `generalCorrespondence_send`'s conditional `hSenderPost` is what makes one theorem
  -- serve both.
  by_cases hSame :
      receiverName = senderInstance.name

  · subst hSame

    -- The record the rule reads back is the sender's own advanced record.
    obtain rfl :
        receiver =
          {
            state := sender.state
            activeBody := remaining
          } := by
      rw [
        Store.lookup_update_eq
      ] at hReceiver

      exact
        (Option.some.inj hReceiver).symm

    refine
      generalCorrespondence_send
        hCorrespondence
        hUniqueS
        hUniqueT
        senderInstance.name
        senderInstance.name
        senderEnv
        senderEnv
        hEnvSenderName
        hEnvSenderName
        {
          state := sender.state
          activeBody := remaining
        }
        _
        {
          valuation := reactor.valuation
          activeBody := targetRemaining
        }
        {
          valuation := reactor.valuation
          activeBody := targetRemaining
        }
        _
        (Store.mem_update_self
          state.reactors
          senderInstance.name
          _)
        (Store.mem_update_self
          state.reactors
          senderInstance.name
          _)
        (fun hNe =>
          absurd rfl hNe)
        ?_
        ?_
        ?_

    · exact
        {
          valuation := hPair.valuation

          messages :=
            generalPendingAgrees_append_matched
              hPair.messages
              hMatch

          continuation := hTailCompiles
        }

    · intro name envOther actor candidateReactor hNotSender _ hCandidatePair

      refine
        {
          valuation := hCandidatePair.valuation

          messages :=
            generalPendingAgrees_append_other
              hCandidatePair.messages
              ?_

          continuation := hCandidatePair.continuation
        }

      show
        senderInstance.name ≠ name

      exact
        Ne.symm hNotSender

    · exact
        ⟨_,
         Store.mem_update_self
           _
           senderInstance.name
           _⟩

  · -- Distinct keys: the receiver's record is untouched by the sender's update, so its own pairing
    -- comes from the pre-state correspondence.
    have hReceiverOriginal :
        Store.lookup
            config.actors
            receiverName =
          some receiver := by
      rw [
        Store.lookup_update_ne
          config.actors
          _
          (Ne.symm hSame)
      ] at hReceiver

      exact hReceiver

    obtain ⟨envReceiver, targetReceiver, hEnvReceiver, hReceiverMem, hReceiverPair⟩ :=
      hCorrespondence.reactorOfActor
        receiverName
        receiver
        (Store.mem_of_lookup
          config.actors
          receiverName
          receiver
          hReceiverOriginal)

    refine
      generalCorrespondence_send
        hCorrespondence
        hUniqueS
        hUniqueT
        senderInstance.name
        receiverName
        senderEnv
        envReceiver
        hEnvSenderName
        hEnvReceiver
        {
          state := sender.state
          activeBody := remaining
        }
        _
        {
          valuation := reactor.valuation
          activeBody := targetRemaining
        }
        targetReceiver
        _
        (Store.mem_update_self
          state.reactors
          senderInstance.name
          _)
        (Store.mem_update_of_ne
          hReceiverMem
          hSame)
        ?_
        ?_
        ?_
        ?_

    · intro _

      exact
        {
          valuation := hPair.valuation

          messages :=
            generalPendingAgrees_append_other
              hPair.messages
              hSame

          continuation := hTailCompiles
        }

    · exact
        {
          valuation := hReceiverPair.valuation

          messages :=
            generalPendingAgrees_append_matched
              hReceiverPair.messages
              hMatch

          continuation := hReceiverPair.continuation
        }

    · intro name envOther actor candidateReactor _ hNotReceiver hCandidatePair

      refine
        {
          valuation := hCandidatePair.valuation

          messages :=
            generalPendingAgrees_append_other
              hCandidatePair.messages
              ?_

          continuation := hCandidatePair.continuation
        }

      show
        receiverName ≠ name

      exact
        Ne.symm hNotReceiver

    · exact
        ⟨_,
         Store.mem_update_self
           _
           receiverName
           _⟩

/-!
## What the routed half needed, and where each piece came from

`generalRoutedSend_forward` is the last of the four τ statement transfers, and it is the only one that
had to reach outside this module. Recording the assembled chain, because the same shape will be wanted
by the backward direction and because two earlier attempts at it failed on the same wall.

**The obstruction, twice.** A compiled `LF.GeneralStmt.setPort` carries a *port name* and nothing else:
the statement's known rebec became part of the generated port name (non-injectively — F48), and its
delay became a property of the connection the value travels along. So inverting a `setPort` head
recovers an entry that, on its own, says nothing about the statement it came from. Both the rebec and
the delay hit that wall, and neither can be recovered by composing routing lemmas at the transfer site:
`Translation.externalSendsFromIndex_knownRebec_of_drop` and
`Translation.externalSendsFromIndex_delay_of_drop` both need the class's *declared* body and the
statement's position in it, while `activeBody` is a suffix of a declared body whose `bodyKey` and
`index` are existential in `GeneralContinuationCompiles`.

**The repair, once.** `GeneralContinuationCompiles`' site conjunct concludes
`entry.knownRebec = rebec ∧ entry.delay = delay`, discharged at the single construction site
(`generalActorCorresponds_constructorEntry`) where the declared body *is* in hand, and read off here at
`k = 0` by `generalContinuationCompiles_routedSend_head`. The routing lemmas are what discharge it
there, so they are load-bearing — just at the other end of the relation.

**The chain, in the order the proof walks it.**

1. `hCorrespondence.reactorOfActor` → the sender's pairing, at the environment the relation pins;
   `outputPortEnvOfActorName_eq_of_mem_instances` identifies that environment with the class's, so no
   `hEnvAt` premise is exported.
2. `generalContinuationCompiles_routedSend_head` → the entry, its membership, and the two field
   equations.
3. `compileGeneralExpr_preserves_evaluateArguments` → the compiled payload.
4. `Translation.generalConnectionFrom?_siteFaithful` → the route, the `connectionFrom?` lookup the rule
   consumes, and the connection's five field equations.
5. `Translation.generalRouteFor_receiverInstance` with
   `sendTargetActor?_knownRebec_eq_bindings` → the source's resolved receiver *is* the connection's
   target instance. Both sides are one `Store.lookup` on the sending instance's bindings.
6. `Translation.generalRouteFor_delay` with the entry equation → the connection's delay is the
   statement's, so the emitted event lands at the tag the source names.
7. `generalCorrespondence_send`, case-split on whether the two written keys coincide.

**No new premises, and no narrowing.** `hEnvNodup` and `hNames` are accepted-program facts the routing
side already consumed; nothing here assumes route uniqueness, target-endpoint uniqueness, or
injectivity of `outputPortNameFor`, and the `receiverName = senderInstance.name` case is *handled*
rather than excluded — a routed send may resolve to its own sender, and a distinctness premise would
have silently dropped that. `GeneralConsumeMatch`'s event kind is `.inputPort` of the connection's
target port, whatever the runtime followed, never a function of the message. F78.

**What comes after this.** The `DTR.GeneralSendTarget` dispatch is `generalSend_forward`, the
constructor dispatch is `generalTau_forward`, and the closure is `generalTauSteps_forward` — all below,
in that order. The forward instant-block transfer this whole chain was discovered as a prerequisite of
consumes the last of them.
-/

/-!
## The send rule, both targets at once

`DTR.GeneralStep.send` is **one** constructor carrying a `DTR.GeneralSendTarget`, so the τ transfer owes
one theorem at that constructor's shape rather than two theorems a caller has to dispatch between. This
is that theorem, and its whole content is the case split: `DTR.GeneralSendTarget` has two constructors,
`generalSelfSend_forward` answers one and `generalRoutedSend_forward` the other.

**The premise set is the routed half's, and the self half ignores it.** The routed branch needs the
compiled program, the routing table, the sending instance and its class, its port environment, the
per-instance port `Nodup` and instance-name distinctness; the self branch needs none of those, because
`.selfTarget` resolves to the sender without consulting an entry, a route or a connection. Taking the
union is what lets the two halves stay as they are — the alternative, weakening the routed half, is not
available, and giving the caller two theorems would push the dispatch outwards to every consumer.

The `senderName`/`senderInstance` mismatch resolves in the same direction: `generalSelfSend_forward` is
stated over a bare `ActorName` while the routed half needs the *instance record* (its `bindings` are what
a known rebec resolves through). The combined statement follows the routed form and instantiates the
self branch at `senderInstance.name`.
-/

/--
A source `send` step is answered by a target step, preserving the correspondence.

The τ transfer for `DTR.GeneralStep.send`, both send targets. No new premises beyond the union of the
two halves', no distinctness premise, and no narrowing: neither branch excludes the case where the
sender and the resolved receiver are the same actor.

The two branches emit *different* target statements, and that asymmetry is the translation's, not this
proof's. A self-send compiles to `LF.GeneralStmt.schedule` on a site-derived logical action; a routed
send compiles to `LF.GeneralStmt.setPort`, whose value travels a connection carrying the delay. So the
existential target state is genuinely branch-dependent, which is why this is a case split rather than a
shared construction with two instantiations.
-/
theorem generalSend_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {senderInstance : DTR.GeneralActorInstance}
    {sendingClass : DTR.GeneralReactiveClass}
    {senderEnv : Translation.GeneralOutputPortEnv}
    {receiverName : ActorName}
    {sender receiver : DTR.GeneralActorRuntime}
    {sendTarget : DTR.GeneralSendTarget}
    {message : MsgName}
    {arguments : List DTR.GeneralExpr}
    {delay : Delay}
    {remaining : DTR.GeneralBody}
    {payload : DTR.GeneralPayload}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hInstance :
      senderInstance ∈ model.instances)
    (hClass :
      model.class? senderInstance.className =
        some sendingClass)
    (hSenderEnv :
      Translation.outputPortEnvOf
          model.classes
          sendingClass =
        .ok senderEnv)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
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
        model.instances).Nodup)
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hSender :
      Store.lookup config.actors senderInstance.name =
        some sender)
    (hBody :
      sender.activeBody =
        DTR.GeneralStmt.send sendTarget message arguments delay ::
          remaining)
    (hArguments :
      DTR.GeneralExpr.evaluateArguments
          sender.state.valuation
          arguments =
        some payload)
    (hTarget :
      DTR.sendTargetActor?
          model
          senderInstance.name
          sendTarget =
        some receiverName)
    (hReceiver :
      Store.lookup
          (Store.update
            config.actors
            senderInstance.name
            {
              state := sender.state
              activeBody := remaining
            })
          receiverName =
        some receiver) :
    ∃ state' : LF.GeneralRuntimeState,
      LF.GeneralStep
          program
          state
          LF.GeneralLabel.tau
          state' ∧
        GeneralStateCorrespondence
          model
          {
            now := config.now

            actors :=
              Store.update
                (Store.update
                  config.actors
                  senderInstance.name
                  {
                    state := sender.state
                    activeBody := remaining
                  })
                receiverName
                {
                  state :=
                    {
                      valuation := receiver.state.valuation

                      bag :=
                        receiver.state.bag ++
                          [{
                            sender := senderInstance.name
                            messageName := message
                            payload := payload
                            arrival :=
                              LogicalTime.after
                                config.now
                                delay
                          }]
                    }

                  activeBody := receiver.activeBody
                }
          }
          state' := by

  -- `DTR.GeneralSendTarget` has exactly two constructors, and each half is already proved. A third
  -- send target would break this match rather than fall through a default branch, which is why the
  -- source syntax keeps one `send` statement instead of splitting self-sends off.
  cases sendTarget with

  | selfTarget =>
      exact
        generalSelfSend_forward
          hCorrespondence
          hUniqueS
          hUniqueT
          hSender
          hBody
          hArguments
          hTarget
          hReceiver

  | knownRebec rebec =>
      exact
        generalRoutedSend_forward
          hCompiled
          hRoutes
          hInstance
          hClass
          hSenderEnv
          hEnvNodup
          hNames
          hCorrespondence
          hUniqueS
          hUniqueT
          hSender
          hBody
          hArguments
          hTarget
          hReceiver

/-!
## The τ dispatch

`DTR.GeneralStep` has five constructors and the three τ ones are covered above, so what is left is the
dispatch: one theorem taking a source step *at label `.tau`* and producing a matching target step. This
is the interface the `Common.TauSteps` closure induces over, and the first statement in this module whose
premises mention no statement shape at all.

**`take` and `timeProgress` are excluded, and excluded by their labels rather than by their shape.**
They carry `.consume` and `.timeAdvance`, so fixing the label index to `.tau` makes them unconstructible
and the eliminator discards them. That is deliberate: a dispatch that matched on statement shape and
defaulted the rest would silently absorb a sixth constructor, while this one becomes a build error.
`take` is handled by `generalConsume_forward_weak_of_fireRepresentative` and `timeProgress` by the
time-equivalence layer; neither is this theorem's business.
-/

private theorem findActor?_mem_and_name :
    ∀ (instances : List DTR.GeneralActorInstance)
      (actorName : ActorName)
      (actor : DTR.GeneralActorInstance),
      DTR.findActor? instances actorName = some actor →
        actor ∈ instances ∧
          actor.name = actorName := by

  intro instances
  induction instances with

  | nil =>
      intro actorName actor hFound

      simp [
        DTR.findActor?
      ] at hFound

  | cons head remaining inductionHypothesis =>
      intro actorName actor hFound

      by_cases hHead :
          head.name = actorName

      · rw [
          DTR.findActor?,
          if_pos hHead
        ] at hFound

        injection hFound with hFound

        subst hFound

        exact
          ⟨List.mem_cons_self,
           hHead⟩

      · rw [
          DTR.findActor?,
          if_neg hHead
        ] at hFound

        obtain ⟨hMember, hName⟩ :=
          inductionHypothesis
            actorName
            actor
            hFound

        exact
          ⟨List.mem_cons_of_mem
             _
             hMember,
           hName⟩

/--
The correspondence's pinned environment names a declared instance and its class.

The converse of `outputPortEnvOfActorName_eq`, and the reason the τ dispatch below needs **no** routing
premises about the stepping actor. `outputPortEnvOfActorName` is defined through
`DTR.GeneralModel.classOfActor?`, which resolves the *instance* before it resolves the class, so an
environment equation already contains everything `generalRoutedSend_forward` asks for about its sender:
the instance record, its membership, its class, and the environment that class compiles to.

This matters because `DTR.GeneralStep.send` carries only a `senderName : ActorName`, while the routed
transfer needs the instance *record* — a known rebec resolves through `senderInstance.bindings`. Without
this inversion the dispatch would have to take a premise tying runtime actor names to declared
instances, and that premise would be an obligation no caller could discharge from the relation it
already holds. It turns out not to be needed: the relation carries it.

Both `.toOption` refusal branches and the two `none` branches close by `simp`; the content is that
`DTR.findActor?` answers with a member carrying the queried name.
-/
theorem exists_instance_of_outputPortEnvOfActorName
    {model : DTR.GeneralModel}
    {name : ActorName}
    {env : Translation.GeneralOutputPortEnv}
    (hEnv :
      outputPortEnvOfActorName model name =
        some env) :
    ∃ (senderInstance : DTR.GeneralActorInstance)
      (sendingClass : DTR.GeneralReactiveClass),
      senderInstance ∈ model.instances ∧
        senderInstance.name = name ∧
        model.class? senderInstance.className =
          some sendingClass ∧
        Translation.outputPortEnvOf
            model.classes
            sendingClass =
          .ok env := by

  unfold outputPortEnvOfActorName at hEnv

  cases hActor :
      model.actor? name with

  | none =>
      rw [
        show
            model.classOfActor? name =
              none from by
          unfold DTR.GeneralModel.classOfActor?
          rw [hActor]
      ] at hEnv

      simp at hEnv

  | some senderInstance =>

      obtain ⟨hMember, hName⟩ :=
        findActor?_mem_and_name
          model.instances
          name
          senderInstance
          (by
            unfold DTR.GeneralModel.actor? at hActor
            exact hActor)

      cases hClass :
          model.class? senderInstance.className with

      | none =>
          rw [
            show
                model.classOfActor? name =
                  none from by
              unfold DTR.GeneralModel.classOfActor?
              rw [hActor]
              exact hClass
          ] at hEnv

          simp at hEnv

      | some sendingClass =>

          rw [
            show
                model.classOfActor? name =
                  some sendingClass from by
              unfold DTR.GeneralModel.classOfActor?
              rw [hActor]
              exact hClass
          ] at hEnv

          dsimp only at hEnv

          cases hEnvOf :
              Translation.outputPortEnvOf
                model.classes
                sendingClass with

          | error diagnostic =>
              rw [hEnvOf] at hEnv

              simp [
                Except.toOption
              ] at hEnv

          | ok resolved =>
              rw [hEnvOf] at hEnv

              simp [
                Except.toOption
              ] at hEnv

              subst hEnv

              exact
                ⟨senderInstance,
                 sendingClass,
                 hMember,
                 hName,
                 hClass,
                 hEnvOf⟩

/--
Every source τ step is answered by a target τ step, preserving the correspondence.

The dispatch over `DTR.GeneralStep`'s three τ constructors, onto `generalAssign_forward`,
`generalTrace_forward` and `generalSend_forward`. This is the theorem the `Common.TauSteps` closure
inducts over, and its statement mentions no statement shape — the source step is the whole hypothesis.

**Only four premises beyond the step and the correspondence**, and every one of them is an
accepted-program fact the routing side already consumed: the compilation, the routing table, the
per-instance output-port `Nodup`, and instance-name distinctness. In particular there is **no** premise
tying the stepping actor to a declared instance; `exists_instance_of_outputPortEnvOfActorName` derives
that from the environment the correspondence already pins, so the `send` branch reaches
`generalSend_forward` without exporting an obligation.

`take` and `timeProgress` do not appear because they cannot: their labels are `.consume` and
`.timeAdvance`, so at label `.tau` the eliminator discards them.
-/
theorem generalTau_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
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
        model.instances).Nodup)
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hStep :
      DTR.GeneralStep
        model
        config
        DTR.GeneralLabel.tau
        config') :
    ∃ state' : LF.GeneralRuntimeState,
      LF.GeneralStep
          program
          state
          LF.GeneralLabel.tau
          state' ∧
        GeneralStateCorrespondence
          model
          config'
          state' := by

  cases hStep with

  | assign hActor hBody hEvaluate =>
      exact
        generalAssign_forward
          hCorrespondence
          hUniqueS
          hUniqueT
          hActor
          hBody
          hEvaluate

  | trace hActor hBody =>
      exact
        generalTrace_forward
          hCorrespondence
          hUniqueS
          hUniqueT
          hActor
          hBody

  | send hSender hBody hArguments hTarget hReceiver =>

      -- The sending actor's own instance record, recovered from the environment the correspondence
      -- pins for it. This is what lets the routed half be reached from a step that names only an actor.
      -- The step's own binders stay inaccessible; every position below is inferred from `hSender`.
      obtain ⟨senderEnv, _, hEnvAt, _, _⟩ :=
        hCorrespondence.reactorOfActor
          _
          _
          (Store.mem_of_lookup
            config.actors
            _
            _
            hSender)

      obtain ⟨senderInstance, sendingClass, hInstance, hName, hClass, hSenderEnv⟩ :=
        exists_instance_of_outputPortEnvOfActorName
          hEnvAt

      subst hName

      exact
        generalSend_forward
          hCompiled
          hRoutes
          hInstance
          hClass
          hSenderEnv
          hEnvNodup
          hNames
          hCorrespondence
          hUniqueS
          hUniqueT
          hSender
          hBody
          hArguments
          hTarget
          hReceiver

/-!
## The τ closure

The theorem the forward instant-block wrapper actually calls. A source instant block is
`Common.WeakSteps (DTR.GeneralStep model) DTR.GeneralLabel.isTau`, and `Common.WeakStep.visible` pads
every visible label with a `TauSteps` prefix and suffix, so what the wrapper needs across each padding
is exactly this: a source τ closure answered by a target τ closure.

**Two theorems, because the raw induction and the α-lift are different obligations.** The induction
below stays in the *raw* target system, and `generalTauSteps_forward` lifts its result once with
`LF.GeneralStepModulo.tauSteps_of_raw`. Lifting inside the induction would put one
`GeneralStepModulo.of_raw` on every step and invite a representative switch at each one; decision 0042's
quotient is entered at the closure boundary and nowhere else.

**The two store-uniqueness premises are re-established at every step, not assumed along the way.**
`DTR.generalStoreKeyUnique_of_step` and `LF.generalStoreKeyUnique_of_step` are what carry them, and they
have to be threaded because `generalTau_forward` consumes both at each step — the source's to rule out a
stale shadowed binding at the key a step writes, the target's to turn a reactor membership into the
lookup a target rule wants.
-/

/--
A source τ closure is answered by a raw target τ closure, preserving the correspondence.

Induction on `Common.TauSteps`' two constructors. `refl` answers with `refl` and the correspondence
unchanged; `cons` takes one step with `generalTau_forward`, re-establishes both store invariants at the
intermediate states, recurses, and prefixes the produced target step.

**The step's label is forced to `.tau` rather than assumed.** `DTR.GeneralLabel.isTau` is `True` only at
`tau`, so the two visible labels are refuted by `not_isTau_timeAdvance` and `not_isTau_consume`. This is
where the closure's τ filter and the dispatch's label index meet, and refuting rather than defaulting is
what keeps a future visible label from silently entering the internal closure.

Stated in the raw target system on purpose; `generalTauSteps_forward` below is the lifted form.
-/
theorem generalTauSteps_forward_raw
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
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
        model.instances).Nodup)
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hSteps :
      Common.TauSteps
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        config') :
    ∃ state' : LF.GeneralRuntimeState,
      Common.TauSteps
          (LF.GeneralStep program)
          LF.GeneralLabel.isTau
          state
          state' ∧
        GeneralStateCorrespondence
          model
          config'
          state' := by

  induction hSteps generalizing state with

  | refl current =>
      exact
        ⟨state,
         Common.TauSteps.refl state,
         hCorrespondence⟩

  | @cons _ _ _ label headStep headIsTau remainingSteps IH =>

      -- The closure's τ filter forces the step's label. `DTR.GeneralLabel.isTau` is a match returning
      -- `True` only at `tau`, so the two visible labels are refuted from `headIsTau` rather than
      -- defaulted away.
      cases label with

      | timeAdvance before after =>
          exact
            absurd
              headIsTau
              (DTR.GeneralLabel.not_isTau_timeAdvance
                before
                after)

      | consume receiver consumedMessage =>
          exact
            absurd
              headIsTau
              (DTR.GeneralLabel.not_isTau_consume
                receiver
                consumedMessage)

      | tau =>

          -- One step, by the dispatch.
          obtain ⟨middleState, hMiddleStep, hMiddleCorrespondence⟩ :=
            generalTau_forward
              hCompiled
              hRoutes
              hEnvNodup
              hNames
              hCorrespondence
              hUniqueS
              hUniqueT
              headStep

          -- Both invariants at the intermediate states, so the recursion may consume them again.
          obtain ⟨tailState, hTailSteps, hTailCorrespondence⟩ :=
            IH
              hMiddleCorrespondence
              (DTR.generalStoreKeyUnique_of_step
                hUniqueS
                headStep)
              (LF.generalStoreKeyUnique_of_step
                hUniqueT
                hMiddleStep)

          exact
            ⟨tailState,
             Common.TauSteps.cons
               hMiddleStep
               LF.GeneralLabel.isTau_tau
               hTailSteps,
             hTailCorrespondence⟩

/--
A source τ closure is answered by a target τ closure in the quotient system.

The closure form the forward instant-block wrapper consumes, and the **one** place
`LF.GeneralStepModulo.tauSteps_of_raw` is applied in this module. Everything above it is raw, so no
α-representative is ever switched mid-closure; the quotient of decision 0042 is entered here, at the
boundary, and the whole internal segment is lifted in a single step.
-/
theorem generalTauSteps_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
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
        model.instances).Nodup)
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hSteps :
      Common.TauSteps
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        config') :
    ∃ state' : LF.GeneralRuntimeState,
      Common.TauSteps
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          state' ∧
        GeneralStateCorrespondence
          model
          config'
          state' := by

  obtain ⟨state', hRawSteps, hFinalCorrespondence⟩ :=
    generalTauSteps_forward_raw
      hCompiled
      hRoutes
      hEnvNodup
      hNames
      hCorrespondence
      hUniqueS
      hUniqueT
      hSteps

  exact
    ⟨state',
     LF.GeneralStepModulo.tauSteps_of_raw
       hRawSteps,
     hFinalCorrespondence⟩

end Correctness

end Relico
