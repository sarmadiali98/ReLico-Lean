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

  obtain ⟨context, index, hCompiled⟩ :=
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
     ⟨context, index + 1, hRemaining⟩⟩

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

  obtain ⟨context, index, hCompiled⟩ :=
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
     ⟨context, index + 1, hRemaining⟩⟩

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

  obtain ⟨context, index, hCompiled⟩ :=
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
     ⟨context, index + 1, hRemaining⟩⟩

/--
A compiled body whose source head is an external send has the compiled `setPort` as its head, at the
entry the compiler resolved.

The entry comes back as a member of its environment, which is exactly the shape
`generalConnectionFrom?_siteFaithful` takes. The `none` branch is the compiler's own refusal, so a
successful compilation rules it out.
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

  obtain ⟨context, index, hCompiled⟩ :=
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

      exact
        ⟨entry,
         compiledRemaining,
         Translation.generalEntryAtSite?_mem
           env
           _
           entry
           hEntry,
         hShape,
         ⟨context, index + 1, hRemaining⟩⟩

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
## What remains: the entry-to-send inversion landed, and the site link is still absent

Option 3 was implemented. `Translation.exists_send_of_mem_outputPortEnv`
(`Relico/Correctness/GeneralConnectionSourceUniqueness.lean`) is green and supplies the direction
`GeneralRouting` never had: from `entry ∈ env`, recover an originating external send together with
`entry.knownRebec = send.knownRebec` and `entry.site = send.site`. It is existential in the send and
introduces no uniqueness, which is what makes it sound in the presence of F48.

It is necessary and **not sufficient**, and the reason is worth recording exactly, because it is a
different obstruction from the one this section described before.

**The chain, and where it now breaks.** Matching the routed rule needs
`entry.knownRebec = rebec`, since `Translation.generalRouteFor` computes the route's receiver from
`Store.lookup actor.bindings entry.knownRebec` while the source resolves
`Store.lookup actor.bindings rebec` (`sendTargetActor?_knownRebec_eq_bindings`). Composing what is now
available:

- `Translation.compileGeneralStmt_send_knownRebec_ok` → the entry is
  `generalEntryAtSite? env ⟨context.bodyKey, index⟩`;
- `Translation.generalEntryAtSite?_site` → `entry.site = ⟨context.bodyKey, index⟩`;
- `exists_send_of_mem_outputPortEnv` → a send with `send.site = entry.site` and
  `entry.knownRebec = send.knownRebec`.

So the missing step is now precisely `send.knownRebec = rebec`: the send sitting at
`⟨context.bodyKey, index⟩` in `externalSendsOfClass sendingClass` must be the statement being
executed. `Translation.externalSendsFromIndex`'s `.knownRebec` arm does put a statement's rebec into
the send at its own site, so the fact is true of the *declared* body — but the runtime `activeBody` is
a **suffix** of that declared body, and `context.bodyKey` and `index` are existential in
`GeneralContinuationCompiles`. Nothing relates the position the compilation restarted from to a
position in the class's declared bodies.

**That is option 1, and option 1 is excluded.** Pinning `bodyKey` and `index` would supply the link,
and it is the only thing that would: the equation is about *where in the class* the running statement
sits, which is information the relation deliberately does not carry. Carrying
`entry.knownRebec = rebec` as a premise (option 2) is likewise excluded. So `generalRoutedSend_forward`
is blocked on a standing constraint rather than on missing infrastructure, and every routing lemma it
could want now exists.

**What this leaves.** `generalTrace_forward`, `generalAssign_forward` and `generalSelfSend_forward` are
green and unaffected — the self-send half never needed the site, because `.selfTarget` resolves to the
sender without consulting an entry. `generalSend_forward`, `generalTau_forward` and the
`Common.TauSteps` closure remain behind the routed half; the closure is still where the single
`LF.GeneralStepModulo.tauSteps_of_raw` lift belongs.

The decision that would unblock this is whether the correspondence should record *which body position*
a reactor is executing. That is a change to the shape of the relation, not its arity, and it is not
one to make silently.

Nothing here weakens a correspondence conjunct, adds a distinctness premise, introduces a
message-to-kind map, assumes route or target-endpoint uniqueness, or transports store-key uniqueness
through α.
-/

end Correctness

end Relico
