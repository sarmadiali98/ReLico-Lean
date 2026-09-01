/-
! # Backward instant-block transfer, general family: the source-readiness derivation

The backward direction's first obligation, attempted before the wrapper because the audit found it to
be the thing the wrapper stands or falls on.

## The obstruction the audit measured

`DTR.GeneralStep.take` resolves **which actor** steps through
`DTR.GeneralActorSelection.selectedActor`, which is a *function*: a `selectMinimum` fold over
`DTR.GeneralConfiguration.readyActors` ordered by actor priority and then arrival. So the source's
choice of actor is deterministic, and `DTR.take_of_split` — the availability statement F27 rests on —
frees only the choice of **message inside that actor's bag**, never the actor. When a target block fires
reactor `B` while source priority forces actor `A`, no source `.consume` step at `B` exists to be built.
`DTR.GeneralActorSelection.selectedActor_unique` sharpens this rather than relieving it: under the
priority guard the source schedule is *forced*. That is what F86's tail means by "the backward direction
needs the DTR side's own within-instant modulo".

## What this module does instead

No source quotient, and no change to either semantics. The route around the obstruction is that
`Correctness.generalConsumeBlockMatch` is **per reactor** and constrains no cross-reactor interleaving:
a backward-constructed source block may consume in the *source's own* priority order and still match,
provided each source step takes that actor's next-unconsumed target occurrence.

What that needs is not a quotient but a **source-readiness fact** — at each point of the instant, the
actor the source selects exists and has an unconsumed target occurrence at the current time. This module
derives exactly that from the correspondence, `readyActors` and `earliestDueArrival`, with no new
premise about scheduling.

Whether the derived fact is *sufficient* to structure the wrapper is a separate question, and the
concluding section of this module records what is still missing. The facts below are worth having either
way: they are the backward direction's counterpart of the forward direction's environment inversion, and
they are what any backward `.consume` core lemma will need in order to produce its `take`.

Nothing here weakens F27, adds an ordering premise, uses α to repair ordering, or touches
`GeneralStateCorrespondence`.
-/
import Relico.Correctness.GeneralInstantBlockForward
import Relico.Correctness.GeneralSameReactorOrder

set_option autoImplicit false

namespace Relico

namespace DTR

/-!
## Membership through continuation erasure

`selectedActor` and `readyActors` are stated over `DTR.GeneralConfiguration`, the continuation-free
projection, while the correspondence is stated over `DTR.GeneralRuntimeConfiguration`. Crossing that
boundary by *lookup* is already available (`eraseContinuations_lookup`), but the readiness cohort's
completeness theorem is **membership**-shaped, and membership is the stronger fact — so the lookup lemma
cannot serve. This is the missing direction.
-/

/--
Erasure preserves membership, keeping the key and dropping only the continuation.

The companion of `eraseContinuations_lookup`, in the shape `DTR.readyActors_complete` reads. Needed
rather than merely convenient: `readyActors_complete` takes `(actorName, state) ∈ config.actors`, and
deriving membership from a lookup is unsound in general — `Store.lookup` sees only the first binding at
a key, which is the whole reason the store-key uniqueness layer exists.

The same induction `eraseContinuations_lookup` uses, without the case split, since membership needs no
decision about the key.
-/
theorem eraseContinuations_mem
    {actors :
      Store ActorName DTR.GeneralActorRuntime}
    {name : ActorName}
    {actor : DTR.GeneralActorRuntime}
    (hMember :
      (name, actor) ∈ actors) :
    (name, actor.state) ∈
      eraseContinuations actors := by

  induction actors with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨headName, headActor⟩

      rcases List.mem_cons.mp hMember with
        hHead |
          hTail

      · obtain ⟨hName, hActor⟩ :=
          Prod.mk.inj hHead

        subst hName

        subst hActor

        exact List.mem_cons_self

      · exact
          List.mem_cons_of_mem
            _
            (inductionHypothesis hTail)

/--
Erasure reflects membership: an erased binding names a runtime actor.

The converse direction of `eraseContinuations_mem`, needed because the readiness cohort is computed on
the erased configuration while the correspondence's fields live on runtime actors. `DTR.readyActors_sound`
hands back an erased state, and this is what turns it into the runtime record whose bag the pairing talks
about.

Existential in the actor rather than functional, and that is not slack: the erasure is not injective on
records — two runtime actors differing only in `activeBody` erase to the same state — so no function
inverts it. What the caller needs is a runtime actor with *that* state, which is exactly what is
returned.
-/
theorem exists_of_mem_eraseContinuations
    {actors :
      Store ActorName DTR.GeneralActorRuntime}
    {name : ActorName}
    {state : DTR.GeneralActorState}
    (hMember :
      (name, state) ∈
        eraseContinuations actors) :
    ∃ actor : DTR.GeneralActorRuntime,
      (name, actor) ∈ actors ∧
        actor.state = state := by

  induction actors with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨headName, headActor⟩

      rcases List.mem_cons.mp hMember with
        hHead |
          hTail

      · obtain ⟨hName, hState⟩ :=
          Prod.mk.inj hHead

        subst hName

        exact
          ⟨headActor,
           List.mem_cons_self,
           hState.symm⟩

      · obtain ⟨actor, hActorMember, hActorState⟩ :=
          inductionHypothesis hTail

        exact
          ⟨actor,
           List.mem_cons_of_mem
             _
             hActorMember,
           hActorState⟩

/-!
## Readiness from one due message

The cohort layer proves completeness in terms of `GeneralActorState.dueArrival`, and the bag layer
proves that a due message makes `earliestDueArrival` answer. Composing the two at the runtime
configuration is what turns "this actor holds a message that has arrived" into "the source has a step
to take", which is the fact the backward direction needs and the source semantics does not state.
-/

/--
An actor holding a message at or before the clock makes the source's selection answer.

Three links, none of which is a restatement: `earliestDueArrival_complete` says a due message makes the
bag's minimum exist, `readyActors_complete` puts the actor in the cohort carrying that minimum, and
`selectedActor_isSome_iff` turns a non-empty cohort into an answer.

The selected actor is **not** claimed to be this one. It cannot be — priority decides, and that is
precisely the determinism the backward direction has to work around rather than through. What is claimed
is only that the source is not stuck, which is what lets a backward construction proceed at all.
-/
theorem selectedActor_isSome_of_dueMessage
    {model : DTR.GeneralModel}
    {config : GeneralRuntimeConfiguration}
    {name : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {message : DTR.GeneralMessage}
    (hMember :
      (name, actor) ∈ config.actors)
    (hMessage :
      message ∈ actor.state.bag)
    (hDue :
      message.arrival ≤ config.now) :
    ∃ selected :
        GlobalMultiStorePayloadActorPriority.ReadyActor,
      GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected := by

  obtain ⟨arrival, hArrival⟩ :=
    earliestDueArrival_complete
      actor.state.bag
      config.now
      message
      hMessage
      hDue

  have hDueArrival :
      GeneralActorState.dueArrival
          actor.state
          config.erase.now =
        some arrival := by
    unfold GeneralActorState.dueArrival

    rw [
      GeneralRuntimeConfiguration.erase_now
    ]

    exact hArrival

  have hCohortMember :
      (
        {
          actorName := name
          logicalTime := arrival
        } :
          GlobalMultiStorePayloadActorPriority.ReadyActor
      ) ∈
        config.erase.readyActors :=
    readyActors_complete
      config.erase
      name
      actor.state
      arrival
      (by
        rw [
          GeneralRuntimeConfiguration.erase_actors
        ]

        exact
          eraseContinuations_mem
            hMember)
      hDueArrival

  have hCohortNonempty :
      config.erase.readyActors ≠ [] := by
    intro hEmpty

    rw [hEmpty] at hCohortMember

    cases hCohortMember

  exact
    Option.isSome_iff_exists.mp
      ((GeneralActorSelection.selectedActor_isSome_iff
        model
        config.erase).mpr
        hCohortNonempty)

end DTR

namespace Correctness

/-!
## The derivation

Two theorems. The first crosses from a target event at the current instant to the source's own
selection answering; the second crosses back, from whatever actor the source selected to an unconsumed
target event for it. Together they are the source-readiness fact the audit named.
-/

/--
**A target event at the current instant makes the source's selection answer.**

The correspondence's `pendingTargeted` field supplies the actor the event names, `reactorOfActor`
supplies that actor's `GeneralPendingAgrees`, and `generalPendingAgrees_message_of_event` — the
backward accessor of the pairing — supplies a message in its bag at the event's own instant. The
`logicalTime` field converts the event's tag time into the source clock, and
`DTR.selectedActor_isSome_of_dueMessage` finishes.

`hEventTime` is at the *current* instant rather than merely due, because that is what a block entry
gives: `GeneralInstantBlockSpine`'s `consume` fires at the tag it is anchored to. Dueness is all the
readiness computation needs, so the premise is weakened to `≤` inside the proof rather than at the
boundary.

**This says nothing about which actor is selected**, and that is not an omission this theorem can
repair. See the closing section.
-/
theorem generalSelectedActor_isSome_of_targetEvent
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {event : LF.GeneralPendingEvent}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hEvent :
      event ∈ state.pending)
    (hEventTime :
      event.tag.time =
        state.currentTag.time) :
    ∃ selected :
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor,
      DTR.GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected := by

  obtain ⟨actor, hActorMember⟩ :=
    hCorrespondence.pendingTargeted
      event
      hEvent

  obtain ⟨_, _, _, _, hPair⟩ :=
    hCorrespondence.reactorOfActor
      event.target
      actor
      hActorMember

  obtain ⟨message, hMessageMember, hArrival⟩ :=
    generalPendingAgrees_message_of_event
      event.target
      actor.state.bag
      state.pending
      hPair.messages
      event
      hEvent
      rfl

  refine
    DTR.selectedActor_isSome_of_dueMessage
      hActorMember
      hMessageMember
      ?_

  rw [
    hArrival,
    hEventTime,
    hCorrespondence.logicalTime
  ]

  exact
    Nat.le_refl
      config.now

/--
**Any actor with a due message has an unconsumed target event of its own.**

The other half, and the one that makes the pair a readiness statement rather than a liveness one.
`earliestDueArrival_sound` exhibits the bag message realizing the due arrival, and
`generalPendingAgrees_event_of_message` — the forward accessor of the pairing — turns that message into
a pending target event aimed at the actor.

**Callers instantiate this at the actor the source selected**, which is how it composes with
`generalSelectedActor_isSome_of_targetEvent` above: that theorem produces a selection,
`DTR.GeneralActorSelection.selectedActor_mem` with `DTR.readyActors_sound` turn the selection into a due
arrival, and this theorem turns the due arrival into a target event. The selection is deliberately
**not** a premise: nothing in the proof consults priority, and carrying a hypothesis the proof does not
use would misrepresent where the content lies. Stated over the runtime configuration rather than the
erased one because the pairing lives on runtime actors.

The event is returned with its target and its tag time — what a spine entry's `hTag` and a match's
`GeneralConsumeMatch` compare against. Its **kind** is deliberately not mentioned: F78 forbids computing
a kind from a message, and the backward direction has no more licence to do so than the forward one had.
-/
theorem generalEvent_of_dueActor
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {name : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {arrival : LogicalTime}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hRuntime :
      (name, actor) ∈ config.actors)
    (hBag :
      DTR.GeneralActorState.dueArrival
          actor.state
          config.now =
        some arrival) :
    ∃ event : LF.GeneralPendingEvent,
      event ∈ state.pending ∧
        event.target = name ∧
        event.tag.time = arrival := by

  obtain ⟨message, hMessageMember, _, _⟩ :=
    DTR.earliestDueArrival_sound
      actor.state.bag
      config.now
      arrival
      hBag

  obtain ⟨_, _, _, _, hPair⟩ :=
    hCorrespondence.reactorOfActor
      name
      actor
      hRuntime

  obtain ⟨event, hEventMember, hTarget, hTime⟩ :=
    generalPendingAgrees_event_of_message
      name
      actor.state.bag
      state.pending
      hPair.messages
      message
      hMessageMember

  exact
    ⟨event,
     hEventMember,
     hTarget,
     by
       rw [hTime]
       omega⟩

/--
**The source-readiness fact, composed: whenever the target has instant work, the source has a step to
take, and the actor it will take it at has a target event of its own.**

The derivation the backward audit set out to attempt, and the strongest form it reaches. Both halves
above are spent: the first turns the target's pending event into a source selection, and the second turns
that selection back into a target event for the *selected* actor — going through
`selectedActor_mem` to put the selection in the cohort, `readyActors_sound` to read off its erased state
and due arrival, and `exists_of_mem_eraseContinuations` to recover the runtime actor the pairing needs.

**What it gives the backward wrapper.** At every point of a target instant block the source is not
stuck, and the step it is about to take is not spurious — the actor it fires has genuine target work at
the same instant, so a constructed source block never consumes a message the target never delivered.
That is the soundness half of the per-step agreement.

**What it does not give, and cannot.** The returned event need not be the block's *current* occurrence.
It is an event for whichever actor priority selected, and the target's fire order is its own; the two
orders differ, which is F76's measured divergence. Nothing derivable from `readyActors` can close that,
because `readyActors` does not mention the target at all. The consequence for the wrapper is worked out
in the closing section.

`hEventTime` is at the current tag because that is what a `GeneralInstantBlockSpine` entry supplies.
No premise about ordering, no α, no source quotient.
-/
theorem generalSourceReadiness_of_targetEvent
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {event : LF.GeneralPendingEvent}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hEvent :
      event ∈ state.pending)
    (hEventTime :
      event.tag.time =
        state.currentTag.time) :
    ∃ (selected :
        DTR.GlobalMultiStorePayloadActorPriority.ReadyActor)
      (actor : DTR.GeneralActorRuntime)
      (selectedEvent : LF.GeneralPendingEvent),
      DTR.GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected ∧
        (selected.actorName, actor) ∈ config.actors ∧
        DTR.GeneralActorState.dueArrival
            actor.state
            config.now =
          some selected.logicalTime ∧
        selectedEvent ∈ state.pending ∧
        selectedEvent.target = selected.actorName ∧
        selectedEvent.tag.time = selected.logicalTime := by

  obtain ⟨selected, hSelected⟩ :=
    generalSelectedActor_isSome_of_targetEvent
      hCorrespondence
      hEvent
      hEventTime

  obtain ⟨erasedState, hErasedMember, hDueArrival⟩ :=
    DTR.readyActors_sound
      config.erase
      selected
      (DTR.GeneralActorSelection.selectedActor_mem
        hSelected)

  obtain ⟨actor, hActorMember, hActorState⟩ :=
    DTR.exists_of_mem_eraseContinuations
      (by
        rw [
          ← DTR.GeneralRuntimeConfiguration.erase_actors
        ]

        exact hErasedMember)

  have hBag :
      DTR.GeneralActorState.dueArrival
          actor.state
          config.now =
        some selected.logicalTime := by
    rw [
      hActorState
    ]

    rw [
      DTR.GeneralRuntimeConfiguration.erase_now
    ] at hDueArrival

    exact hDueArrival

  obtain ⟨selectedEvent, hSelectedMember, hSelectedTarget, hSelectedTime⟩ :=
    generalEvent_of_dueActor
      hCorrespondence
      hActorMember
      hBag

  exact
    ⟨selected,
     actor,
     selectedEvent,
     hSelected,
     hActorMember,
     hBag,
     hSelectedMember,
     hSelectedTarget,
     hSelectedTime⟩

/-!
## The backward `.consume` core lemma

The derivation above settles the existence half of the per-step actor agreement and demonstrably cannot
settle the ordering half. So the ordering half becomes a **premise**, exactly as the forward direction's
α-representative package is a premise of
`Correctness.generalConsume_forward_weak_of_fireRepresentative`. Both residues are per-step, both are
named, and neither is faked.

**One observation shapes the statement, and it is worth recording.** The post-state *correspondence* is
**direction-agnostic**: it relates one source post-configuration to one target post-state, and which
side was given first is not part of that claim. The forward core lemma already proves it from local
content. So the backward core lemma's genuinely new content is only the **source step construction**,
and the correspondence half is the forward core's conclusion reused verbatim rather than reproved. That
is why this lemma is short, and the shortness is the finding rather than a gap.
-/

/--
**Backward, at the `.consume` label, under the light within-tag quotient — the core lemma.**

Given a target fire's local content at a corresponding pair, and given the source scheduler's own answer
at that configuration together with the per-step agreement that it names the fired reactor, the source
takes the matched message — and the answered pair still corresponds.

**The residue, stated plainly.** `hName : selected.actorName = actorName` is the per-step actor
agreement, and it is a **premise** because it is not derivable: `DTR.GeneralActorSelection.selectedActor`
is a function of the source configuration alone — `readyActors` and `earliestDueArrival` never mention
the target program, its queue, or its fire order — so nothing over them can conclude that source priority
selects the reactor the target fired. `DTR.GeneralActorSelection.selectedActor_unique` sharpens this
rather than relieving it: under the priority guard the source schedule is *forced*. This is F76's
measured cross-actor divergence and what F86's tail means by "the backward direction needs the DTR side's
own within-instant modulo".

`hName` mentions **one** actor at **one** configuration. It encodes no list, no global order, and no
relation between the two sides' interleavings — the block match is per-reactor precisely so that none is
needed. No scheduler semantics is added, no source quotient is introduced, and F27 is not weakened: the
choice of *which occurrence* in the bag is still free, and `hDue`'s `earlier ++ message :: later` split
is that freedom being used.

**The premise package is not vacuous**, and `Correctness.generalSourceReadiness_of_targetEvent` above is
the soundness companion that shows it: whenever the target has instant work the source's selection does
answer, and the actor it answers with does have a target event at the same instant. That is supporting
evidence, **not** a replacement — it cannot produce `hName`, and this lemma does not pretend it can.

**What the two conjuncts are.** The first is `DTR.take_of_split` at the supplied package: the source
`.consume` step, at `take`'s own post-configuration literal. The second is
`generalConsume_forward_weak_of_fireRepresentative` unchanged — the target's modulo weak step at the
fired event's label together with the full post-state correspondence. Nothing is reproved, and the
target-side premises are passed through in the shape that lemma fixed, including `hUniqueT` **at the
representative** (not at `state`): transporting store-key uniqueness across α would be unsound, so it is
not transported.

Both `.consume` labels are the ones each semantics actually emits, and the target's kind is read off the
fired event as always — never computed from a payload. F78.
-/
theorem generalConsume_backward_weak_of_takeRepresentative
    (program : LF.GeneralProgram)
    (model : DTR.GeneralModel)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (actorName : ActorName)
    (actor : DTR.GeneralActorRuntime)
    (message : DTR.GeneralMessage)
    (earlier later : DTR.GeneralMessageBag)
    (hDue :
      actor.state.bag =
        earlier ++ message :: later)
    (server : DTR.GeneralMessageServer)
    (event : LF.GeneralPendingEvent)
    (hMatch :
      GeneralConsumeMatch
        actorName
        message
        event)
    (hEventTime :
      event.tag.time =
        state.currentTag.time)
    (selected :
      DTR.GlobalMultiStorePayloadActorPriority.ReadyActor)
    (hSelected :
      DTR.GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected)
    (hName :
      selected.actorName = actorName)
    (hActor :
      Store.lookup config.actors actorName =
        some actor)
    (hIdle :
      actor.idle = true)
    (hArrival :
      message.arrival = selected.logicalTime)
    (hServer :
      DTR.GeneralModel.messageServerFor?
          model
          actorName
          message.messageName =
        some server)
    (aligned : LF.GeneralRuntimeState)
    (hAlignSteps :
      Common.TauSteps
        (LF.GeneralStep program)
        LF.GeneralLabel.isTau
        state
        aligned)
    (hAlignedReactors :
      aligned.reactors = state.reactors)
    (hAlignedPending :
      aligned.pending = state.pending)
    (before : LF.GeneralRuntimeState)
    (hAlpha :
      LF.generalStateAlphaEquiv
        before
        aligned)
    (hEarliest :
      LF.GeneralRuntimeState.earliestPendingEvent?
          before =
        some event)
    (hTagAligned :
      event.tag = before.currentTag)
    (earlier' later' : LF.GeneralEventQueue)
    (hQueue :
      before.pending =
        earlier' ++ event :: later')
    (reactorRT : LF.GeneralReactorRuntime)
    (hUniqueT :
      before.reactors.filter
          (fun entry =>
            decide (entry.1 = event.target)) =
        [(event.target, reactorRT)])
    (hReactorBefore :
      Store.lookup
          before.reactors
          event.target =
        some reactorRT)
    (hIdleRT :
      reactorRT.idle = true)
    (reaction : LF.GeneralReaction)
    (hReaction :
      LF.GeneralProgram.reactionFor?
          program
          event.target
          event.kind =
        some reaction)
    (hParams :
      reaction.parameters =
        server.parameters.map
          (fun parameter =>
            parameter.name))
    (env : Translation.GeneralOutputPortEnv)
    (hEnv :
      outputPortEnvOfActorName model actorName =
        some env)
    (hBody :
      GeneralContinuationCompiles
        env
        server.body
        reaction.body)
    (hUniqueS :
      config.actors.filter
          (fun entry =>
            decide (entry.1 = actorName)) =
        [(actorName, actor)])
    (hPaired :
      GeneralActorCorresponds
        env
        actorName
        actor
        reactorRT
        state.pending) :
    DTR.GeneralStep
        model
        config
        (DTR.GeneralLabel.consume
          actorName
          message)
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
                      DTR.bindParameters
                        server.parameters
                        message.payload
                        actor.state.valuation

                    bag := earlier ++ later
                  }

                activeBody := server.body
              }
        } ∧
      Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          (LF.GeneralLabel.consume
            event.target
            event.kind)
          {
          currentTag := before.currentTag

          reactors :=
            Store.update
              before.reactors
              event.target
              {
                valuation :=
                  LF.bindReactionParameters
                    reaction.parameters
                    event.payload
                    reactorRT.valuation

                activeBody := reaction.body
              }

          pending := earlier' ++ later'
        } ∧
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
                      DTR.bindParameters
                        server.parameters
                        message.payload
                        actor.state.valuation

                    bag := earlier ++ later
                  }

                activeBody := server.body
              }
        }
          {
          currentTag := before.currentTag

          reactors :=
            Store.update
              before.reactors
              event.target
              {
                valuation :=
                  LF.bindReactionParameters
                    reaction.parameters
                    event.payload
                    reactorRT.valuation

                activeBody := reaction.body
              }

          pending := earlier' ++ later'
        } := by

  refine
    ⟨DTR.take_of_split
       hSelected
       hName
       hActor
       hIdle
       hDue
       hArrival
       hServer,
     ?_⟩

  exact
    generalConsume_forward_weak_of_fireRepresentative
      program
      model
      config
      state
      hCorrespondence
      actorName
      actor
      message
      earlier
      later
      hDue
      server
      event
      hMatch
      hEventTime
      aligned
      hAlignSteps
      hAlignedReactors
      hAlignedPending
      before
      hAlpha
      hEarliest
      hTagAligned
      earlier'
      later'
      hQueue
      reactorRT
      hUniqueT
      hReactorBefore
      hIdleRT
      reaction
      hReaction
      hParams
      env
      hEnv
      hBody
      hUniqueS
      hPaired

/--
The core lemma packaged as **weak** steps on both sides, which is the shape a block induction consumes.

`Common.WeakSteps.cons` takes a `Common.WeakStep`, and the source's `.consume` is a bare
`DTR.GeneralStep` — so the block's per-entry obligation is this, not the lemma above. `Common.WeakStep.of_step`
supplies the padding, and it is empty at both ends: a source take needs no administrative traffic around
it, and claiming exactly one step is **stronger** than claiming a padded one. Genuine padding is owed only
on the *target* side, where P24 measured that a zero-delay send costs a microstep the source does not
take — and that padding is already inside the target half, carried by `hAlignSteps`.

**Both endpoints are pinned at the rule literals, not existential.** The spine induction's tail is
indexed at the specific `fireResult` state, so an anonymous endpoint cannot feed the induction
hypothesis — the pin is what lets this thread. Both literals are `take`'s and `fire`'s own outputs, so
nothing is re-derived: a caller pattern-matches and moves on.

**`hUniqueS` is the whole-store invariant here, not the filter singleton the core lemma reads.** Two
reasons, and both are about the caller. The filter form is derived on the spot by
`DTR.generalStoreKeyUnique_filter_of_lookup`, so nothing is lost; and the invariant is what a block
induction actually carries between entries, since `DTR.generalStoreKeyUnique_of_step` is what
re-establishes it — which is also why it is returned as a fourth conjunct rather than left for the caller
to recover.
-/
theorem generalConsume_backward_weakStep_of_takeRepresentative
    (program : LF.GeneralProgram)
    (model : DTR.GeneralModel)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (actorName : ActorName)
    (actor : DTR.GeneralActorRuntime)
    (message : DTR.GeneralMessage)
    (earlier later : DTR.GeneralMessageBag)
    (hDue :
      actor.state.bag =
        earlier ++ message :: later)
    (server : DTR.GeneralMessageServer)
    (event : LF.GeneralPendingEvent)
    (hMatch :
      GeneralConsumeMatch
        actorName
        message
        event)
    (hEventTime :
      event.tag.time =
        state.currentTag.time)
    (selected :
      DTR.GlobalMultiStorePayloadActorPriority.ReadyActor)
    (hSelected :
      DTR.GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected)
    (hName :
      selected.actorName = actorName)
    (hActor :
      Store.lookup config.actors actorName =
        some actor)
    (hIdle :
      actor.idle = true)
    (hArrival :
      message.arrival = selected.logicalTime)
    (hServer :
      DTR.GeneralModel.messageServerFor?
          model
          actorName
          message.messageName =
        some server)
    (aligned : LF.GeneralRuntimeState)
    (hAlignSteps :
      Common.TauSteps
        (LF.GeneralStep program)
        LF.GeneralLabel.isTau
        state
        aligned)
    (hAlignedReactors :
      aligned.reactors = state.reactors)
    (hAlignedPending :
      aligned.pending = state.pending)
    (before : LF.GeneralRuntimeState)
    (hAlpha :
      LF.generalStateAlphaEquiv
        before
        aligned)
    (hEarliest :
      LF.GeneralRuntimeState.earliestPendingEvent?
          before =
        some event)
    (hTagAligned :
      event.tag = before.currentTag)
    (earlier' later' : LF.GeneralEventQueue)
    (hQueue :
      before.pending =
        earlier' ++ event :: later')
    (reactorRT : LF.GeneralReactorRuntime)
    (hUniqueT :
      before.reactors.filter
          (fun entry =>
            decide (entry.1 = event.target)) =
        [(event.target, reactorRT)])
    (hReactorBefore :
      Store.lookup
          before.reactors
          event.target =
        some reactorRT)
    (hIdleRT :
      reactorRT.idle = true)
    (reaction : LF.GeneralReaction)
    (hReaction :
      LF.GeneralProgram.reactionFor?
          program
          event.target
          event.kind =
        some reaction)
    (hParams :
      reaction.parameters =
        server.parameters.map
          (fun parameter =>
            parameter.name))
    (env : Translation.GeneralOutputPortEnv)
    (hEnv :
      outputPortEnvOfActorName model actorName =
        some env)
    (hBody :
      GeneralContinuationCompiles
        env
        server.body
        reaction.body)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hPaired :
      GeneralActorCorresponds
        env
        actorName
        actor
        reactorRT
        state.pending) :
    Common.WeakStep
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        (DTR.GeneralLabel.consume
          actorName
          message)
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
                      DTR.bindParameters
                        server.parameters
                        message.payload
                        actor.state.valuation

                    bag := earlier ++ later
                  }

                activeBody := server.body
              }
        } ∧
      Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          (LF.GeneralLabel.consume
            event.target
            event.kind)
          {
          currentTag := before.currentTag

          reactors :=
            Store.update
              before.reactors
              event.target
              {
                valuation :=
                  LF.bindReactionParameters
                    reaction.parameters
                    event.payload
                    reactorRT.valuation

                activeBody := reaction.body
              }

          pending := earlier' ++ later'
        } ∧
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
                      DTR.bindParameters
                        server.parameters
                        message.payload
                        actor.state.valuation

                    bag := earlier ++ later
                  }

                activeBody := server.body
              }
        }
          {
          currentTag := before.currentTag

          reactors :=
            Store.update
              before.reactors
              event.target
              {
                valuation :=
                  LF.bindReactionParameters
                    reaction.parameters
                    event.payload
                    reactorRT.valuation

                activeBody := reaction.body
              }

          pending := earlier' ++ later'
        } ∧
        DTR.GeneralStoreKeyUnique
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
                      DTR.bindParameters
                        server.parameters
                        message.payload
                        actor.state.valuation

                    bag := earlier ++ later
                  }

                activeBody := server.body
              }
        } := by

  obtain ⟨hTake, hTargetStep, hPostCorrespondence⟩ :=
    generalConsume_backward_weak_of_takeRepresentative
      program
      model
      config
      state
      hCorrespondence
      actorName
      actor
      message
      earlier
      later
      hDue
      server
      event
      hMatch
      hEventTime
      selected
      hSelected
      hName
      hActor
      hIdle
      hArrival
      hServer
      aligned
      hAlignSteps
      hAlignedReactors
      hAlignedPending
      before
      hAlpha
      hEarliest
      hTagAligned
      earlier'
      later'
      hQueue
      reactorRT
      hUniqueT
      hReactorBefore
      hIdleRT
      reaction
      hReaction
      hParams
      env
      hEnv
      hBody
      (DTR.generalStoreKeyUnique_filter_of_lookup
        hUniqueS
        hActor)
      hPaired

  exact
    ⟨Common.WeakStep.of_step
       hTake,
     hTargetStep,
     hPostCorrespondence,
     DTR.generalStoreKeyUnique_of_step
       hUniqueS
       hTake⟩

/-!
## Endpoint transport: the source's quiescence and idleness, from the target's

The forward wrapper deliberately **discarded** the block endpoint conditions, and its docstring records
that transporting them is genuine unproved work. In the backward direction they turn out to be
**derivable**, and the asymmetry is worth stating because it is not an accident of effort.

`GeneralInstantBlockSpine.nil` carries `hFuture` — every pending target event is strictly after the
instant — and `hIdle` — every reactor is idle. Both cross to the source along the *direction the
correspondence supports*:

* **Quiescence** crosses because a *ready source actor* is backed by a *pending target event at or before
  the instant* (`generalPendingAgrees_event_of_message`), which `hFuture` forbids. The forward direction
  needed the opposite implication — from source quiescence to target futureness — and the pairing does not
  run that way without knowing the queue holds nothing else.
* **Idleness** crosses because a compiled body is `nil` only if its source body was: `compileGeneralBody`
  maps a `cons` to a `cons` whenever it succeeds at all.

So the backward wrapper can conclude the **whole** `Correctness.generalInstantBlock_source` predicate,
where the forward wrapper could only conclude a `Common.WeakSteps`. That is the payoff of the target block
being the given side.
-/

/--
A compiled body is empty only if its source body was.

The inversion behind idleness transport. `Translation.compileGeneralBody` sends `[]` to `.ok []` and sends
`statement :: remaining` to either an error or `.ok (compiled :: compiledRemaining)` — never to `.ok []`,
because a successful statement compilation contributes exactly one target statement. So an empty compiled
body forces an empty source body.

Stated over the raw compiler rather than over `GeneralContinuationCompiles` so that the relation's
existentials do not have to be opened twice; the wrapper's consumer is the corollary below.
-/
private theorem compileGeneralBody_eq_nil
    {env : Translation.GeneralOutputPortEnv}
    {context : Translation.GeneralBodyContext}
    {index : Nat}
    {source : DTR.GeneralBody}
    (hCompiled :
      Translation.compileGeneralBody
          env
          context
          index
          source =
        .ok []) :
    source = [] := by

  cases source with

  | nil =>
      rfl

  | cons statement remaining =>
      unfold Translation.compileGeneralBody at hCompiled

      cases hStatement :
          Translation.compileGeneralStmt
            env
            context
            index
            statement with

      | error diagnostic =>
          rw [hStatement] at hCompiled

          simp at hCompiled

      | ok compiledStatement =>
          rw [hStatement] at hCompiled

          cases hRemaining :
              Translation.compileGeneralBody
                env
                context
                (index + 1)
                remaining with

          | error diagnostic =>
              rw [hRemaining] at hCompiled

              simp at hCompiled

          | ok compiledRemaining =>
              rw [hRemaining] at hCompiled

              simp at hCompiled

/--
An idle reactor's actor is idle.

Idleness is `activeBody.isEmpty` on both sides, and the correspondence's `continuation` field is a
compilation of the source body into the target body — so `compileGeneralBody_eq_nil` closes it. This is
what carries `GeneralInstantBlockSpine.nil`'s `hIdle` to the source block predicate's own all-idle
endpoint.

No well-formedness premise, and no appeal to the model: emptiness of a compiled body is a fact about the
compiler alone.
-/
theorem generalActorIdle_of_reactorIdle
    {env : Translation.GeneralOutputPortEnv}
    {name : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {reactor : LF.GeneralReactorRuntime}
    {pending : LF.GeneralEventQueue}
    (hCorresponds :
      GeneralActorCorresponds
        env
        name
        actor
        reactor
        pending)
    (hIdle :
      LF.GeneralReactorRuntime.idle reactor = true) :
    DTR.GeneralActorRuntime.idle actor = true := by

  obtain ⟨context, index, hCompiled, _⟩ :=
    hCorresponds.continuation

  have hTargetNil :
      reactor.activeBody = [] := by
    unfold LF.GeneralReactorRuntime.idle at hIdle

    exact
      List.isEmpty_iff.mp hIdle

  rw [hTargetNil] at hCompiled

  unfold DTR.GeneralActorRuntime.idle

  rw [
    compileGeneralBody_eq_nil
      hCompiled
  ]

  rfl

/--
**The source has no ready actor when every pending target event is strictly future.**

The quiescence half of endpoint transport, and the direction the pairing genuinely supports. A ready
source actor holds a message due at or before `now`; `generalPendingAgrees_event_of_message` turns that
message into a pending target event at the message's own arrival; `logicalTime` puts that arrival at or
before the target's current time; and `hFuture` says every pending event is strictly after it. The two
cannot both hold, so the cohort is empty.

Contrast `Correctness.generalQuiescent_of_earliestPendingEventFuture`, which derives the same conclusion
from the target's *selection* being future. That form needs the queue to be non-empty to have a selection
at all; this one is stated over the `hFuture` predicate a `GeneralInstantBlockSpine.nil` actually carries,
so it covers the empty queue with no case split.

`DTR.mem_eraseContinuations` is the bridge from the cohort's erased store to the runtime actor the pairing
talks about.
-/
theorem generalQuiescent_of_pendingFuture
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hFuture :
      ∀ event ∈ state.pending,
        state.currentTag.time < event.tag.time) :
    DTR.GeneralConfiguration.readyActors config.erase =
      [] := by

  cases hReady :
      DTR.GeneralConfiguration.readyActors config.erase with

  | nil =>
      rfl

  | cons ready rest =>

      exfalso

      have hReadyMember :
          ready ∈
            DTR.GeneralConfiguration.readyActors config.erase := by
        rw [hReady]

        exact List.mem_cons_self

      obtain ⟨erasedState, hErasedMember, hDueArrival⟩ :=
        DTR.readyActors_sound
          config.erase
          ready
          hReadyMember

      obtain ⟨actor, hActorMember, hActorState⟩ :=
        DTR.mem_eraseContinuations
          config.actors
          ready.actorName
          erasedState
          hErasedMember

      obtain ⟨message, hMessageMember, hMessageArrival, hMessageDue⟩ :=
        DTR.earliestDueArrival_sound
          erasedState.bag
          config.erase.now
          ready.logicalTime
          hDueArrival

      obtain ⟨_, _, _, _, hPair⟩ :=
        hCorrespondence.reactorOfActor
          ready.actorName
          actor
          hActorMember

      obtain ⟨event, hEventMember, _, hEventTime⟩ :=
        generalPendingAgrees_event_of_message
          ready.actorName
          actor.state.bag
          state.pending
          hPair.messages
          message
          (by
            rw [hActorState]

            exact hMessageMember)

      have hStrict :
          state.currentTag.time < event.tag.time :=
        hFuture
          event
          hEventMember

      rw [
        hEventTime,
        hMessageArrival,
        hCorrespondence.logicalTime
      ] at hStrict

      rw [
        DTR.GeneralRuntimeConfiguration.erase_now
      ] at hMessageDue

      -- Explicit `Nat` lemma rather than `omega`: F72 measured that `omega` does not see through the
      -- `LogicalTime` abbreviation, and here it reports no usable constraints.
      exact
        absurd
          hStrict
          (Nat.not_lt.mpr
            hMessageDue)

/-!
## A τ closure keeps the logical time

`tauSteps_time_eq` in `Relico/Correctness/GeneralInstantBlock.lean` is `private`, so this is the local
twin, and so is the label-refutation it needs. P24's discipline at the closure level: internal activity may
move microsteps but never logical time, which is what keeps a block inside its instant.
-/

/--
A τ-labelled step's label is `tau`.

`LF.GeneralLabel.isTau` is a `match` returning `True` only at `tau`, so the two visible labels are refuted
rather than defaulted. Needed because `LF.GeneralStep.now_eq_of_tau` is stated at the literal label while
`Common.TauSteps.cons` carries the predicate.
-/
private theorem label_eq_tau_of_isTauLocal
    {label : LF.GeneralLabel}
    (hTau :
      LF.GeneralLabel.isTau label) :
    label = LF.GeneralLabel.tau := by

  cases label with

  | tau =>
      rfl

  | timeAdvance before after =>
      exact
        absurd
          hTau
          (LF.GeneralLabel.not_isTau_timeAdvance
            before
            after)

  | consume target kind =>
      exact
        absurd
          hTau
          (LF.GeneralLabel.not_isTau_consume
            target
            kind)

/--
A τ closure preserves the target's logical time.

`LF.GeneralStep.now_eq_of_tau` lifted to `Common.TauSteps`. Stated on `currentTag.time` because that is the
component the spine's anchoring premises are about; the microstep is deliberately free, since a zero-delay
send advances it and stays inside the instant.
-/
private theorem tauSteps_time_eqLocal
    {program : LF.GeneralProgram}
    {state state' : LF.GeneralRuntimeState}
    (hSteps :
      Common.TauSteps
        (LF.GeneralStep program)
        LF.GeneralLabel.isTau
        state
        state') :
    state'.currentTag.time =
      state.currentTag.time := by

  induction hSteps with

  | refl current =>
      rfl

  | cons headStep headIsTau remainingSteps IH =>
      rw [
        label_eq_tau_of_isTauLocal
          headIsTau
      ] at headStep

      exact
        IH.trans
          (LF.GeneralStep.now_eq_of_tau
            headStep)

/-!
## The block match, extended one occurrence at a time

`generalConsumeBlockMatch_cons` in `Relico/Correctness/GeneralInstantBlockForward.lean` is `private`, so
this is the local twin. The house rule prefers duplicating a small lemma over de-privatising one, and the
duplication is deliberate: the forward file's copy is consumed by the forward induction and this one by the
backward induction, so a later change to either direction breaks only its own copy.
-/

/--
Extending a block match by one matched occurrence.

Case split on whether the actor is the consuming one; both branches are decided by the single fact that
the answer's `GeneralConsumeMatch` carries, namely `event.target = receiver`, so the two extractions cannot
disagree about which of them keeps the new element.

**No cross-reactor content.** One actor at a time, so nothing is said about how this occurrence is ordered
against another reactor's — the property the block match exists to leave free.
-/
private theorem generalConsumeBlockMatch_consLocal
    {receiver : ActorName}
    {message : DTR.GeneralMessage}
    {event : LF.GeneralPendingEvent}
    {labels : List DTR.GeneralLabel}
    {occurrences : List LF.GeneralPendingEvent}
    (hMatch :
      GeneralConsumeMatch
        receiver
        message
        event)
    (hRest :
      generalConsumeBlockMatch
        labels
        occurrences) :
    generalConsumeBlockMatch
      (DTR.GeneralLabel.consume
          receiver
          message ::
        labels)
      (event :: occurrences) := by

  intro actor

  have hTarget :
      event.target = receiver :=
    hMatch.1

  by_cases hActor :
      actor = receiver

  · subst hActor

    have hSource :
        sourceConsumesAt
            actor
            (DTR.GeneralLabel.consume
                actor
                message ::
              labels) =
          message ::
            sourceConsumesAt
              actor
              labels := by
      unfold sourceConsumesAt

      rw [
        List.filterMap_cons
      ]

      simp [
        sourceConsumeFilter
      ]

    have hTargetList :
        targetConsumesAt
            actor
            (event :: occurrences) =
          event ::
            targetConsumesAt
              actor
              occurrences := by
      unfold targetConsumesAt

      rw [
        List.filter_cons_of_pos
          (by
            simp [hTarget])
      ]

    rw [
      hSource,
      hTargetList
    ]

    exact
      Forall2.cons
        hMatch
        (hRest actor)

  · have hSource :
        sourceConsumesAt
            actor
            (DTR.GeneralLabel.consume
                receiver
                message ::
              labels) =
          sourceConsumesAt
            actor
            labels := by
      unfold sourceConsumesAt

      rw [
        List.filterMap_cons
      ]

      simp [
        sourceConsumeFilter,
        hActor
      ]

    have hTargetList :
        targetConsumesAt
            actor
            (event :: occurrences) =
          targetConsumesAt
            actor
            occurrences := by
      unfold targetConsumesAt

      rw [
        List.filter_cons_of_neg
          (by
            simp [
              hTarget,
              Ne.symm hActor
            ])
      ]

    rw [
      hSource,
      hTargetList
    ]

    exact hRest actor

/-!
## The wrapper

One induction over `GeneralInstantBlockSpine`, with the visible `.consume` delegated to a premise in the
shape the committed core produces.

**Why the premise is quantified over steps rather than over spine entries.** `hTakeAnswer` below takes a
corresponding pair and a *target weak step at a consume label* and returns the source's answer. That is
exactly the conclusion of `generalConsume_backward_weakStep_of_takeRepresentative`, so a caller discharges
it by applying that theorem once per occurrence — supplying `hName` and the rest of the take package there,
where the entry's own data is in scope. Stating it over the spine's constructor instead would inline
thirteen binders into this theorem's signature and buy nothing.

The spine's per-entry target step is not assumed: `GeneralInstantBlockSpine.weakStep_consume` produces it
from the constructor's own fire premises, so the target side of each entry is structural.

**The `hName` residue is preserved, not eliminated.** It sits inside `hTakeAnswer`'s discharge, once per
occurrence, exactly as the forward wrapper's `hConsumeAnswer` carries the α-representative residue. Nothing
here derives which reactor the source selects.

**The conclusion is the whole source block predicate**, which is strictly more than the forward wrapper
achieved — that one could only produce a `Common.WeakSteps` and had to discard the endpoint conditions.
The asymmetry is real and is explained above: quiescence and idleness cross target-to-source but not
source-to-target.
-/

/--
**Backward instant-block transfer.** A target instant block is answered by a source execution whose
consume labels pair per reactor with the events the target actually fired, ending at a corresponding,
quiescent, all-idle source configuration.

Induction on the spine. `nil` answers with the empty label list and transports the endpoint conditions;
`consume` produces its own target weak step by `GeneralInstantBlockSpine.weakStep_consume`, spends
`hTakeAnswer` on it, recurses, and extends both the execution and the match by one.

**`hTakeAnswer` is the residue, and it is per-step.** Its shape is precisely
`generalConsume_backward_weakStep_of_takeRepresentative`'s conclusion, so discharging it means supplying
that theorem's take package — including `hName : selected.actorName = actorName`, the per-step actor
agreement that is not derivable from source-side data. No global interleaving is encoded: the premise
mentions one step, one event and one message.

**What is derived rather than assumed.** Every label's arrival time (`message.arrival = t`, from the
match's own time conjunct against `GeneralInstantBlockSpine.event_time_of_mem`'s reasoning), the source's
end-of-instant quiescence (`generalQuiescent_of_pendingFuture`), and every actor's idleness
(`generalActorIdle_of_reactorIdle`). Those three are what make the corollary below able to conclude the
whole of `Correctness.generalInstantBlock_source`.

F27 is untouched: the source consume order this produces follows the target's per-reactor order by
construction, which is the direction `GeneralSameReactorOrder`'s header calls the constructive asset. No α
is used to reorder anything, and store-key uniqueness is threaded by
`DTR.generalStoreKeyUnique_of_step` inside `hTakeAnswer`'s own conclusion rather than transported.
-/
theorem generalInstantBlock_backward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {t : LogicalTime}
    {config : DTR.GeneralRuntimeConfiguration}
    {state finish : LF.GeneralRuntimeState}
    {occurrences : List LF.GeneralPendingEvent}
    (hTakeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (event : LF.GeneralPendingEvent),
        GeneralStateCorrespondence
          model
          stepConfig
          stepState →
        DTR.GeneralStoreKeyUnique stepConfig →
        event.tag.time =
          stepState.currentTag.time →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.consume
            event.target
            event.kind)
          stepState' →
        ∃ (stepConfig' : DTR.GeneralRuntimeConfiguration)
          (message : DTR.GeneralMessage),
          Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.consume
                event.target
                message)
              stepConfig' ∧
            GeneralConsumeMatch
              event.target
              message
              event ∧
            GeneralStateCorrespondence
              model
              stepConfig'
              stepState' ∧
            DTR.GeneralStoreKeyUnique stepConfig')
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hSpine :
      GeneralInstantBlockSpine
        program
        t
        state
        occurrences
        finish) :
    ∃ (labels : List DTR.GeneralLabel)
      (config' : DTR.GeneralRuntimeConfiguration),
      Common.WeakSteps
          (DTR.GeneralStep model)
          DTR.GeneralLabel.isTau
          config
          labels
          config' ∧
        generalConsumeBlockMatch
          labels
          occurrences ∧
        (∀ label ∈ labels,
          ∃ (receiver : ActorName)
            (message : DTR.GeneralMessage),
            label =
              DTR.GeneralLabel.consume
                receiver
                message ∧
              message.arrival = t) ∧
        GeneralStateCorrespondence
          model
          config'
          finish ∧
        DTR.GeneralStoreKeyUnique config' ∧
        config'.now = t ∧
        DTR.GeneralConfiguration.readyActors
            config'.erase =
          [] ∧
        ∀ entry ∈ config'.actors,
          DTR.GeneralActorRuntime.idle
            entry.2 =
            true := by

  induction hSpine generalizing config with

  | nil hTime hFuture hIdle =>

      -- The empty answer, plus the two endpoint transports. This is where the backward direction is
      -- strictly stronger than the forward one.
      refine
        ⟨[],
         config,
         Common.WeakSteps.refl config,
         generalConsumeBlockMatch.nil,
         (fun label hLabel =>
           absurd
             hLabel
             (List.not_mem_nil)),
         hCorrespondence,
         hUniqueS,
         ?_,
         ?_,
         ?_⟩

      · rw [
          ← hCorrespondence.logicalTime
        ]

        exact hTime

      · refine
          generalQuiescent_of_pendingFuture
            hCorrespondence
            ?_

        intro event hEvent

        rw [hTime]

        exact
          hFuture
            event
            hEvent

      · intro entry hEntry

        obtain ⟨name, actor⟩ := entry

        obtain ⟨_, reactor, _, hReactorMem, hPair⟩ :=
          hCorrespondence.reactorOfActor
            name
            actor
            hEntry

        exact
          generalActorIdle_of_reactorIdle
            hPair
            (hIdle
              (name, reactor)
              hReactorMem)

  | @consume before aligned rep event events hTime hAlign hAlpha hEarliest hTag earlier' later' reactorRT reaction hQueue hReactor hIdleRT hReaction finish' hTail IH =>

      -- The entry's own event sits at the block's instant: the fire pins it to the representative's tag,
      -- α pins that to the aligned state's, the τ alignment preserves logical time, and `hTime` anchors
      -- the start. Same chain as `GeneralInstantBlockSpine.event_time_of_mem`.
      have hEventTime :
          event.tag.time =
            before.currentTag.time := by
        rw [
          hTag,
          hAlpha.1,
          tauSteps_time_eqLocal
            hAlign,
          hTime
        ]

      -- The source's answer to this entry. The target step is structural, not assumed.
      obtain
          ⟨stepConfig, message, hSourceStep, hMatch, hStepCorrespondence, hStepUnique⟩ :=
        hTakeAnswer
          config
          before
          _
          event
          hCorrespondence
          hUniqueS
          hEventTime
          (GeneralInstantBlockSpine.weakStep_consume
            hAlign
            hAlpha
            hEarliest
            hTag
            hQueue
            hReactor
            hIdleRT
            hReaction)

      obtain
          ⟨tailLabels,
           tailConfig,
           hTailSteps,
           hTailMatch,
           hTailLabels,
           hTailCorrespondence,
           hTailUnique,
           hTailNow,
           hTailReady,
           hTailIdle⟩ :=
        IH
          hStepCorrespondence
          hStepUnique

      refine
        ⟨DTR.GeneralLabel.consume
             event.target
             message ::
           tailLabels,
         tailConfig,
         Common.WeakSteps.cons
           hSourceStep
           hTailSteps,
         generalConsumeBlockMatch_consLocal
           hMatch
           hTailMatch,
         ?_,
         hTailCorrespondence,
         hTailUnique,
         hTailNow,
         hTailReady,
         hTailIdle⟩

      intro label hLabel

      rcases List.mem_cons.mp hLabel with
        rfl |
          hTail'

      · refine
          ⟨event.target,
           message,
           rfl,
           ?_⟩

        -- The match's own time conjunct, read against the instant anchor.
        rw [
          ← hMatch.2.1,
          hEventTime,
          hTime
        ]

      · exact
          hTailLabels
            label
            hTail'

/--
The transfer against the two block predicates, source and target.

`generalInstantBlock_target` is `state.currentTag.time = t` together with the spine, so this corollary
projects it and assembles the main theorem's seven conjuncts into
`Correctness.generalInstantBlock_source`. Nothing is discarded, which is the difference from
`Correctness.generalInstantBlock_forward_of_source` — there the block predicate's endpoint conditions had
to be dropped because transporting them source-to-target is unproved. Here they are transported, so both
block predicates are in play at once and the statement reads as the correspondence of two blocks rather
than of a block and a bare execution.

`config.now = t` is derived from the correspondence's `logicalTime` against the target block's own start
time; it is not a premise.
-/
theorem generalInstantBlock_backward_of_target
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {t : LogicalTime}
    {config : DTR.GeneralRuntimeConfiguration}
    {state finish : LF.GeneralRuntimeState}
    {occurrences : List LF.GeneralPendingEvent}
    (hTakeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (event : LF.GeneralPendingEvent),
        GeneralStateCorrespondence
          model
          stepConfig
          stepState →
        DTR.GeneralStoreKeyUnique stepConfig →
        event.tag.time =
          stepState.currentTag.time →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.consume
            event.target
            event.kind)
          stepState' →
        ∃ (stepConfig' : DTR.GeneralRuntimeConfiguration)
          (message : DTR.GeneralMessage),
          Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.consume
                event.target
                message)
              stepConfig' ∧
            GeneralConsumeMatch
              event.target
              message
              event ∧
            GeneralStateCorrespondence
              model
              stepConfig'
              stepState' ∧
            DTR.GeneralStoreKeyUnique stepConfig')
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hBlock :
      generalInstantBlock_target
        program
        t
        state
        finish
        occurrences) :
    ∃ (labels : List DTR.GeneralLabel)
      (config' : DTR.GeneralRuntimeConfiguration),
      generalInstantBlock_source
          model
          t
          config
          config'
          labels ∧
        generalConsumeBlockMatch
          labels
          occurrences ∧
        GeneralStateCorrespondence
          model
          config'
          finish ∧
        DTR.GeneralStoreKeyUnique config' := by

  obtain ⟨hStartTime, hSpine⟩ :=
    hBlock

  obtain
      ⟨labels,
       config',
       hSteps,
       hMatch,
       hLabels,
       hFinalCorrespondence,
       hFinalUnique,
       hFinalNow,
       hFinalReady,
       hFinalIdle⟩ :=
    generalInstantBlock_backward
      hTakeAnswer
      hCorrespondence
      hUniqueS
      hSpine

  refine
    ⟨labels,
     config',
     ⟨?_,
      hSteps,
      ?_,
      hFinalNow,
      hFinalReady,
      hFinalIdle⟩,
     hMatch,
     hFinalCorrespondence,
     hFinalUnique⟩

  · rw [
      ← hCorrespondence.logicalTime
    ]

    exact hStartTime

  · intro label hLabel

    obtain ⟨receiver, message, hShape, hArrival⟩ :=
      hLabels
        label
        hLabel

    exact
      ⟨receiver,
       message,
       hShape,
       hArrival⟩

/-!
## What the derivation settles, and what it does not

**Settled.** The source is never stuck while the target has instant work: a pending target event at the
current tag forces the source's cohort to be non-empty and its selection to answer, and whichever actor
that selection returns has a pending target event of its own. Both directions of the pairing are used,
and no scheduling premise was added.

**Not settled, and this is the honest residue.** The wrapper cannot be built from these two facts alone,
because the derived agreement is about *existence*, not about *order*. Concretely:

* An induction on `GeneralInstantBlockSpine` walks the target's occurrences in the target's global fire
  order. At each entry the source must produce a `.consume` for **that entry's reactor**, and
  `selectedActor` will produce one for the priority-minimal ready actor instead. The first theorem above
  says the source has *a* step; it does not say the step is at the reactor the spine is at. Nothing
  derivable from `readyActors` can say that, because the two orders genuinely differ — F76's measured
  divergence.
* Inducting on the source's own execution instead removes that mismatch but replaces it with two new
  obligations: that the source-order block **terminates** having consumed exactly the target's
  per-reactor multiset, and that its per-reactor extraction equals the target's. Both are reordering
  facts about whole blocks, and the second needs the block **endpoint** conditions — the same
  `readyActors config'.erase = []` and all-idle facts the forward wrapper deliberately discarded, plus
  their target-side counterparts.

**That choice has been taken: the premise.** `generalConsume_backward_weak_of_takeRepresentative` above
supplies the per-step actor agreement as `hName`, mirroring exactly how
`Correctness.generalConsume_forward_weak_of_fireRepresentative` supplies its α-representative package,
and leaving the residue named and visible. The alternative — proving the whole-block reordering argument
so that `hName` is derived once per occurrence — remains open, and it needs both the per-reactor
multiset-equality argument and the endpoint transport the forward direction also left open.

**What the block wrapper still owes.** Per occurrence: `hName`, and the target-side representative
package the forward core already required. Across the block: that the constructed source labels'
per-reactor extraction equals the target's, which `generalConsumeBlockMatch_cons`-style reasoning gives
step by step once the per-step agreement is in hand, plus termination at the block endpoint. None of that
is claimed here.

What is *not* on the table: a DTR-side quotient, an ordering premise that re-specifies cross-reactor
interleaving, α widening to swap same-target events (decision 0042 forbids it; F80 measured that real
`lfc` orders same-reactor reactions), or any weakening of F27.
-/

end Correctness

end Relico
