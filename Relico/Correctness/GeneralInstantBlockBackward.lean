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

So the remaining choice is between supplying the per-step actor agreement as a premise — mirroring
exactly how `Correctness.generalConsume_forward_weak_of_fireRepresentative` supplies its
α-representative package, and leaving the residue named and visible — and proving the whole-block
reordering argument, which is a larger piece of work than this milestone was scoped for and which needs
the endpoint transport the forward direction also left open.

What is *not* on the table: a DTR-side quotient, an ordering premise that re-specifies cross-reactor
interleaving, α widening to swap same-target events (decision 0042 forbids it; F80 measured that real
`lfc` orders same-reactor reactions), or any weakening of F27.
-/

end Correctness

end Relico
