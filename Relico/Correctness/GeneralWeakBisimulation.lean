import Relico.Correctness.GeneralTimeEquivalence
import Relico.DTR.GeneralSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/-!
# Definition 1 at run level, for the labels priority does not decide

Stage G row 8 (**G2c**). This module holds the part of Definition 1's two transfer conditions that is
**independent of the open decision recorded as F76**, and deliberately stops short of the part that is not.

`docs/STAGE_G_FINDINGS.md` **F76** measured that the two run-level selectors disagree: the source's
`DTR.GeneralActorSelection.selectedActor` keys on `(arrival, priority)`, while the target's
`LF.GeneralRuntimeState.earliestPendingEvent?` keys on `(Tag.time, Tag.microstep)` and is priority-blind,
breaking a same-tag tie by queue append order instead. So the transfer conditions are **false as stated in
§7 item 5** for the `.consume` label, and the guard the design names for them constrains the wrong side.

What F76 does *not* touch is the decomposition by label. `DTR.GeneralStep` has four rules and
`LF.GeneralStep` six; the observable labels are `.consume` and `.timeAdvance`, and **priority enters only at
`.consume`**. Both time rules are selector-driven but priority-free: `DTR.GeneralStep.timeProgress` is tied
to `nextArrival` by F74's repair, `LF.GeneralStep.timeAdvance` to `earliestPendingEvent?`, and Lemma 1
(`generalTimeEquivalence`) already equates the two. The `.timeAdvance` case of both transfer conditions is
therefore provable now, and is proved here.

The `.consume` case is **not** stated in this module, not even in a weakened form. Stating a narrowed version
would be the under-delivery the standing doctrine forbids: where the target is at fault the answer is to
refuse the input, not to quietly shrink the theorem. It waits on the repair decision F76 leaves open, which
in turn waits on the `lfc` reaction-priority probe.

Row 8 also owes a lemma §7 does not list. The source's time rule carries **three** premises and the target's
**two**, so the backward direction cannot simply transcribe them: quiescence has to be *derived* on the
target side. `generalQuiescent_of_earliestPendingEventFuture` below is that derivation, and it is what makes
the backward `.timeAdvance` case go through at all.
-/

/--
Transport `R` along field equalities, so a step case never rebuilds the relation by hand.

`GeneralStateCorrespondence` reads its two arguments through exactly five projections — `next.now`,
`next.actors`, `target.currentTag.time`, `target.reactors`, `target.pending` — so any pair of endpoints
agreeing on those five is related whenever the originals were. Stated in **projection** form rather than
against structure literals because the endpoint a `cases` on a step hands back is a literal only by
accident of how the rule is written: an inversion-driven proof has `next.actors = config.actors` as an
equation, not as a definitional identity, and would otherwise have to `subst` its way back to a literal.

The `logicalTime` field is the one that genuinely changes across a time advance, which is why it is a
hypothesis here rather than being derived: both sides move, and the caller is the only one that knows they
move to the same instant. `generalCorrespondence_retag` is the sibling for the case where **only** the
target moves and the time is unchanged; neither subsumes the other.
-/
theorem generalCorrespondence_advance
    (config next : DTR.GeneralRuntimeConfiguration)
    (state target : LF.GeneralRuntimeState)
    (hNow :
      target.currentTag.time =
        next.now)
    (hActors :
      next.actors =
        config.actors)
    (hReactors :
      target.reactors =
        state.reactors)
    (hPending :
      target.pending =
        state.pending)
    (hCorrespondence :
      GeneralStateCorrespondence config state) :
    GeneralStateCorrespondence next target := by

  refine
    {
      logicalTime := hNow
      reactorOfActor := ?_
      actorOfReactor := ?_
      pendingTargeted := ?_
    }

  · intro name actor hMember

    rw [
      hActors
    ] at hMember

    obtain ⟨reactor, hReactor, hCorresponds⟩ :=
      hCorrespondence.reactorOfActor
        name
        actor
        hMember

    refine
      ⟨reactor,
       ?_,
       ?_⟩

    · rw [
        hReactors
      ]

      exact hReactor

    · rw [
        hPending
      ]

      exact hCorresponds

  · intro name reactor hMember

    rw [
      hReactors
    ] at hMember

    obtain ⟨actor, hActor, hCorresponds⟩ :=
      hCorrespondence.actorOfReactor
        name
        reactor
        hMember

    refine
      ⟨actor,
       ?_,
       ?_⟩

    · rw [
        hActors
      ]

      exact hActor

    · rw [
        hPending
      ]

      exact hCorresponds

  · intro event hMember

    rw [
      hPending
    ] at hMember

    obtain ⟨actor, hActor⟩ :=
      hCorrespondence.pendingTargeted
        event
        hMember

    refine
      ⟨actor,
       ?_⟩

    rw [
      hActors
    ]

    exact hActor

/--
**A target whose earliest event is strictly future forces the source to be quiescent.**

The lemma row 8 owes and `docs/STAGE_G_DESIGN.md` §7 does not list. `DTR.GeneralStep.timeProgress` carries
three premises and `LF.GeneralStep.timeAdvance` two, so the two rules are *not* in premise-for-premise
correspondence and the backward transfer condition cannot transcribe. `hForward` and `hSelected` cross by
Lemma 1; `hQuiescent` has no counterpart to cross from and must be **derived** from the target's own
premise, which is what this does.

The argument is the contrapositive of `DTR.arrival_future_of_readyActors_nil`, run through the relation. A
ready actor is one holding a message already due, so it is backed by a pending event at a time **at or
before** now; but the selected event is the queue's minimum and is strictly **after** now; and a minimum
cannot exceed a member. Six landed results compose to say that, and one of them —
`DTR.mem_eraseContinuations` — was landed by row 7 for an unrelated purpose.

Two instrument notes. The erasure projections are crossed by **defeq ascription**, not by `simp only`:
`config.erase.actors` is definitionally `DTR.eraseContinuations config.actors` and
`GeneralActorState.dueArrival s n` is definitionally `DTR.earliestDueArrival s.bag n`, and a `simp only`
that finds nothing is a hard error. And every arithmetic step uses an explicit `Nat` lemma, because **F72**
measured that `omega` does not see through the `LogicalTime` abbreviation — `Tag.time` is invisible to it
while `Tag.microstep` is not.
-/
theorem generalQuiescent_of_earliestPendingEventFuture
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (event : LF.GeneralPendingEvent)
    (hCorrespondence :
      GeneralStateCorrespondence config state)
    (hSelected :
      LF.GeneralRuntimeState.earliestPendingEvent? state =
        some event)
    (hForward :
      state.currentTag.time <
        event.tag.time) :
    DTR.GeneralConfiguration.readyActors config.erase =
      [] := by

  cases hReady :
      DTR.GeneralConfiguration.readyActors config.erase with

  | nil =>
      rfl

  | cons ready rest =>

      have hReadyMember :
          ready ∈
            DTR.GeneralConfiguration.readyActors config.erase := by

        rw [
          hReady
        ]

        exact
          List.mem_cons.mpr
            (Or.inl rfl)

      obtain ⟨actorState, hActorMember, hDue⟩ :=
        DTR.readyActors_sound
          config.erase
          ready
          hReadyMember

      have hEraseMember :
          (ready.actorName, actorState) ∈
            DTR.eraseContinuations config.actors :=
        hActorMember

      obtain ⟨actor, hActor, hActorState⟩ :=
        DTR.mem_eraseContinuations
          config.actors
          ready.actorName
          actorState
          hEraseMember

      have hEarliest :
          DTR.earliestDueArrival
              actorState.bag
              config.now =
            some ready.logicalTime :=
        hDue

      obtain ⟨message, hBagMember, hArrival, hDueNow⟩ :=
        DTR.earliestDueArrival_sound
          actorState.bag
          config.now
          ready.logicalTime
          hEarliest

      have hActorBagMember :
          message ∈ actor.state.bag := by

        rw [
          hActorState
        ]

        exact hBagMember

      obtain ⟨reactor, _, hCorresponds⟩ :=
        hCorrespondence.reactorOfActor
          ready.actorName
          actor
          hActor

      obtain ⟨witness, hWitnessMember, _, hWitnessTime⟩ :=
        generalPendingAgrees_event_of_message
          ready.actorName
          actor.state.bag
          state.pending
          hCorresponds.messages
          message
          hActorBagMember

      have hOrder :
          LF.Tag.PrecedesOrEqual
            event.tag
            witness.tag :=
        LF.GeneralRuntimeState.earliestPendingEvent?_precedesOrEqual_of_mem
          state
          event
          witness
          hSelected
          hWitnessMember

      have hAtMost :
          event.tag.time ≤
            witness.tag.time :=
        LF.Tag.time_le_of_precedesOrEqual
          hOrder

      rw [
        hWitnessTime,
        hArrival
      ] at hAtMost

      have hEventAtMostNow :
          event.tag.time ≤
            config.now :=
        Nat.le_trans
          hAtMost
          hDueNow

      have hNowForward :
          config.now <
            event.tag.time := by

        rw [
          hCorrespondence.logicalTime
        ] at hForward

        exact hForward

      exact
        absurd
          (Nat.lt_of_lt_of_le
            hNowForward
            hEventAtMostNow)
          (Nat.lt_irrefl config.now)

/--
**Forward, at the `.timeAdvance` label.** Whenever the source may advance time, the target may advance to
the same instant, and the relation survives.

Definition 1's forward transfer condition, restricted to the one observable label priority does not decide.
No `τ*` padding is needed on either side: the source's advance is matched by a single target advance, so the
weak transition degenerates to a strong one here. That is a property of *this* label, not of the
bisimulation — the `.consume` label is where the surplus τ steps and F76's divergence both live.

Stated with the source rule's three premises taken directly rather than with a packaged `DTR.GeneralStep`
hypothesis, and symmetrically for the backward direction below. Two reasons, both measured. The premises are
exactly what `DTR.GeneralStep.quiescent_of_timeAdvance`, `…selected_of_timeAdvance` and `…lt_of_timeAdvance`
hand back, so a caller holding a step is one line away either way; and inverting the *target* rule is not
symmetric with inverting the source one, because `LF.GeneralStep.timeAdvance` carries its event as an
**implicit** field, which `cases` leaves inaccessible — a convention row 6 recorded in its own inversion
preamble. Taking premises keeps both directions in one shape instead of one clean and one fighting the
elaborator.

The event is existential because it is genuinely not determined by the source: Lemma 1
(`generalTimeEquivalence_forward`) is what produces it, and the witness that *justifies* the source's
minimum need not be the event the target *selects*.
-/
theorem generalTimeAdvance_forward
    (program : LF.GeneralProgram)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (future : LogicalTime)
    (hCorrespondence :
      GeneralStateCorrespondence config state)
    (hForward :
      config.now < future)
    (hQuiescent :
      DTR.GeneralConfiguration.readyActors config.erase =
        [])
    (hSelected :
      DTR.GeneralConfiguration.nextArrival config.erase =
        some future) :
    ∃ event : LF.GeneralPendingEvent,
      event.tag.time = future ∧
        LF.GeneralStep
            program
            state
            (LF.GeneralLabel.timeAdvance
              state.currentTag.time
              event.tag.time)
            {
              currentTag := event.tag
              reactors := state.reactors
              pending := state.pending
            } ∧
          GeneralStateCorrespondence
            {
              now := future
              actors := config.actors
            }
            {
              currentTag := event.tag
              reactors := state.reactors
              pending := state.pending
            } := by

  obtain ⟨event, hEventSelected, hEventTime⟩ :=
    generalTimeEquivalence_forward
      config
      state
      future
      hQuiescent
      hCorrespondence
      hSelected

  have hLater :
      state.currentTag.time <
        event.tag.time := by

    rw [
      hCorrespondence.logicalTime,
      hEventTime
    ]

    exact hForward

  refine
    ⟨event,
     hEventTime,
     ?_,
     ?_⟩

  · exact
      LF.GeneralStep.timeAdvance
        hEventSelected
        hLater

  · exact
      generalCorrespondence_advance
        config
        {
          now := future
          actors := config.actors
        }
        state
        {
          currentTag := event.tag
          reactors := state.reactors
          pending := state.pending
        }
        hEventTime
        rfl
        rfl
        rfl
        hCorrespondence

/--
**Backward, at the `.timeAdvance` label.** Whenever the target may advance time, the source may advance to
the same instant, and the relation survives.

The direction that needs the derived quiescence lemma, and the reason that lemma exists. The target rule
supplies two premises and the source rule demands three, so `hQuiescent` is manufactured here by
`generalQuiescent_of_earliestPendingEventFuture` rather than crossed over; `hSelected` then crosses by
Lemma 1's backward half, and `hForward` by `R`'s `logicalTime` field alone.

The asymmetry in premise counts is **not** a defect to be fixed by trimming the source rule. F74 added the
third premise precisely because without it the source could leap past a pending arrival, which made Lemma 1
false. That the extra premise is *recoverable* on the target side is what makes the repair free rather than
restrictive, and this theorem is where that is cashed in.
-/
theorem generalTimeAdvance_backward
    (model : DTR.GeneralModel)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (event : LF.GeneralPendingEvent)
    (hCorrespondence :
      GeneralStateCorrespondence config state)
    (hSelected :
      LF.GeneralRuntimeState.earliestPendingEvent? state =
        some event)
    (hForward :
      state.currentTag.time <
        event.tag.time) :
    DTR.GeneralStep
        model
        config
        (DTR.GeneralLabel.timeAdvance
          config.now
          event.tag.time)
        {
          now := event.tag.time
          actors := config.actors
        } ∧
      GeneralStateCorrespondence
        {
          now := event.tag.time
          actors := config.actors
        }
        {
          currentTag := event.tag
          reactors := state.reactors
          pending := state.pending
        } := by

  have hQuiescent :
      DTR.GeneralConfiguration.readyActors config.erase =
        [] :=
    generalQuiescent_of_earliestPendingEventFuture
      config
      state
      event
      hCorrespondence
      hSelected
      hForward

  have hNext :
      DTR.GeneralConfiguration.nextArrival config.erase =
        some event.tag.time :=
    generalTimeEquivalence_backward
      config
      state
      event
      hQuiescent
      hCorrespondence
      hSelected

  have hSourceForward :
      config.now <
        event.tag.time := by

    rw [
      ← hCorrespondence.logicalTime
    ]

    exact hForward

  exact
    ⟨DTR.GeneralStep.timeProgress
       hSourceForward
       hQuiescent
       hNext,
     generalCorrespondence_advance
       config
       {
         now := event.tag.time
         actors := config.actors
       }
       state
       {
         currentTag := event.tag
         reactors := state.reactors
         pending := state.pending
       }
       rfl
       rfl
       rfl
       rfl
       hCorrespondence⟩

end Correctness
end Relico
