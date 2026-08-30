import Relico.Correctness.GeneralTimeEquivalence
import Relico.DTR.GeneralSemantics
import Relico.Common.WeakTransition
import Relico.LF.GeneralAlphaEquivalence

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

What F76 does *not* touch is the decomposition by label. `DTR.GeneralStep` has five rules and
`LF.GeneralStep` seven; the observable labels are `.consume` and `.timeAdvance`, and **priority enters only at
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

And it owes a second thing §7 does not list, measured as **F78**: the two transfer conditions above conclude
with bare `DTR.GeneralStep`/`LF.GeneralStep`, whereas the architecture the paper states is a **weak**
bisimulation. A step correspondence with an owed lift proves something strictly weaker, so
`generalTimeAdvance_forward_weak` and `generalTimeAdvance_backward_weak` restate both directions over
`Common.WeakStep`. The padding they supply is empty, which is the honest reading of these two rules rather
than a shortcut — see the forward lift's own docstring. F78's *other* half is not repaired here and cannot be:
there is no label correspondence ϕ anywhere in the repository, and the `.timeAdvance` cases avoid needing one
only because that constructor carries the same payload type on both sides.
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

/--
**Forward, at the `.timeAdvance` label, lifted to a weak transition.**

The lift `docs/STAGE_G_FINDINGS.md` **F78** records as owed. The architecture the paper states is a *weak*
bisimulation, and `generalTimeAdvance_forward` above concludes with a bare `LF.GeneralStep` — a step
correspondence, which is strictly **weaker** than the architecture claims, because nothing in it permits the
matched target transition to sit inside internal traffic. Until this module produces a `Common.WeakStep`, the
machinery in `Relico/Common/WeakTransition.lean` is exercised only by the five concrete pins at
`emptyProgram`/`emptyModel` in `Relico/Tests/GeneralSemantics.lean`, and Definition 1's *weak* reading is
checked nowhere against the general families.

The τ padding is **empty at both ends**, and that is the content rather than a shortcut. `TauSteps.refl` on
each side says the source's advance is matched by *exactly one* target advance with no administrative traffic
around it, which is **stronger** than a padded statement, and it is what the two time rules actually do.
Genuine padding is owed only at `.consume`, where **P24** measured that a zero-delay send costs the target a
microstep the source does not take; `generalCorrespondence_microstepAdvance` is what absorbs that, so #129
inherits the padded shape and this label does not.

Proved through the `WeakStep.visible` **constructor**, never through `WeakStep.of_step`, for the reason the
pins record in their own comment: `of_step` takes only `hStep`, splits on `isTau label` with `classical`
`by_cases`, and so elaborates whatever the τ classification says. Routing through it would make this theorem
invariant under the very classification that decides whether `.timeAdvance` is observable at all — the
statement would still typecheck if `isTau` were changed to accept it. `hVisible` is therefore discharged
explicitly by `LF.GeneralLabel.not_isTau_timeAdvance`, which is the one component that would break.

Restated in full rather than derived by a `WeakStep`-valued corollary of a shared lemma, because the existential
sits *outside* the conjunction: the event is chosen by the target and the weak transition is one conjunct of
three, so there is nothing to abstract over without reproducing the whole statement anyway.
-/
theorem generalTimeAdvance_forward_weak
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
        Common.WeakStep
            (LF.GeneralStep program)
            LF.GeneralLabel.isTau
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

  obtain ⟨event, hEventTime, hStep, hNextCorrespondence⟩ :=
    generalTimeAdvance_forward
      program
      config
      state
      future
      hCorrespondence
      hForward
      hQuiescent
      hSelected

  refine
    ⟨event,
     hEventTime,
     ?_,
     hNextCorrespondence⟩

  exact
    Common.WeakStep.visible
      (LF.GeneralLabel.not_isTau_timeAdvance
        state.currentTag.time
        event.tag.time)
      (Common.TauSteps.refl state)
      hStep
      (Common.TauSteps.refl _)

/--
**Backward, at the `.timeAdvance` label, lifted to a weak transition.**

F78's other half. Identical in shape to the forward lift and for the same reasons, with the source's step
relation and the source's τ classification in place of the target's; the asymmetry that made the *underlying*
directions differ — three premises against two, quiescence derived rather than crossed — is entirely inside
`generalTimeAdvance_backward` and does not reach the lift.

The one thing worth reading off this pair is that both `GeneralStep` relations inhabit
`Common.LabeledTransition` after partial application, `LF.GeneralStep program` at
`LF.GeneralRuntimeState`/`LF.GeneralLabel` and `DTR.GeneralStep model` at
`DTR.GeneralRuntimeConfiguration`/`DTR.GeneralLabel`. That is what makes one piece of machinery serve both
sides, and it is checked here on the general families rather than only at the empty pins.

What this pair still does **not** give is Definition 1. A weak bisimulation is a *relation* closed under both
transfer conditions at *every* label; these two theorems close it at one label in both directions. The
`.consume` case is the other label, it is where F76's selector divergence lives, and F78 part 1 measured that
it additionally needs a label correspondence ϕ that **does not exist anywhere in the repository** — the
`.timeAdvance` cases evade that only because `timeAdvance` carries `(LogicalTime, LogicalTime)` on both sides,
so ϕ can be inlined as a literal constructor application. `consume` carries `DTR.GeneralMessage` against
`LF.GeneralEventKind`, and no literal bridges two different types.
-/
theorem generalTimeAdvance_backward_weak
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
    Common.WeakStep
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
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

  obtain ⟨hStep, hNextCorrespondence⟩ :=
    generalTimeAdvance_backward
      model
      config
      state
      event
      hCorrespondence
      hSelected
      hForward

  refine
    ⟨?_,
     hNextCorrespondence⟩

  exact
    Common.WeakStep.visible
      (DTR.GeneralLabel.not_isTau_timeAdvance
        config.now
        event.tag.time)
      (Common.TauSteps.refl config)
      hStep
      (Common.TauSteps.refl _)

/-!
## Reaction order is not observable at the weak level either

The closing rung of `#106` item 3, and the last thing F80 asked row 8 for. F80's sentence is that every
`LF.GeneralStep` derivation is invariant under permuting a reactor's `messageReactions`, "and hence
`LF.GeneralStep`" — the step relation, not just the lookup. Three pieces meet here, each proved where it
belonged and none of them mentioning the other two:

* `Common.WeakStep.mono` — a weak transition survives a pointwise weakening of the step relation. Generic
  to the foundation, so it lives in `Relico/Common/WeakTransition.lean` with no consumer in its own file.
* `LF.GeneralStep.congr_of_projections` — two programs agreeing on `connections` and on `reactionFor?`
  admit the same steps. The whole content of that theorem is that `GeneralStep` reads its program through
  **exactly two** projections, which is a fact about the inductive and belongs beside it.
* `Correctness.generalReactionFor?_perm_of_compiled_pointwise` — the translator's output resolves reactions
  the same way under any reordering, at every instance. That one mentions the translator and the target
  semantics at once, so `Correctness/` is its boundary.

This module is the only place in the repository that can see all three: it imports
`Relico.Common.WeakTransition` directly and reaches `Relico.Correctness.GeneralCorrespondence` through
`Relico.Correctness.GeneralTimeEquivalence`. `GeneralCorrespondence.lean` itself cannot host the
composition — it never imports `Common.WeakTransition`, and `Relico/LF/GeneralSemantics.lean` records
under **F70** that instantiating `Common.WeakStep` is G2c's job rather than the foundation's.

**No `TauSteps` counterpart is stated.** `WeakStep.mono` consumes `TauSteps.mono` internally on its three
internal segments, so a general-family `TauSteps` wrapper would be a declaration with no caller — F75's
defect, which this stage has now recorded twice.

**No biconditional either, and that is a difference from the step level rather than an oversight.**
`LF.GeneralStep.congr_iff_of_projections` is two-way because both of its hypotheses are symmetric
equations. The composition below is not symmetric: the translator hypothesis sits on `left` only, exactly
as `generalReactionFor?_perm_of_compiled` intends — its docstring says `right` "is not required to be a
translation of anything". Turning this into an `Iff` would force a translation hypothesis onto the
reordered side, strengthening a premise that was deliberately left one-sided. The two-way statement
belongs at the step level, where it is free.
-/

/--
A weak transition of the target semantics survives replacing the program by one with the same
`connections` and the same `reactionFor?`.

Nothing here is about permutation or about the translator; it is `Common.WeakStep.mono` instantiated at
`LF.GeneralStep`, with `LF.GeneralStep.congr_of_projections` supplying the pointwise implication. Stated
separately from the composition below because the two hypotheses are the honest interface — a caller
holding them for any reason at all, not only because one side is a reordering of a translated program,
gets the conclusion.
-/
theorem generalWeakStep_congr_of_projections
    {left right : LF.GeneralProgram}
    {state next : LF.GeneralRuntimeState}
    {label : LF.GeneralLabel}
    (hConnections :
      left.connections = right.connections)
    (hReactionFor :
      ∀ (target : ActorName)
        (kind : LF.GeneralEventKind),
        left.reactionFor? target kind =
          right.reactionFor? target kind)
    (hWeakStep :
      Common.WeakStep
        (LF.GeneralStep left)
        LF.GeneralLabel.isTau
        state
        label
        next) :
    Common.WeakStep
      (LF.GeneralStep right)
      LF.GeneralLabel.isTau
      state
      label
      next :=
  Common.WeakStep.mono
    (fun _before _transitionLabel _after hStep =>
      LF.GeneralStep.congr_of_projections
        hConnections
        hReactionFor
        hStep)
    hWeakStep

/--
**F80's closing statement.** Reordering the message reactions of a translated reactor changes no weak
transition of the target semantics.

This is the run-level refutation of Lemma 2 in its strongest available form. Stage F's two ordering
theorems — `portReactions_realizeActorPriority` and
`messageServerReactions_realizeMessageServerPriority` — fix the order of the emitted reaction list, and
this says that order is invisible not merely to the reaction lookup, not merely to a single step, but to
whole weak transitions with their internal τ traffic on both sides. F80 calls those theorems *inert* at
run level; this is the positive form of that word, in the `#60`/F50 shape the repository uses whenever an
owed claim turns out to be false.

`hConnections` is `rfl` for the caller this is written for, since permuting a reaction list inside one
reactor leaves the connection list untouched; it is a hypothesis rather than an assumption because there
is no program-rebuilding function to make it an equation about.

**What this does not do is unblock `#129`.** Both programs here are targets. The `.consume` transfer
conditions compare a *source* step against a target one, and they still wait on F76's repair decision,
which is not a consequence of anything proved here. F80 narrowed the candidate space for that decision;
it did not make it.

The premises `generalReactionFor?_perm_of_compiled_pointwise` inherits are guard-relative and, per **F81**,
have no public discharger yet, so this theorem is sound and satisfiable but not yet applicable to a
concrete translated program without assuming them. `hElsewhere` is the one premise **F82** adds, and F82
records why the closing theorem needs it at all.
-/
theorem generalWeakStep_perm_of_compiled
    {classes : List DTR.GeneralReactiveClass}
    {routes : List Translation.GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {leftReactor rightReactor : LF.GeneralReactor}
    {left right : LF.GeneralProgram}
    {target : ActorName}
    {state next : LF.GeneralRuntimeState}
    {label : LF.GeneralLabel}
    (hCompiled :
      Translation.compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok leftReactor)
    (hInputPortNames :
      ((Translation.generalInputPortsOf
        reactiveClass.name
        routes).map
        (fun port =>
          port.name.value)).Nodup)
    (hActionNames :
      ((Translation.generalActionNamesOf
        (Translation.selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
        (fun name =>
          name.value)).Nodup)
    (hServerNames :
      (reactiveClass.messageServers.map
        (fun server =>
          server.name)).Nodup)
    (hLeft :
      left.reactorOfInstance? target =
        some leftReactor)
    (hRight :
      right.reactorOfInstance? target =
        some rightReactor)
    (hPerm :
      List.Perm
        leftReactor.messageReactions
        rightReactor.messageReactions)
    (hConnections :
      left.connections = right.connections)
    (hElsewhere :
      ∀ (other : ActorName),
        other ≠ target →
        left.reactorOfInstance? other =
          right.reactorOfInstance? other)
    (hWeakStep :
      Common.WeakStep
        (LF.GeneralStep left)
        LF.GeneralLabel.isTau
        state
        label
        next) :
    Common.WeakStep
      (LF.GeneralStep right)
      LF.GeneralLabel.isTau
      state
      label
      next :=
  generalWeakStep_congr_of_projections
    hConnections
    (generalReactionFor?_perm_of_compiled_pointwise
      hCompiled
      hInputPortNames
      hActionNames
      hServerNames
      hLeft
      hRight
      hPerm
      hElsewhere)
    hWeakStep

/-!
## The `.consume` transfer conditions under the partial within-tag quotient

Decision `docs/decisions/0042-within-tag-partial-quotient.md` (2026-08-28) commissions these
statements — audit item C7, task `#129`. F76 measured the two selectors disagree at one tag; the
decision's repair is to state the correspondence up to within-tag permutation, free among events
targeting **distinct** reactors, order-preserving within one. Three things this section builds on,
each implemented in the working tree (uncommitted):

* `Store.lookup_update_commute` (`Relico/Common/Store.lean`) — disjoint updates commute
  observationally, the generating case of the quotient, and the constructive answer to F76's
  "not settled here" question;
* `LF.GeneralStep.fire_execution_commute_of_adjacent_queue_swap`
  (`Relico/LF/GeneralSemantics.lean`) — an execution commutation across an adjacent same-tag
  distinct-target queue swap: both executions' steps constructed (the first from the original
  queue, the second from the queue-swapped partner state — a common-start diamond is impossible,
  since the scheduler selects only the head-most of an equal-tag pair), the finals equal in tag,
  queue and every reactor lookup. An audit on 2026-08-28 replaced an earlier draft of that
  theorem that proved only the store-lookup equality behind premises which did not describe the
  adjacent-pair configuration; the audit, and the correction of the draft's "two-fire diamond"
  terminology to the accurate execution-commutation classification, are recorded in the theorem's
  section header;
* P24's τ classification — a zero-delay send costs the target a microstep the source does not
  take, so the forward condition's match may need one `microstepAdvance` before the fire. That is
  the τ padding of the eventual conditions, and it is *genuine* padding, unlike the
  `.timeAdvance` pair's empty padding.

**The label correspondence is a hypothesis, not a definition** — F78's measurement, honoured here.
`GeneralPendingAgrees` — since the β-(i) repair, a pairing through `Correctness.GeneralConsumeMatch`
(see `Relico/Correctness/GeneralCorrespondence.lean`) — agrees occurrences on target, time and
compiled payload, but still cannot see message names vs event kinds. So each direction of the
eventual conditions takes a *match* premise naming which target event answers which source
message; the payload bridge is now inside the relation rather than a premise, while the kind
bridge stays a premise. The `.timeAdvance` pair evaded this only because both labels carry
`(LogicalTime, LogicalTime)`.

**The transfer conditions themselves are not stated here.** The proof attempt recorded as **F86**
surfaced a relation-granularity blocker — `GeneralPendingAgrees` was, at that point,
non-multiplicity-aware, and consuming one message and one event preserved it only for a matched
pair — so the two conditions waited on that decision and on the quotient-placement question, and
nothing below states them in a weakened form. The multiplicity decision has since been taken
(β-(i), 2026-08-29): `GeneralPendingAgrees` is now a multiplicity-aware pairing stated through
`Correctness.GeneralConsumeMatch`, and both definitions live in
`Relico/Correctness/GeneralCorrespondence.lean` — the pairing needed the match, and the import
graph runs through this module, so the match moved there when its consumer landed. The F86
scheduler question and the quotient-placement question were then both settled: the placement by
the light within-tag quotient (`Relico/LF/GeneralAlphaEquivalence.lean`, 2026-08-30), and with it
the forward condition's **core lemma** below —
`generalConsume_forward_weak_of_fireRepresentative`, the first of the two, stated against
`LF.GeneralStepModulo`. The strength audit of 2026-08-30 fixed its classification: it is the
non-scheduler half of the forward condition — the modulo weak step and the entire post-state
correspondence, derived once an α-representative whose raw `fire` premises hold is *supplied* —
and it is **not** the transfer clause itself, because the representative's existence and the
fire's enablement are premises there, not conclusions. The full forward wrapper is not proved
yet and needs, mechanically, a no-overdue/tag-alignment invariant, a kind-origin invariant
(connecting a runtime event's kind to the send site/route that produced it), and
reachable-state store-key uniqueness, plus two decision-class blockers the audit demonstrated
with reachable counterexamples: the α′ cross-microstep policy and the F27 same-target same-tag
source tie policy. The backward condition is also still unwritten: F86's audit recorded
that it needs the DTR side's own within-instant modulo (the source's actor-priority selection is
deterministic and cannot τ-hide its choice), and that obligation remains exactly where the audit
left it.
-/

/-!
### Store-update membership, privately

Four facts about `Store.update` and list membership, none of which `Relico/Common/Store.lean`
states — its public API is lookup-shaped, and that is deliberate (the lookup/agreement convention
`lookup_update_commute`'s docstring records). The forward `.consume` condition below is the first
theorem in the general family that must reason about *which entries* an updated store still has,
because it updates both stores at one key and must re-establish the correspondence's
membership-shaped fields around that update.

The fourth lemma is the shadowed-binding discipline made occurrence-exact. `hUniqueT`-style
hypotheses below say the updated key's entries filter to exactly one pair: a *value*-uniqueness
premise would not do — `[(k, v), (k, v)]` has one value at `k` and two occurrences, `Store.update`
replaces only the first, the duplicate survives into the post-state, and the correspondence's
`actorOfReactor` would then demand a pairing for the stale occurrence that no side of the step
produced. Reachable states have occurrence-unique keys throughout (the initializers build them
that way and `update` preserves it), so the premises are free for any caller that starts from an
initial state and steps; the relation `R` itself cannot see key multiplicity, which is why the
first updating theorem carries these as premises rather than deriving them.
-/

/--
An update at the head key replaces the head binding.
-/
private theorem update_cons_eq
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (candidate : Key)
    (currentValue : Value)
    (remaining : Store Key Value)
    (key : Key)
    (newValue : Value)
    (hCandidate :
      candidate = key) :
    Store.update
        ((candidate, currentValue) :: remaining)
        key
        newValue =
      (key, newValue) :: remaining := by
  simp [Store.update, hCandidate]

/--
An update at another key keeps the head binding and recurses.
-/
private theorem update_cons_ne
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (candidate : Key)
    (currentValue : Value)
    (remaining : Store Key Value)
    (key : Key)
    (newValue : Value)
    (hCandidate :
      candidate ≠ key) :
    Store.update
        ((candidate, currentValue) :: remaining)
        key
        newValue =
      (candidate, currentValue) ::
        Store.update
          remaining
          key
          newValue := by
  simp [Store.update, hCandidate]

/--
An entry at another key survives an update.
-/
private theorem store_mem_update_of_ne
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (store : Store Key Value)
    (name key : Key)
    (value newValue : Value)
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

  | cons entry remaining inductionHypothesis =>
      obtain ⟨candidate, currentValue⟩ := entry

      by_cases hCandidate : candidate = key

      · rw [
          update_cons_eq
            candidate
            currentValue
            remaining
            key
            newValue
            hCandidate
        ]

        rcases
          List.mem_cons.mp hMem with
          hEq | hIn
        · exact
            absurd
              ((Prod.mk.inj
                  hEq).1.trans
                hCandidate)
              hNe
        · exact
            List.mem_cons_of_mem
              _
              hIn

      · rw [
          update_cons_ne
            candidate
            currentValue
            remaining
            key
            newValue
            hCandidate
        ]

        rcases
          List.mem_cons.mp hMem with
          hEq | hIn
        · rw [hEq]

          exact List.mem_cons_self
        · exact
            List.mem_cons_of_mem
              _
              (inductionHypothesis hIn)

/--
The updated binding itself is a member of the updated store.
-/
private theorem store_mem_update_self
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key)
    (newValue : Value) :
    (key, newValue) ∈
      Store.update
        store
        key
        newValue := by
  induction store with

  | nil =>
      simp [Store.update]

  | cons entry remaining inductionHypothesis =>
      obtain ⟨candidate, currentValue⟩ := entry

      by_cases hCandidate : candidate = key

      · rw [
          update_cons_eq
            candidate
            currentValue
            remaining
            key
            newValue
            hCandidate
        ]

        exact List.mem_cons_self

      · rw [
          update_cons_ne
            candidate
            currentValue
            remaining
            key
            newValue
            hCandidate
        ]

        exact
          List.mem_cons_of_mem
            _
            inductionHypothesis

/--
Every entry of an updated store is either an old entry or the new binding.
-/
private theorem store_mem_update_cases
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {key : Key}
    {newValue : Value}
    {name : Key}
    {value : Value}
    (hMem :
      (name, value) ∈
        Store.update
          store
          key
          newValue) :
    (name, value) ∈ store ∨
      (name, value) = (key, newValue) := by
  induction store with

  | nil =>
      simp only [Store.update] at hMem

      exact
        Or.inr
          (List.mem_singleton.mp hMem)

  | cons entry remaining inductionHypothesis =>
      obtain ⟨candidate, currentValue⟩ := entry

      by_cases hCandidate : candidate = key

      · rw [
          update_cons_eq
            candidate
            currentValue
            remaining
            key
            newValue
            hCandidate
        ] at hMem

        rcases
          List.mem_cons.mp hMem with
          hEq | hIn
        · exact Or.inr hEq
        · exact
            Or.inl
              (List.mem_cons_of_mem
                _
                hIn)

      · rw [
          update_cons_ne
            candidate
            currentValue
            remaining
            key
            newValue
            hCandidate
        ] at hMem

        rcases
          List.mem_cons.mp hMem with
          hEq | hIn
        · exact
            Or.inl
              (List.mem_cons.mpr
                (Or.inl hEq))
        · rcases inductionHypothesis hIn with
            hOld | hNew
          · exact
              Or.inl
                (List.mem_cons_of_mem
                  _
                  hOld)
          · exact Or.inr hNew

/--
If a key's entries filter to exactly one pair, that pair is the key's only entry.

The occurrence-exact form of "no shadowed binding at this key": the filter equation pins how many
times the key occurs, which value-uniqueness cannot.
-/
private theorem store_mem_of_filter_unique
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key)
    (value value' : Value)
    (hUnique :
      store.filter
          (fun entry =>
            decide (entry.1 = key)) =
        [(key, value)])
    (hMem :
      (key, value') ∈ store) :
    value' = value := by
  have hFiltered :
      (key, value') ∈
        store.filter
          (fun entry =>
            decide (entry.1 = key)) :=
    List.mem_filter.mpr
      ⟨hMem,
       by
         show
           decide (key = key) =
             true

         exact decide_eq_true rfl⟩

  rw [hUnique] at hFiltered

  exact
    (Prod.mk.inj
        (List.mem_singleton.mp
            hFiltered)).2

/--
Updating the one entry a key has keeps the key's entries at exactly one pair — the new one.

The companion of `store_mem_of_filter_unique`: together they say the filter-single shape is
invariant under the update, which is how the correspondence's membership fields stay
occurrence-honest across a step that replaces one binding.
-/
private theorem store_filter_update_unique
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (store : Store Key Value)
    (key : Key)
    (oldValue newValue : Value)
    (hUnique :
      store.filter
          (fun entry =>
            decide (entry.1 = key)) =
        [(key, oldValue)]) :
    (Store.update
          store
          key
          newValue).filter
        (fun entry =>
          decide (entry.1 = key)) =
      [(key, newValue)] := by
  induction store with

  | nil =>
      simp at hUnique

  | cons entry remaining inductionHypothesis =>
      obtain ⟨candidate, currentValue⟩ := entry

      by_cases hCandidate : candidate = key

      · rw [
          List.filter_cons_of_pos
            (p := fun entry =>
              decide (entry.1 = key))
            (a := (candidate, currentValue))
            (by
              show
                decide (candidate = key) =
                  true

              rw [hCandidate]

              exact decide_eq_true rfl)
        ] at hUnique

        rw [
          update_cons_eq
            candidate
            currentValue
            remaining
            key
            newValue
            hCandidate
        ]

        injection hUnique with hPairEq hRestEq

        rw [
          List.filter_cons_of_pos
            (p := fun entry =>
              decide (entry.1 = key))
            (a := (key, newValue))
            (by
              show
                decide (key = key) =
                  true

              exact decide_eq_true rfl),
          hRestEq
        ]

      · rw [
          List.filter_cons_of_neg
            (p := fun entry =>
              decide (entry.1 = key))
            (a := (candidate, currentValue))
            (by
              intro hEqual

              exact
                hCandidate
                  (decide_eq_true_iff.mp
                    hEqual))
        ] at hUnique

        rw [
          update_cons_ne
            candidate
            currentValue
            remaining
            key
            newValue
            hCandidate,
          List.filter_cons_of_neg
            (p := fun entry =>
              decide (entry.1 = key))
            (a := (candidate, currentValue))
            (by
              intro hEqual

              exact
                hCandidate
                  (decide_eq_true_iff.mp
                    hEqual))
        ]

        exact inductionHypothesis hUnique

/-!
### The forward `.consume` core lemma

`generalConsume_forward_weak_of_fireRepresentative` below is the forward `.consume` transfer
condition's **core lemma** — not the transfer clause itself, a classification fixed by the
strength audit of 2026-08-30. It is the non-scheduler half: given that the source has taken one
occurrence of a matched message, and given an α-representative at which the target's raw `fire`
premises already hold, it *derives* the target's answer — a modulo weak step at exactly the
fired event's `.consume` label — and the full post-state correspondence. What it deliberately
does **not** derive is the representative's existence and the fire's enablement: those are
premises here, and they are the part of the transfer that belongs to the scheduler-alignment
invariants and the frozen decision-class questions. The full forward wrapper — from an actual
`DTR.GeneralStep.take` and the ordinary global assumptions to the existential target answer —
is not proved yet. It is stated against `LF.GeneralStepModulo`, the light within-tag quotient
of decision 0042: the target's answer may begin at an α-equivalent representative, which is how
F76's measured selection divergence — the source's actor-priority order and the target's queue
order disagreeing within one tag — is absorbed without touching either scheduler.

Reading the premise set top to bottom:

**The source step is given by its shape, not by its rule.** `hDue` plus the conclusion's
post-configuration literal are the `take` rule's local content — bag split, parameter binding,
body installation — and the theorem never consults the model or the selection machinery: the
premises `DTR.GeneralStep.take` uses for actor selection (`hSelected`, `hName`, `hArrival`,
`hIdle`) and server lookup are not consumed here, because nothing downstream of them survives
into the correspondence. The one selection fact that *is* load-bearing is re-stated where it is
needed: `hEventTime` says the matched event sits at the current logical time — the non-overdue
alignment — which in any reachable configuration follows from `hArrival` together with the
clock's quiescence discipline (`readyActors` names every actor with a due message, so the clock
never passes one).

**The match is a premise, per F78.** `GeneralConsumeMatch` names the target event that answers
the taken message — target, time, compiled payload — and the kind bridge stays outside it. The
resolution theorems of `Relico/Correctness/GeneralCorrespondence.lean`
(`generalReactionFor?_eq_some_of_actionRoute`, `…_portRoute`) exist to discharge, at a call
site, exactly the three premises `hReaction`, `hParams` and `hBody`: which reaction the event's
kind resolves to, that its parameters are the server's parameter names, and that its body is a
compilation of the server's body. None of that belongs in this statement — it is compiled-program
truth, not runtime truth.

**The target answer is given by its firing, at a representative.** `hAlignSteps` is the τ
prefix — in the realistic flow either empty or one `microstepAdvance`, the P24 zero-delay
padding — constrained by the two endpoint equations to have moved nothing but the tag
(reactors and pending queue literally unchanged; body-execution τ steps change reactors and
would strand every *other* actor's correspondence, so they are excluded by the endpoints rather
than by rule inspection). `hAlpha`, `hEarliest`, `hTagAligned`, `hQueue`, `hReactorBefore` and
`hIdleRT` are the `fire` rule's own premises at the α-representative: the representative is
already at the event's tag, the event is its scheduler's selection, and the reactor that fires
is the lookup reactor. That the representative exists as a *premise* rather than a construction
is the honest residue of the frozen α′ question — when a same-time, different-microstep event
for another reactor sits ahead of the match, no exact-tag quotient can promote it, and the
caller's ability to supply `hAlpha` is exactly the statement that this configuration does not
arise.

**The store premises are the shadowed-binding discipline.** `hUniqueS` and `hUniqueT` say the
updated key occurs exactly once in each store — occurrence-exact, because `Store.update`
replaces only the first binding and a surviving duplicate would leave the correspondence's
membership-shaped fields owing a pairing for a stale entry no side of the step produced.
`hPaired` says the correspondence's actor-level pairing for the taking actor is realised at
that same lookup reactor. All three are free for any caller that starts from the initial
correspondence and steps: the initializers build occurrence-unique stores and `update` preserves
that, but the relation `R` cannot see key multiplicity, so the first updating theorem in the
family carries them as premises.

What this theorem is **not**: not the forward transfer condition itself (the strength audit of
2026-08-30 classified its representative package as undischarged — the wrapper needs the
no-overdue/tag-alignment invariant, the kind-origin invariant behind `hReaction`/`hParams`/
`hBody`, and reachable-state store-key uniqueness, and it stands behind two decision-class
blockers with reachable counterexamples: α′ cross-microstep promotion and the F27 same-target
same-tag source tie); not the backward direction (F86's audit recorded that it needs the
DTR side's own within-instant modulo — the source's actor-priority selection is deterministic
and cannot τ-hide its choice — still unwritten); not the trace-agreement row (which quantifies
over both directions); and not a claim that the quotient's τ prefix was *necessary* — only that
it is *permitted*.
-/

/--
**Forward, at the `.consume` label, under the light within-tag quotient — the core lemma.**

If the source takes one occurrence of a matched message, and an α-representative at which the
target's raw `fire` premises hold is *supplied* — possibly after a reactor-and-queue-preserving
τ alignment — then the target answers with a weak transition at exactly the fired event's
`.consume` label, and the correspondence holds of both post-states. This is the non-scheduler
half of the forward `.consume` transfer condition; the representative package it assumes is
what the still-unproved full wrapper must derive (no-overdue/tag-alignment invariant,
kind-origin invariant, reachable-state store-key uniqueness, and the α′ and F27-tie decisions).

The conclusion's post-configuration is `DTR.GeneralStep.take`'s own output literal, and the
weak step's final state is `LF.GeneralStep.fire`'s own output literal: nothing in the statement
mentions a step derivation, so a caller holds a concrete take (with its rule premises) and a
concrete firing (with the fire rule's premises at a representative) and reads off the transfer.
The τ prefix is lifted into the quotient system by `LF.GeneralStepModulo.tauSteps_of_raw`, and
the visible step itself is one modulo step — reflexivity on the post-state, the representative
on the pre-state — so the raw `WeakStep` machinery runs unchanged over the lifted relation.
-/
theorem generalConsume_forward_weak_of_fireRepresentative
    (program : LF.GeneralProgram)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (hCorrespondence :
      GeneralStateCorrespondence
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
    (hBody :
      GeneralContinuationCompiles
        server.body
        reaction.body)
    (hUniqueS :
      config.actors.filter
          (fun entry =>
            decide (entry.1 = actorName)) =
        [(actorName, actor)])
    (hPaired :
      GeneralActorCorresponds
        actorName
        actor
        reactorRT
        state.pending) :
    ∃ state' : LF.GeneralRuntimeState,
      Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          (LF.GeneralLabel.consume
            event.target
            event.kind)
          state' ∧
        GeneralStateCorrespondence
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
          state' := by
  have hMatchTarget :
      event.target = actorName :=
    hMatch.1

  have hMatchPayload :
      event.payload =
        message.payload.map
          Translation.compileGeneralValue :=
    hMatch.2.2

  have hAlphaMem :
      ∀ (name : ActorName)
          (reactor : LF.GeneralReactorRuntime),
        (name, reactor) ∈ before.reactors ↔
          (name, reactor) ∈ aligned.reactors :=
    hAlpha.2.1

  have hAlphaQueue :
      LF.generalQueueAlphaEquiv
        before.pending
        aligned.pending :=
    hAlpha.2.2.2

  have hQueuePerm :
      List.Perm
        before.pending
        state.pending := by
    rw [← hAlignedPending]

    exact hAlphaQueue.perm

  have hMessagesBefore :
      GeneralPendingAgrees
        actorName
        actor.state.bag
        before.pending :=
    generalPendingAgrees_of_queue_perm
      actorName
      actor.state.bag
      hPaired.messages
      hQueuePerm.symm

  have hPostMessages :
      GeneralPendingAgrees
        actorName
        (earlier ++ later)
        (earlier' ++ later') :=
    generalPendingAgrees_removeOne
      actorName
      actor.state.bag
      before.pending
      hMessagesBefore
      message
      event
      hMatch
      earlier
      later
      hDue
      earlier'
      later'
      hQueue

  have hPostValuation :
      GeneralValuationAgrees
        (DTR.bindParameters
            server.parameters
            message.payload
            actor.state.valuation)
        (LF.bindReactionParameters
            reaction.parameters
            event.payload
            reactorRT.valuation) := by
    have hBound :=
      generalValuationAgrees_bind
        server.parameters
        message.payload
        actor.state.valuation
        reactorRT.valuation
        hPaired.valuation

    rw [hParams, hMatchPayload]

    exact hBound

  have hPostActorCorresponds :
      GeneralActorCorresponds
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
        {
          valuation :=
            LF.bindReactionParameters
              reaction.parameters
              event.payload
              reactorRT.valuation

          activeBody := reaction.body
        }
        (earlier' ++ later') :=
    {
      valuation := hPostValuation

      messages := hPostMessages

      continuation := hBody
    }

  have hFire :
      LF.GeneralStep
          program
          before
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
          } :=
    LF.GeneralStep.fire
      hEarliest
      hTagAligned
      hQueue
      hReactorBefore
      hIdleRT
      hReaction

  refine
    ⟨{
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
      },
      Common.WeakStep.visible
        (LF.GeneralLabel.not_isTau_consume
          event.target
          event.kind)
        (LF.GeneralStepModulo.tauSteps_of_raw
          hAlignSteps)
        ⟨before,
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
          },
          hAlpha,
          LF.generalStateAlphaEquiv.refl
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
            },
          hFire⟩
        (Common.TauSteps.refl
          ({
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
          } :
            LF.GeneralRuntimeState)),
      ?_⟩

  have hPostActorsFilter :
      (Store.update
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
            }).filter
          (fun entry =>
            decide (entry.1 = actorName)) =
        [(actorName,
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
          })] :=
    store_filter_update_unique
      config.actors
      actorName
      actor
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
      hUniqueS

  have hAfterReactorsFilter :
      (Store.update
            before.reactors
            event.target
            {
              valuation :=
                LF.bindReactionParameters
                  reaction.parameters
                  event.payload
                  reactorRT.valuation

              activeBody := reaction.body
            }).filter
          (fun entry =>
            decide (entry.1 = event.target)) =
        [(event.target,
          {
            valuation :=
              LF.bindReactionParameters
                reaction.parameters
                event.payload
                reactorRT.valuation

            activeBody := reaction.body
          })] :=
    store_filter_update_unique
      before.reactors
      event.target
      reactorRT
      {
        valuation :=
          LF.bindReactionParameters
            reaction.parameters
            event.payload
            reactorRT.valuation

        activeBody := reaction.body
      }
      hUniqueT

  exact
    {
      logicalTime := by
        show
          before.currentTag.time =
            config.now

        rw [← hTagAligned]

        exact
          hEventTime.trans
            hCorrespondence.logicalTime

      reactorOfActor := by
        intro name actor' hMember

        by_cases hName : name = actorName

        · rw [hName] at hMember ⊢

          have hActorEq :
              actor' =
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
                } :=
            store_mem_of_filter_unique
              (Store.update
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
                  })
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
              actor'
              hPostActorsFilter
              hMember

          subst hActorEq

          refine
            ⟨{
                valuation :=
                  LF.bindReactionParameters
                    reaction.parameters
                    event.payload
                    reactorRT.valuation

                activeBody := reaction.body
              },
              ?_,
              hPostActorCorresponds⟩

          rw [hMatchTarget]

          exact
            store_mem_update_self
              before.reactors
              actorName
              {
                valuation :=
                  LF.bindReactionParameters
                    reaction.parameters
                    event.payload
                    reactorRT.valuation

                activeBody := reaction.body
              }

        · rcases
              store_mem_update_cases
                hMember with
            hOld | hNew
          · obtain
                ⟨reactorX, hReactorX, hCorrX⟩ :=
              hCorrespondence.reactorOfActor
                name
                actor'
                hOld

            refine ⟨reactorX, ?_, ?_⟩

            · have hInBefore :
                  (name, reactorX) ∈
                    before.reactors :=
                (hAlphaMem name reactorX).mpr
                  (by
                    rw [hAlignedReactors]

                    exact hReactorX)

              exact
                store_mem_update_of_ne
                  before.reactors
                  name
                  event.target
                  reactorX
                  {
                    valuation :=
                      LF.bindReactionParameters
                        reaction.parameters
                        event.payload
                        reactorRT.valuation

                    activeBody := reaction.body
                  }
                  hInBefore
                  (fun hEqual =>
                    hName
                      (hEqual.trans
                        hMatchTarget))

            · exact
                {
                  valuation :=
                    hCorrX.valuation

                  messages := by
                    have hMessagesAtSplit :
                        GeneralPendingAgrees
                          name
                          actor'.state.bag
                          (earlier' ++ event :: later') := by
                      rw [← hQueue]

                      exact
                        generalPendingAgrees_of_queue_perm
                          name
                          actor'.state.bag
                          hCorrX.messages
                          hQueuePerm.symm

                    exact
                      generalPendingAgrees_of_queue_drop
                        name
                        actor'.state.bag
                        event
                        earlier'
                        later'
                        hMessagesAtSplit
                        (fun hEqual =>
                          hName
                            (hEqual.symm.trans
                              hMatchTarget))

                  continuation :=
                    hCorrX.continuation
                }

          · obtain ⟨hNameEq, _⟩ :=
              Prod.mk.inj hNew

            exact absurd hNameEq hName

      actorOfReactor := by
        intro name reactor' hMember

        by_cases hName : name = actorName

        · rw [hName] at hMember ⊢

          rw [← hMatchTarget] at hMember

          have hMemberTarget :
              (event.target, reactor') ∈
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
                  } := hMember

          have hReactorEq :
              reactor' =
                {
                  valuation :=
                    LF.bindReactionParameters
                      reaction.parameters
                      event.payload
                      reactorRT.valuation

                  activeBody := reaction.body
                } :=
            store_mem_of_filter_unique
              (Store.update
                  before.reactors
                  event.target
                  {
                    valuation :=
                      LF.bindReactionParameters
                        reaction.parameters
                        event.payload
                        reactorRT.valuation

                    activeBody := reaction.body
                  })
              event.target
              {
                valuation :=
                  LF.bindReactionParameters
                    reaction.parameters
                    event.payload
                    reactorRT.valuation

                activeBody := reaction.body
              }
              reactor'
              hAfterReactorsFilter
              hMemberTarget

          subst hReactorEq

          refine
            ⟨{
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
              },
              ?_,
              hPostActorCorresponds⟩

          exact
            store_mem_update_self
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

        · rcases
              store_mem_update_cases
                hMember with
            hOld | hNew
          · have hInAligned :
                (name, reactor') ∈
                  aligned.reactors :=
              (hAlphaMem name reactor').mp
                hOld

            rw [hAlignedReactors] at hInAligned

            obtain
                ⟨actorX, hActorX, hCorrX⟩ :=
              hCorrespondence.actorOfReactor
                name
                reactor'
                hInAligned

            refine ⟨actorX, ?_, ?_⟩

            · exact
                store_mem_update_of_ne
                  config.actors
                  name
                  actorName
                  actorX
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
                  hActorX
                  hName

            · exact
                {
                  valuation :=
                    hCorrX.valuation

                  messages := by
                    have hMessagesAtSplit :
                        GeneralPendingAgrees
                          name
                          actorX.state.bag
                          (earlier' ++ event :: later') := by
                      rw [← hQueue]

                      exact
                        generalPendingAgrees_of_queue_perm
                          name
                          actorX.state.bag
                          hCorrX.messages
                          hQueuePerm.symm

                    exact
                      generalPendingAgrees_of_queue_drop
                        name
                        actorX.state.bag
                        event
                        earlier'
                        later'
                        hMessagesAtSplit
                        (fun hEqual =>
                          hName
                            (hEqual.symm.trans
                              hMatchTarget))

                  continuation :=
                    hCorrX.continuation
                }

          · obtain ⟨hNameEq, _⟩ :=
              Prod.mk.inj hNew

            exact
              absurd
                (hNameEq.trans hMatchTarget)
                hName

      pendingTargeted := by
        intro event' hMember

        have hBefore :
            event' ∈ before.pending := by
          rcases
              List.mem_append.mp
                (show
                  event' ∈ earlier' ++ later'
                  from
                    hMember) with
            hIn | hIn
          · rw [hQueue]

            exact
              List.mem_append.mpr
                (Or.inl hIn)
          · rw [hQueue]

            exact
              List.mem_append.mpr
                (Or.inr
                  (List.mem_cons.mpr
                    (Or.inr hIn)))

        obtain ⟨actorX, hActorX⟩ :=
          hCorrespondence.pendingTargeted
            event'
            (hQueuePerm.mem_iff.mp hBefore)

        by_cases hTarget :
          event'.target = actorName

        · refine
            ⟨{
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
              },
              ?_⟩

          rw [hTarget]

          exact
            store_mem_update_self
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

        · refine ⟨actorX, ?_⟩

          exact
            store_mem_update_of_ne
              config.actors
              event'.target
              actorName
              actorX
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
              hActorX
              hTarget
    }

end Correctness
end Relico
