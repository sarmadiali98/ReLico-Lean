/-
! # The target-side no-past-event invariant

The target-side half of the tag-alignment invariant pair the block-transfer audit commissioned
(2026-08-30): **no pending event carries a tag strictly before the runtime's current tag**.
This is what makes an instant's τ alignment well-behaved — a closure of τ steps toward an
event's tag never has to step *past* another pending event, because there are none behind the
clock — and it is the premise-level reason a fired event's logical time agrees with the
runtime's (the fire rule's own `hTag` pin, read off a state where nothing earlier could have
survived).

Why the invariant is true is a fact about the scheduler and the tag arithmetic, not a new
constraint:

* Both send rules schedule at `LF.Tag.schedule state.currentTag delay`, and
  `Tag.precedesOrEqual_schedule` (`Relico/LF/PendingNotPast.lean`) makes that at-or-after the
  current tag for every delay — zero delay stays at the time and advances the microstep,
  positive delay advances the time. Same-instant generation and future scheduling are the one
  fact.
* `fire` only removes the selected event, leaving the tag alone.
* Both advance rules move the tag **to the selected earliest event's tag**, and
  `earliestPendingEvent?_precedesOrEqual_of_mem` makes that the minimum of the pending tags —
  so after an advance, every surviving event is still at-or-after the new tag. An advance to
  an arbitrary future tag would falsify this invariant; the rules advance to *the event*, and
  that refusal is the design.

Alongside the predicate, the initializer theorem (the initial queue is empty), one
step-preservation theorem covering all seven `GeneralStep` constructors, a τ-closure lift
(the spine's alignment premises consume this), an α-transfer theorem (the light quotient
permutes the queue and nothing else, and the invariant is membership-shaped), and the
fired-event-time corollary. What is deliberately absent: any transitivity or totality
development of `PrecedesOrEqual` — those live where the scheduler declared them, and nothing
here needs more than the two lemmas named above.
-/
import Relico.LF.GeneralInitialization
import Relico.LF.PendingNotPast
import Relico.LF.GeneralAlphaEquivalence

set_option autoImplicit false

namespace Relico
namespace LF

/--
The no-past-event invariant: every pending event is at-or-after the current tag.

Membership-shaped over `state.pending`, like every other consumer of the queue, so it
transports through α-equivalence's queue permutation for free. Says nothing about
multiplicity or order — those are the instant-block layer's business, not time's.
-/
def GeneralNoPastPending
    (state : GeneralRuntimeState) :
    Prop :=
  ∀ event ∈ state.pending,
    LF.Tag.PrecedesOrEqual
      state.currentTag
      event.tag

/--
Every initial state is no-past: the initial queue is empty, so the invariant is vacuous.
-/
theorem generalNoPastPending_initial
    (program : LF.GeneralProgram) :
    GeneralNoPastPending
      (LF.GeneralProgram.initialState program) := by
  intro event hMem

  rw [
    LF.GeneralProgram.initialState_pending
      program
  ] at hMem

  cases hMem

/--
The no-past invariant survives every target step.

Case by case: the three body rules leave tag and queue untouched; both send rules append one
event at `Tag.schedule currentTag delay`, which `precedesOrEqual_schedule` covers for every
delay (zero included — the same-instant case); `fire` removes the selected event and keeps the
tag; and both advance rules set the tag to the selected event's tag, which
`earliestPendingEvent?_precedesOrEqual_of_mem` makes the minimum of the pending tags, so every
survivor is at-or-after the new tag.
-/
theorem generalNoPastPending_of_step
    {program : LF.GeneralProgram}
    {state state' : GeneralRuntimeState}
    {label : LF.GeneralLabel}
    (hNoPast :
      GeneralNoPastPending state)
    (hStep :
      GeneralStep
        program
        state
        label
        state') :
    GeneralNoPastPending state' := by
  cases hStep with

  | assign hReactor hBody hEvaluate =>
      exact hNoPast

  | trace hReactor hBody =>
      exact hNoPast

  -- Stage I's local declaration copies the queue, like `assign` and `trace`, so the
  -- invariant transfers unchanged.
  | localDecl hReactor hBody hEvaluate =>
      exact hNoPast

  -- The three step-into rules copy the queue, so the invariant transfers unchanged.
  | branchTrue hReactor hBody hCondition =>
      exact hNoPast

  | branchFalse hReactor hBody hCondition =>
      exact hNoPast

  | resume hReactor hBody hFrames =>
      exact hNoPast

  | schedule hReactor hBody hArguments =>
      intro event hMem

      rcases
          List.mem_append.mp hMem with
        hOld | hNew
      · exact hNoPast event hOld

      · obtain rfl :=
          List.mem_singleton.mp hNew

        exact
          LF.Tag.precedesOrEqual_schedule
            state.currentTag
            _

  | setPort hReactor hBody hArguments hConnection =>
      intro event hMem

      rcases
          List.mem_append.mp hMem with
        hOld | hNew
      · exact hNoPast event hOld

      · obtain rfl :=
          List.mem_singleton.mp hNew

        exact
          LF.Tag.precedesOrEqual_schedule
            state.currentTag
            _

  | fire hSelected hTag hQueue hReactor hIdle hReaction =>
      intro event hMem

      refine hNoPast event ?_

      rcases
          List.mem_append.mp hMem with
        hEarlier | hLater
      · rw [hQueue]

        exact
          List.mem_append.mpr
            (Or.inl hEarlier)

      · rw [hQueue]

        exact
          List.mem_append.mpr
            (Or.inr
              (List.mem_cons.mpr
                (Or.inr hLater)))

  | microstepAdvance hSelected hTime hMicrostep =>
      intro event hMem

      exact
        GeneralRuntimeState.earliestPendingEvent?_precedesOrEqual_of_mem
          state
          _
          event
          hSelected
          hMem

  | timeAdvance hSelected hForward =>
      intro event hMem

      exact
        GeneralRuntimeState.earliestPendingEvent?_precedesOrEqual_of_mem
          state
          _
          event
          hSelected
          hMem

/--
The no-past invariant survives a τ closure.

The lift the instant-block spine consumes: its alignment premises are `TauSteps`, and this
turns the step-level theorem into closure form by induction. Every τ step is a `GeneralStep`,
so the label plays no role.
-/
theorem generalNoPastPending_of_tauSteps
    {program : LF.GeneralProgram}
    {state state' : GeneralRuntimeState}
    (hNoPast :
      GeneralNoPastPending state)
    (hSteps :
      Common.TauSteps
        (LF.GeneralStep program)
        LF.GeneralLabel.isTau
        state
        state') :
    GeneralNoPastPending state' := by
  revert hNoPast

  induction hSteps with

  | refl current =>
      intro hNoPastCurrent

      exact hNoPastCurrent

  | cons headStep headIsTau remainingSteps IH =>
      intro hNoPastStep

      exact
        IH
          (generalNoPastPending_of_step
            hNoPastStep
            headStep)

/--
The no-past invariant transports across α-equivalence.

The light quotient permutes the pending queue and equates tags, and the invariant is
membership-shaped over the queue and reads only the tag — so a representative of an
α-equivalence class is no-past exactly when the class's every member is. This is what lets a
spine fire at a representative while the invariant was established at the aligned state.
-/
theorem generalNoPastPending_of_generalStateAlphaEquiv
    {state state' : GeneralRuntimeState}
    (hNoPast :
      GeneralNoPastPending state)
    (hAlpha :
      generalStateAlphaEquiv
        state
        state') :
    GeneralNoPastPending state' := by
  obtain ⟨hTag, _, _, hQueue⟩ :=
    hAlpha

  intro event hMem

  rw [← hTag]

  refine hNoPast event ?_

  exact
    hQueue.perm.mem_iff.mpr
      hMem

/--
A fired event's logical time is the runtime's current logical time.

The fire rule pins the selected event's tag to the current tag outright (`hTag`), so the
corollary is that pin read through the `.time` projection — stated for the consumers that
hold a consume-labelled step plus the selected event rather than the rule's own premises. The
impossible constructors are discharged by the label index: only `fire` carries `.consume`.
-/
theorem GeneralStep.consume_event_time
    {program : LF.GeneralProgram}
    {state state' : GeneralRuntimeState}
    {target : ActorName}
    {kind : LF.GeneralEventKind}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume
          target
          kind)
        state')
    {event : LF.GeneralPendingEvent}
    (hSelected :
      GeneralRuntimeState.earliestPendingEvent?
          state =
        some event) :
    event.tag.time =
      state.currentTag.time := by
  cases hStep with

  | fire hFireSelected hTag hQueue hReactor hIdle hReaction =>
      rw [hFireSelected] at hSelected

      obtain rfl :=
        Option.some.inj hSelected

      rw [hTag]

end LF
end Relico
