import Relico.Correctness.GeneralCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness

/-!
# Lemma 1 for the general family: the two languages compute the same next instant

Obligation G2b, second half. `Relico/Correctness/GeneralCorrespondence.lean` defines the relation `R`,
proves its initial case, and settles the one τ step that has no source counterpart. What remains — and what
the paper calls **Lemma 1** — is the time case: a source configuration and a target state related by `R`
agree on *when something next happens*.

## The two computations, and why they are not the same shape

The source's answer is `DTR.GeneralConfiguration.nextArrival`, a minimum of message arrivals taken over
every binding of the actor store and filtered to arrivals **strictly after** `now`. The target's answer is
`LF.GeneralRuntimeState.earliestPendingEvent?`, a fold over one global event queue with **no filter at all**:
it returns the earliest pending event whether that event is in the future, at the current tag, or at the
current tag and a later microstep.

Two consequences follow, and both are load-bearing.

* The theorems below are stated **under quiescence** — `DTR.GeneralConfiguration.readyActors config.erase =
  []`, the exact premise `DTR.GeneralStep.timeProgress` carries. Without it the two functions genuinely
  disagree, and a theorem claiming otherwise would be false rather than merely unprovable:
  `earliestPendingEvent?` would answer with an event that is already due while `nextArrival` skipped it.
  `DTR.arrival_future_of_readyActors_nil` is what converts that premise into the fact the proofs use — every
  message in every bag is strictly future — and it is stated there rather than here because it is a fact
  about the source alone.
* Under quiescence the target's selected event cannot be at the current tag, so
  `LF.GeneralStep.microstepAdvance` is **not applicable**, and the target step matching a source time
  advance is `LF.GeneralStep.timeAdvance`. That is `generalNoMicrostepAdvance_of_quiescent` below, and it is
  the reason P24's τ step does not reappear as an ambiguity in Lemma 1's time case: the two rules are
  separated by a hypothesis Lemma 1 already carries, not by a choice the proof has to make.

## Why `R` is enough, and where it is not

The forward and backward directions are asymmetric in what they need. Backward — the target selects an
event, the source must have an arrival — needs only `R`: `generalSourceMessageOfEvent` walks the relation's
`pendingTargeted` field to the actor the event names, then its `reactorOfActor` field to that actor's
`GeneralPendingAgrees`, and reads the message out of the backward direction of *that*. Forward — the source
has an arrival, the target must select an event at the same instant — needs `R` plus **minimality on both
sides**, because the event that agrees with the source's minimising message need not be the event the target
selects. `DTR.nextArrival_minimal` and
`LF.GeneralRuntimeState.earliestPendingEvent?_precedesOrEqual_of_mem` are the two halves, and the equality
is closed by antisymmetry.

What `R` deliberately does not give is **multiplicity**: `GeneralPendingAgrees` relates a bag and a queue by
existence at each instant, not by a bijection, so two source messages arriving together may be witnessed by
one event. Nothing in Lemma 1 needs more — the next *instant* is determined by the set of arrival times, not
by how many messages carry each one — and G2c is where the consume case will need it. The module note of
`Relico/Correctness/GeneralCorrespondence.lean` records the same boundary from the other side.

## F74 is the reason this module exists in this shape

Before the repair, `timeProgress` allowed the source to advance to an arbitrary future instant, so no
statement of this form could be true. The rule now carries `nextArrival config.erase = some future` as a
premise, which makes the source's instant *the* minimum rather than *a* future time, and the equality below
is what pairs it with the target's. `docs/STAGE_G_FINDINGS.md` F74 records the defect and the repair.
-/

/--
Every pending event has a source message waiting at its instant.

The backward half of the correspondence, read at the level of whole states rather than one actor. Three of
`R`'s four fields are spent: `pendingTargeted` produces the actor the event names — the field the paper has
no counterpart for, and the field without which an event could name an actor that does not exist —
`reactorOfActor` produces that actor's `GeneralActorCorresponds`, and its `messages` component produces the
message.

The actor is returned as a `DTR.GeneralActorState` bound in `config.erase.actors` rather than as a
`DTR.GeneralActorRuntime` bound in `config.actors`, because every consumer is a theorem about the erased
configuration: `nextArrival`, `nextArrival_complete`, `nextArrival_minimal` and
`arrival_future_of_readyActors_nil` all quantify over the configuration `erase` produces.
`DTR.mem_eraseContinuations_of_mem` is the projection lemma that crosses the boundary, and it is a
*membership* lemma rather than the lookup lemma beside it for the reason `R` quantifies over membership at
all — a shadowed actor's message still moves the source clock.

Note that no quiescence hypothesis appears: this is a fact about the relation alone, and it holds at any
configuration. Only the *futureness* of the message it produces needs quiescence, which is the next theorem.
-/
theorem generalSourceMessageOfEvent
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (event : LF.GeneralPendingEvent)
    (hCorrespondence :
      GeneralStateCorrespondence config state)
    (hEvent :
      event ∈ state.pending) :
    ∃ actorState : DTR.GeneralActorState,
      ∃ message : DTR.GeneralMessage,
        (event.target, actorState) ∈ config.erase.actors ∧
          message ∈ actorState.bag ∧
            message.arrival = event.tag.time := by

  obtain ⟨actor, hActor⟩ :=
    hCorrespondence.pendingTargeted
      event
      hEvent

  obtain ⟨reactor, _, hCorresponds⟩ :=
    hCorrespondence.reactorOfActor
      event.target
      actor
      hActor

  obtain ⟨message, hMessage, hArrival⟩ :=
    generalPendingAgrees_message_of_event
      event.target
      actor.state.bag
      state.pending
      hCorresponds.messages
      event
      hEvent
      rfl

  refine
    ⟨actor.state,
     message,
     ?_,
     hMessage,
     hArrival⟩

  show
    (event.target, actor.state) ∈
      DTR.eraseContinuations config.actors

  exact
    DTR.mem_eraseContinuations_of_mem
      config.actors
      event.target
      actor
      hActor

/--
Under quiescence every pending event is strictly in the future.

The composition of the theorem above with `DTR.arrival_future_of_readyActors_nil`, and the fact that makes
the target's unfiltered fold comparable with the source's filtered minimum. The target queue may in general
hold an event at the current tag; a *quiescent* source says it may not, because such an event would have to
be backed by a message that is already due, and a due message is a ready actor.

Stated at `config.now` rather than at `state.currentTag.time` so that it composes with the source-side
results directly; `R`'s `logicalTime` field converts between the two whenever the target-side form is wanted,
as the next theorem shows.
-/
theorem generalPendingEventFuture
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (event : LF.GeneralPendingEvent)
    (hQuiescent :
      DTR.GeneralConfiguration.readyActors config.erase = [])
    (hCorrespondence :
      GeneralStateCorrespondence config state)
    (hEvent :
      event ∈ state.pending) :
    config.now < event.tag.time := by

  obtain ⟨actorState, message, hActorState, hMessage, hArrival⟩ :=
    generalSourceMessageOfEvent
      config
      state
      event
      hCorrespondence
      hEvent

  have hFuture :
      config.now < message.arrival :=
    DTR.arrival_future_of_readyActors_nil
      config.erase
      event.target
      actorState
      message
      hQuiescent
      hActorState
      hMessage

  rw [
    hArrival
  ] at hFuture

  exact hFuture

/--
A quiescent source rules out the target's microstep advance.

`LF.GeneralStep.microstepAdvance` fires exactly when the selected event sits at the current logical time and
a later microstep — P24's zero-delay send, the one τ step with no source counterpart. This theorem says the
premise it needs is unavailable whenever the source is quiescent and related, so Lemma 1's time case never
has to choose between the target's two advance rules: `timeAdvance` is the only one whose premise can hold.

Together with `generalCorrespondence_microstepAdvance` this closes the microstep story from both ends. There
the τ step is *absorbed*, because it changes nothing `R` constrains; here it is *excluded*, because the
source configuration a time advance starts from cannot be related to a state that has one to make. Neither
theorem forbids the step — the target is free to microstep, and must be, since a zero-delay send is legal
Rebeca — and that is why the architecture is a weak bisimulation.

Proved from `generalPendingEventFuture` and `R`'s `logicalTime` field, with `Nat.lt_irrefl` rather than
`omega`: **F72** measured that `omega` does not see through the `LogicalTime` abbreviation.
-/
theorem generalNoMicrostepAdvance_of_quiescent
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (event : LF.GeneralPendingEvent)
    (hQuiescent :
      DTR.GeneralConfiguration.readyActors config.erase = [])
    (hCorrespondence :
      GeneralStateCorrespondence config state)
    (hEvent :
      event ∈ state.pending) :
    event.tag.time ≠ state.currentTag.time := by

  intro hEqual

  have hFuture :
      config.now < event.tag.time :=
    generalPendingEventFuture
      config
      state
      event
      hQuiescent
      hCorrespondence
      hEvent

  rw [
    hEqual,
    hCorrespondence.logicalTime
  ] at hFuture

  exact
    absurd
      hFuture
      (Nat.lt_irrefl config.now)

/--
**Forward.** Whatever instant the source advances to, the target selects an event at exactly that instant.

The direction Definition 1's forward transfer condition needs, and the harder of the two, because the event
that *witnesses* the source's minimising message need not be the event the target *selects*. Both
minimalities are therefore spent:

* `LF.GeneralRuntimeState.earliestPendingEvent?_precedesOrEqual_of_mem` bounds the selected event by the
  witness, giving `selected ≤ answer` once the witness' time is rewritten through the agreement equation and
  the arrival equation;
* `DTR.nextArrival_minimal` bounds the source's answer by the *selected* event's own source message —
  obtained by running `generalSourceMessageOfEvent` a second time, now on the selected event — giving
  `answer ≤ selected`.

`Nat.le_antisymm` closes the two into the equation. This is why the theorem cannot be proved by exhibiting
the witness event and stopping: the witness is only related to the source's answer, and the *target's*
behaviour is decided by the selection.

Quiescence enters exactly once, in the second bound: `DTR.nextArrival_minimal` is premised on the message it
is compared against being strictly future, and the selected event's message is future because the source is
quiescent. Without that premise a message already due would be outside the minimum's range and the bound
would be unavailable — the concrete way F74's defect would resurface.
-/
theorem generalTimeEquivalence_forward
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (answer : LogicalTime)
    (hQuiescent :
      DTR.GeneralConfiguration.readyActors config.erase = [])
    (hCorrespondence :
      GeneralStateCorrespondence config state)
    (hNext :
      DTR.GeneralConfiguration.nextArrival config.erase =
        some answer) :
    ∃ event : LF.GeneralPendingEvent,
      LF.GeneralRuntimeState.earliestPendingEvent? state =
          some event ∧
        event.tag.time = answer := by

  obtain ⟨name, actorState, message, hActorMember, hBagMember, hArrival, _⟩ :=
    DTR.nextArrival_sound
      config.erase
      answer
      hNext

  have hEraseMember :
      (name, actorState) ∈
        DTR.eraseContinuations config.actors :=
    hActorMember

  obtain ⟨actor, hActor, hActorState⟩ :=
    DTR.mem_eraseContinuations
      config.actors
      name
      actorState
      hEraseMember

  obtain ⟨reactor, _, hCorresponds⟩ :=
    hCorrespondence.reactorOfActor
      name
      actor
      hActor

  rw [← hActorState] at hBagMember

  obtain ⟨event, hEvent, _, hTime⟩ :=
    generalPendingAgrees_event_of_message
      name
      actor.state.bag
      state.pending
      hCorresponds.messages
      message
      hBagMember

  obtain ⟨selected, hSelected⟩ :=
    LF.GeneralRuntimeState.earliestPendingEvent?_isSome_of_mem
      state
      event
      hEvent

  have hSelectedAtMost :
      selected.tag.time ≤ answer := by

    have hOrder :
        LF.Tag.PrecedesOrEqual
          selected.tag
          event.tag :=
      LF.GeneralRuntimeState.earliestPendingEvent?_precedesOrEqual_of_mem
        state
        selected
        event
        hSelected
        hEvent

    have hTimeAtMost :
        selected.tag.time ≤ event.tag.time :=
      LF.Tag.time_le_of_precedesOrEqual
        hOrder

    rw [
      hTime,
      hArrival
    ] at hTimeAtMost

    exact hTimeAtMost

  have hAnswerAtMost :
      answer ≤ selected.tag.time := by

    have hSelectedMember :
        selected ∈ state.pending :=
      LF.GeneralRuntimeState.earliestPendingEvent?_mem
        state
        selected
        hSelected

    obtain ⟨selectedState, selectedMessage, hSelectedActor, hSelectedBag, hSelectedArrival⟩ :=
      generalSourceMessageOfEvent
        config
        state
        selected
        hCorrespondence
        hSelectedMember

    have hSelectedFuture :
        config.erase.now < selectedMessage.arrival :=
      DTR.arrival_future_of_readyActors_nil
        config.erase
        selected.target
        selectedState
        selectedMessage
        hQuiescent
        hSelectedActor
        hSelectedBag

    have hMinimal :
        answer ≤ selectedMessage.arrival :=
      DTR.nextArrival_minimal
        config.erase
        selected.target
        selectedState
        selectedMessage
        hSelectedActor
        hSelectedBag
        hSelectedFuture
        answer
        hNext

    rw [hSelectedArrival] at hMinimal

    exact hMinimal

  exact
    ⟨selected,
     hSelected,
     Nat.le_antisymm
       hSelectedAtMost
       hAnswerAtMost⟩

/--
**Backward.** Whatever event the target selects, the source's next arrival is exactly that event's instant.

The direction Definition 1's backward transfer condition needs. Its first three steps are the relation
alone — the selected event is a member of the queue, `generalSourceMessageOfEvent` produces its source
message, and quiescence makes that message strictly future — after which `DTR.nextArrival_complete` says the
source *can* advance. That is only an existential, and an existential is not enough: the source could in
principle advance to some earlier arrival in another actor's bag.

The equality is therefore closed by invoking the forward direction on the answer completeness produced. That
is not circularity — the forward theorem is already proved above and does not mention this one — and it is
what makes the pair of directions a genuine equivalence rather than two one-sided bounds. The two selections
are then identified through `Option.some.injEq`, the idiom
`LF.GeneralRuntimeState.earliestPendingEvent?_mem` uses for the same purpose.
-/
theorem generalTimeEquivalence_backward
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (event : LF.GeneralPendingEvent)
    (hQuiescent :
      DTR.GeneralConfiguration.readyActors config.erase = [])
    (hCorrespondence :
      GeneralStateCorrespondence config state)
    (hSelected :
      LF.GeneralRuntimeState.earliestPendingEvent? state =
        some event) :
    DTR.GeneralConfiguration.nextArrival config.erase =
      some event.tag.time := by

  have hEvent :
      event ∈ state.pending :=
    LF.GeneralRuntimeState.earliestPendingEvent?_mem
      state
      event
      hSelected

  obtain ⟨actorState, message, hActorMember, hBagMember, _⟩ :=
    generalSourceMessageOfEvent
      config
      state
      event
      hCorrespondence
      hEvent

  have hFuture :
      config.erase.now < message.arrival :=
    DTR.arrival_future_of_readyActors_nil
      config.erase
      event.target
      actorState
      message
      hQuiescent
      hActorMember
      hBagMember

  obtain ⟨answer, hNext⟩ :=
    DTR.nextArrival_complete
      config.erase
      event.target
      actorState
      message
      hActorMember
      hBagMember
      hFuture

  obtain ⟨matched, hMatched, hMatchedTime⟩ :=
    generalTimeEquivalence_forward
      config
      state
      answer
      hQuiescent
      hCorrespondence
      hNext

  rw [hSelected] at hMatched

  simp only [
    Option.some.injEq
  ] at hMatched

  rw [← hMatched] at hMatchedTime

  rw [hMatchedTime]

  exact hNext

/--
**Lemma 1's time case, as one equation.**

The source's next arrival *is* the instant of the target's next pending event, or both are absent. Stated as
an equality of `Option LogicalTime` rather than as the pair of implications above, because that is the form
G2c consumes: the two advance rules are premised on `nextArrival config.erase = some future` and on the
target's selection respectively, and an equation lets one premise be rewritten into the other without a case
split at every use.

The `none` case is where the two computations' different shapes are finally reconciled. It is not symmetric
with the `some` case and cannot be: `earliestPendingEvent?` answers `none` only for an *empty queue*, while
`nextArrival` answers `none` whenever no arrival is strictly future — a distinction that would matter without
quiescence, and does not with it. The proof runs the forward direction to contradiction, which is why the
forward theorem is stated with an existential conclusion rather than as an equation: an equation would need
the target's selection to be known before it could be applied here.

Note what the equation does **not** say: nothing about microsteps, and nothing about which *actor* is next.
`generalNoMicrostepAdvance_of_quiescent` covers the first — under these hypotheses the selected event is
strictly future, so its microstep is unconstrained and irrelevant — and G1's `selectedActor` together with
stage F's ordering results cover the second, at G2c, where a consume step has to be matched rather than a
clock.
-/
theorem generalTimeEquivalence
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (hQuiescent :
      DTR.GeneralConfiguration.readyActors config.erase = [])
    (hCorrespondence :
      GeneralStateCorrespondence config state) :
    DTR.GeneralConfiguration.nextArrival config.erase =
      Option.map
        (fun event : LF.GeneralPendingEvent => event.tag.time)
        (LF.GeneralRuntimeState.earliestPendingEvent? state) := by

  cases hSelected :
      LF.GeneralRuntimeState.earliestPendingEvent? state with

  | none =>
      show
        DTR.GeneralConfiguration.nextArrival config.erase =
          none

      cases hNext :
          DTR.GeneralConfiguration.nextArrival config.erase with

      | none =>
          rfl

      | some answer =>
          obtain ⟨event, hEvent, _⟩ :=
            generalTimeEquivalence_forward
              config
              state
              answer
              hQuiescent
              hCorrespondence
              hNext

          rw [hSelected] at hEvent

          simp at hEvent

  | some event =>
      show
        DTR.GeneralConfiguration.nextArrival config.erase =
          some event.tag.time

      exact
        generalTimeEquivalence_backward
          config
          state
          event
          hQuiescent
          hCorrespondence
          hSelected

end Correctness
end Relico
