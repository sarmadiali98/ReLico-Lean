import Relico.DTR.GeneralSyntax
import Relico.DTR.GlobalMultiStorePayloadActorPriority

set_option autoImplicit false

namespace Relico
namespace DTR

/-!
# Runtime state for the general fragment, and readiness computed from it

The actor-priority layer already defines what a ready cohort *is*
(`GlobalMultiStorePayloadActorPriority.ReadyActor` and the predicates over it),
but nothing in the repository ever computed one from a state. Every producer of a
`List ReadyActor` lives under `Relico/Tests/`, so the cohort was an unconstrained
proof index: a caller could assert any cohort it liked, including one the state
contradicts. That is the first of the four soundness defects recorded for that
layer, and closing it is what this module is for.

The cohort type is deliberately the existing one rather than a general-family
copy. A copy would let this module prove things about itself while leaving the
layer that actually selects an actor still fed by hand, and the discrimination
theorem below would then pin nothing. The cost is that this general module
depends on a module named for the family it is meant to outlive; when that family
is retired, `ReadyActor` and its predicates belong in `Relico/Common/`.

Scope stops at readiness. There is no step relation and no execution here,
because a step relation is what the translation stages need and bundling it into
this module would make the module unreviewable.

This module differs from the approved design in five places. Each is deliberate,
and each is recorded again at the definition it affects; the count is here so that
a reader comparing the two documents knows how many to expect.

The message container is `bag`, not `queue`. The paper models it as "a multi-set
of time-tagged messages", the existing family already calls its own container
`MessageBag`, and no rule anywhere gives insertion order any meaning. Calling it
a queue would invite a later reader to rely on an order that carries no
semantics.

`earliestDueArrival` is one structural recursion rather than a filter followed by
`List.min?`. Fusing them keeps the definition inside the explicit-recursion
discipline the rest of this family follows, and it means the two lemmas below are
one induction each instead of a chain through library lemmas about `filter` and
`min?`.

Times are `LogicalTime`, the abbreviation the rest of the repository uses for
exactly this, rather than a bare `Nat`. It reduces to `Nat`, so the cohort
records built here still fit the existing `ReadyActor`.

`cohortSimultaneous` is added, because the design wrote `simultaneouslyReady` as
though it took a cohort. It does not: it is a two-argument predicate on records,
so the design's expression does not typecheck. Lifting it to a cohort is a
definition, and the discrimination theorem needs the lifted form.

Soundness and completeness are stated through list membership in the actor store,
not through `Store.lookup`. The `lookup` form is not a presentation choice here;
it is false as stated, and the counterexample is recorded where the two lemmas
are proved.

The paper is no authority for any of this and is not cited. Priority appears in
neither of its SOS tables, and its `enabled` predicates are never defined, so
this development is strictly more specified than the paper here. Under the
standing rule that a divergence found by building the tool is a result rather
than an inconvenience, that owes an entry in `docs/PAPER_CORRECTIONS.md`.
-/

open GlobalMultiStorePayloadActorPriority

/--
One message occurrence in an actor's bag.

The sender is retained because the single-port restriction is stated per sender
and receiver pair, so a later stage cannot check it from the message name alone.
-/
structure GeneralMessage where
  sender :
    ActorName

  messageName :
    MsgName

  payload :
    DTR.GeneralPayload

  arrival :
    LogicalTime

deriving Repr, DecidableEq, BEq, Inhabited

/--
An actor's pending messages.

A multi-set, represented as a list. Nothing in the semantics reads the order, and
the well-formedness layer does not constrain it.
-/
abbrev GeneralMessageBag := List DTR.GeneralMessage

/--
One actor's runtime state.

The class is not recorded here. An actor's class is static, so it is read from
the model's instance list, and duplicating it in the state would create a second
place for the two to disagree.
-/
structure GeneralActorState where
  valuation :
    Store VarName DTR.GeneralValue

  bag :
    DTR.GeneralMessageBag

deriving Repr, DecidableEq, BEq, Inhabited

/--
A global configuration: one logical time, and one state per actor.

Actor order is the model's instance order, which is the order the frontend emits
and the order the measured target semantics uses to decide which reaction runs
first at one tag. Keeping it is what lets a later stage line a source cohort up
against a target reaction sequence.
-/
structure GeneralConfiguration where
  now :
    LogicalTime

  actors :
    Store ActorName DTR.GeneralActorState

deriving Repr, DecidableEq, BEq, Inhabited

/--
The earliest arrival among the messages of a bag that are due at `now`, if the bag
has one at all.

Selecting the due messages and taking their minimum are fused into one recursion.
Kept apart, each of the two properties below would have to travel through library
facts relating membership to `List.filter` and a minimum to the list it came from;
fused, each is one induction that uses nothing beyond the equations this
definition generates.
-/
def earliestDueArrival :
    DTR.GeneralMessageBag →
    LogicalTime →
    Option LogicalTime

  | [], _ =>
      none

  | message :: remaining, now =>
      if message.arrival ≤ now then
        match
          earliestDueArrival
            remaining
            now
        with

        | none =>
            some message.arrival

        | some best =>
            if message.arrival ≤ best then
              some message.arrival
            else
              some best
      else
        earliestDueArrival
          remaining
          now


namespace GeneralActorState

/--
The arrival of the earliest message this actor may take at `now`, if it may take
one at all.

An empty bag and a bag every message of which is still in the future both answer
`none`. The two are deliberately not distinguished: an actor with nothing due is
not ready, and nothing downstream asks why not.
-/
def dueArrival
    (state : DTR.GeneralActorState)
    (now : LogicalTime) :
    Option LogicalTime :=
  DTR.earliestDueArrival
    state.bag
    now

end GeneralActorState

/--
A computed option is either absent or holds something.

Splitting on a computed option is the one step several proofs below share, and
doing it through this lemma keeps every such split from having to abstract the
computation out of the goal first. The variants that abstract it are equivalent
here and are not used, because whether they rewrite the surrounding hypotheses is
not something this development can check without a compiler.
-/
private theorem optionCases
    {α : Type}
    (value : Option α) :
    value =
        none ∨
      ∃ content,
        value =
          some content := by

  cases value with

  | none =>
      exact
        Or.inl
          rfl

  | some content =>
      exact
        Or.inr
          ⟨content,
           rfl⟩

/-!
### What `earliestDueArrival` computes

Four equations first, one per branch the definition can take, so that the two
properties after them rewrite instead of unfolding a recursive definition inside
an induction. The `if` on the recursive answer is split into two equations rather
than one carrying an `if` in its right-hand side, so no consumer has to reduce a
conditional afterwards.

Then the two properties that together say the answer is the right one: every
answer is a real due message of the bag, and every due message of the bag forces
an answer. Neither is worth anything alone. Soundness alone is satisfied by a
function that always answers `none`; completeness alone by one that invents an
arrival out of nothing.
-/

theorem earliestDueArrival_cons_not_due
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now : LogicalTime)
    (hNotDue :
      ¬ message.arrival ≤ now) :
    DTR.earliestDueArrival
        (message :: remaining)
        now =
      DTR.earliestDueArrival
        remaining
        now := by

  simp [
    DTR.earliestDueArrival,
    hNotDue
  ]

theorem earliestDueArrival_cons_due_none
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now : LogicalTime)
    (hDue :
      message.arrival ≤ now)
    (hRemaining :
      DTR.earliestDueArrival
          remaining
          now =
        none) :
    DTR.earliestDueArrival
        (message :: remaining)
        now =
      some message.arrival := by

  simp [
    DTR.earliestDueArrival,
    hDue,
    hRemaining
  ]

theorem earliestDueArrival_cons_due_some_le
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now best : LogicalTime)
    (hDue :
      message.arrival ≤ now)
    (hRemaining :
      DTR.earliestDueArrival
          remaining
          now =
        some best)
    (hBetter :
      message.arrival ≤ best) :
    DTR.earliestDueArrival
        (message :: remaining)
        now =
      some message.arrival := by

  simp [
    DTR.earliestDueArrival,
    hDue,
    hRemaining,
    hBetter
  ]

theorem earliestDueArrival_cons_due_some_gt
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now best : LogicalTime)
    (hDue :
      message.arrival ≤ now)
    (hRemaining :
      DTR.earliestDueArrival
          remaining
          now =
        some best)
    (hNotBetter :
      ¬ message.arrival ≤ best) :
    DTR.earliestDueArrival
        (message :: remaining)
        now =
      some best := by

  simp [
    DTR.earliestDueArrival,
    hDue,
    hRemaining,
    hNotBetter
  ]

/--
An answer for a non-empty bag came either from its head or from its tail.

This is the inversion principle the two properties below need, and it is stated
separately for a reason that is not style: it has no induction hypothesis in
scope, so the case analysis on the recursive answer cannot interact with one. Both
properties then reduce to `rcases` on this lemma.
-/
theorem earliestDueArrival_cons_cases
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now arrival : LogicalTime)
    (hEarliest :
      DTR.earliestDueArrival
          (message :: remaining)
          now =
        some arrival) :
    (message.arrival =
          arrival ∧
        arrival ≤ now) ∨
      DTR.earliestDueArrival
          remaining
          now =
        some arrival := by

  by_cases hDue :
      message.arrival ≤ now

  · rcases
        optionCases
          (DTR.earliestDueArrival
            remaining
            now)
      with
        hRemaining |
          ⟨best, hRemaining⟩

    · rw [
        DTR.earliestDueArrival_cons_due_none
          message
          remaining
          now
          hDue
          hRemaining
      ] at hEarliest

      injection hEarliest with hArrival

      refine
        Or.inl
          ⟨hArrival,
           ?_⟩

      rw [← hArrival]
      exact hDue

    · by_cases hBetter :
          message.arrival ≤ best

      · rw [
          DTR.earliestDueArrival_cons_due_some_le
            message
            remaining
            now
            best
            hDue
            hRemaining
            hBetter
        ] at hEarliest

        injection hEarliest with hArrival

        refine
          Or.inl
            ⟨hArrival,
             ?_⟩

        rw [← hArrival]
        exact hDue

      · rw [
          DTR.earliestDueArrival_cons_due_some_gt
            message
            remaining
            now
            best
            hDue
            hRemaining
            hBetter
        ] at hEarliest

        refine
          Or.inr
            ?_

        rw [hRemaining]
        exact hEarliest

  · rw [
      DTR.earliestDueArrival_cons_not_due
        message
        remaining
        now
        hDue
    ] at hEarliest

    exact
      Or.inr
        hEarliest

/--
Every answer names a real message of the bag, and that message really is due.

The message is produced as an existential witness rather than returned by the
function, because the message is not what a ready cohort records; a caller that
needed the message itself would need a different function, not a different
theorem.
-/
theorem earliestDueArrival_sound
    (bag : DTR.GeneralMessageBag)
    (now arrival : LogicalTime)
    (hEarliest :
      DTR.earliestDueArrival
          bag
          now =
        some arrival) :
    ∃ message,
      message ∈ bag ∧
        message.arrival = arrival ∧
        arrival ≤ now := by

  induction bag with

  | nil =>
      simp [
        DTR.earliestDueArrival
      ] at hEarliest

  | cons head remaining inductionHypothesis =>
      rcases
          DTR.earliestDueArrival_cons_cases
            head
            remaining
            now
            arrival
            hEarliest
        with
          ⟨hHeadArrival, hArrivalDue⟩ |
            hRemaining

      · exact
          ⟨head,
           ⟨by simp,
            ⟨hHeadArrival,
             hArrivalDue⟩⟩⟩

      · rcases
            inductionHypothesis
              hRemaining
          with
            ⟨message,
             hMember,
             hMessageArrival,
             hMessageDue⟩

        exact
          ⟨message,
           ⟨by simp [hMember],
            ⟨hMessageArrival,
             hMessageDue⟩⟩⟩

/--
A bag holding a due message always has an answer.

This is the direction that makes readiness non-vacuous: without it, an actor with
a message it could take now could still be reported as having nothing to do, and
every theorem about the cohort would hold of a system that never runs.

The answer this produces need not be the arrival of the message supplied. A
smaller due arrival elsewhere in the bag wins, which is the point of taking a
minimum, so only the existence of an answer is claimed.
-/
theorem earliestDueArrival_complete
    (bag : DTR.GeneralMessageBag)
    (now : LogicalTime)
    (message : DTR.GeneralMessage)
    (hMember :
      message ∈ bag)
    (hDue :
      message.arrival ≤ now) :
    ∃ arrival,
      DTR.earliestDueArrival
          bag
          now =
        some arrival := by

  induction bag with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      by_cases hHeadDue :
          head.arrival ≤ now

      · rcases
            optionCases
              (DTR.earliestDueArrival
                remaining
                now)
          with
            hRemaining |
              ⟨best, hRemaining⟩

        · exact
            ⟨head.arrival,
             DTR.earliestDueArrival_cons_due_none
               head
               remaining
               now
               hHeadDue
               hRemaining⟩

        · by_cases hBetter :
              head.arrival ≤ best

          · exact
              ⟨head.arrival,
               DTR.earliestDueArrival_cons_due_some_le
                 head
                 remaining
                 now
                 best
                 hHeadDue
                 hRemaining
                 hBetter⟩

          · exact
              ⟨best,
               DTR.earliestDueArrival_cons_due_some_gt
                 head
                 remaining
                 now
                 best
                 hHeadDue
                 hRemaining
                 hBetter⟩

      · simp only [
          List.mem_cons
        ] at hMember

        rcases hMember with
          hEqual |
            hRemainingMember

        · rw [hEqual] at hDue
          exact absurd hDue hHeadDue

        · rw [
            DTR.earliestDueArrival_cons_not_due
              head
              remaining
              now
              hHeadDue
          ]

          exact
            inductionHypothesis
              hRemainingMember

/-!
### The ready cohort of a configuration

Every predicate in the actor-priority layer is stated over a `List ReadyActor`,
and until now every such list in the development was written by hand in a test.
The cohort was therefore an index a caller could choose freely, and the three
theorems that follow are what turn it into a function of the state.
-/

/--
The actors of a store of states that can act at `now`, in store order.

Store order is the model's instance order, and it is kept rather than normalised
because it is the order the measured target semantics uses to break a same-tag
choice. A cohort holding the right records in a different order would still be
useless for lining a source choice up against a target reaction sequence.

An actor with nothing due contributes no record. That is the whole content of
readiness, and it is exactly what the earlier layers leave unconstrained: they
accept any cohort at all, including one naming an actor whose bag is empty.
-/
def readyActorsOf :
    Store ActorName DTR.GeneralActorState →
    LogicalTime →
    List ReadyActor

  | [], _ =>
      []

  | (actorName, state) :: remaining, now =>
      match state.dueArrival now with

      | none =>
          readyActorsOf
            remaining
            now

      | some arrival =>
          (
            {
              actorName := actorName
              logicalTime := arrival
            } : ReadyActor
          ) ::
            readyActorsOf
              remaining
              now


namespace GeneralConfiguration

/--
The actors of a configuration that can act at its current time.

The cohort is a function of the configuration alone. Nothing about the model is
consulted, because whether an actor has a message it may take now is a question
about its bag and the clock; which of the ready actors is then selected is what
priority decides, and that is the next stage's concern.
-/
def readyActors
    (config : DTR.GeneralConfiguration) :
    List ReadyActor :=
  DTR.readyActorsOf
    config.actors
    config.now

end GeneralConfiguration


theorem readyActorsOf_cons_none
    (actorName : ActorName)
    (state : DTR.GeneralActorState)
    (remaining :
      Store ActorName DTR.GeneralActorState)
    (now : LogicalTime)
    (hDue :
      state.dueArrival now =
        none) :
    DTR.readyActorsOf
        ((actorName, state) :: remaining)
        now =
      DTR.readyActorsOf
        remaining
        now := by

  simp [
    DTR.readyActorsOf,
    hDue
  ]

theorem readyActorsOf_cons_some
    (actorName : ActorName)
    (state : DTR.GeneralActorState)
    (remaining :
      Store ActorName DTR.GeneralActorState)
    (now arrival : LogicalTime)
    (hDue :
      state.dueArrival now =
        some arrival) :
    DTR.readyActorsOf
        ((actorName, state) :: remaining)
        now =
      (
        {
          actorName := actorName
          logicalTime := arrival
        } : ReadyActor
      ) ::
        DTR.readyActorsOf
          remaining
          now := by

  simp [
    DTR.readyActorsOf,
    hDue
  ]

/--
A record in a non-empty store's cohort came either from the head entry or from the
tail.

As with the bag, the inversion principle is separated out so that the two
properties below are each a single `rcases` on it.
-/
theorem readyActorsOf_cons_cases
    (actorName : ActorName)
    (state : DTR.GeneralActorState)
    (remaining :
      Store ActorName DTR.GeneralActorState)
    (now : LogicalTime)
    (ready : ReadyActor)
    (hMember :
      ready ∈
        DTR.readyActorsOf
          ((actorName, state) :: remaining)
          now) :
    (ready.actorName = actorName ∧
        state.dueArrival now =
          some ready.logicalTime) ∨
      ready ∈
        DTR.readyActorsOf
          remaining
          now := by

  rcases
      optionCases
        (state.dueArrival now)
    with
      hDue |
        ⟨arrival, hDue⟩

  · rw [
      DTR.readyActorsOf_cons_none
        actorName
        state
        remaining
        now
        hDue
    ] at hMember

    exact
      Or.inr
        hMember

  · rw [
      DTR.readyActorsOf_cons_some
        actorName
        state
        remaining
        now
        arrival
        hDue
    ] at hMember

    simp only [
      List.mem_cons
    ] at hMember

    rcases hMember with
      hEqual |
        hRemainingMember

    · subst hEqual

      exact
        Or.inl
          ⟨rfl,
           hDue⟩

    · exact
        Or.inr
          hRemainingMember

/-!
### Soundness

Both this property and its converse are stated through membership of the store
rather than through `Store.lookup`, and that is not a stylistic choice: the
`lookup` form of soundness is false. Take a store `[(a, first), (a, second)]` whose
two states are due at 3 and at 5. The cohort holds `⟨a, 3⟩` and `⟨a, 5⟩` both,
while `Store.lookup` answers `first` for `a`, so the second record has no witness
of the `lookup` shape and the `lookup` statement fails on it.

The `lookup` form is recoverable as a corollary under key uniqueness, which
`GeneralModel.namesUniqueAndValid` already establishes for the instance names a
configuration's store is built from. A stage that wants it should take uniqueness
as a hypothesis there rather than have it silently assumed here.
-/

/--
Every record in a cohort is backed by an actor of the store that really can act at
that time.

Without this, the cohort could name actors the configuration does not have, or
claim a time no message of theirs carries.
-/
theorem readyActorsOf_sound
    (actors :
      Store ActorName DTR.GeneralActorState)
    (now : LogicalTime)
    (ready : ReadyActor)
    (hMember :
      ready ∈
        DTR.readyActorsOf
          actors
          now) :
    ∃ state,
      (ready.actorName, state) ∈ actors ∧
        state.dueArrival now =
          some ready.logicalTime := by

  induction actors with

  | nil =>
      simp [
        DTR.readyActorsOf
      ] at hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨actorName, state⟩

      rcases
          DTR.readyActorsOf_cons_cases
            actorName
            state
            remaining
            now
            ready
            hMember
        with
          ⟨hActorName, hDue⟩ |
            hRemainingMember

      · exact
          ⟨state,
           ⟨by simp [hActorName],
            hDue⟩⟩

      · rcases
            inductionHypothesis
              hRemainingMember
          with
            ⟨witnessState,
             hWitnessMember,
             hWitnessDue⟩

        exact
          ⟨witnessState,
           ⟨by simp [hWitnessMember],
            hWitnessDue⟩⟩

/--
Soundness for a configuration.
-/
theorem readyActors_sound
    (config : DTR.GeneralConfiguration)
    (ready : ReadyActor)
    (hMember :
      ready ∈
        config.readyActors) :
    ∃ state,
      (ready.actorName, state) ∈ config.actors ∧
        state.dueArrival config.now =
          some ready.logicalTime := by

  unfold GeneralConfiguration.readyActors at hMember

  exact
    DTR.readyActorsOf_sound
      config.actors
      config.now
      ready
      hMember

/--
Every actor of the store that can act at a time appears in the cohort, carrying
the arrival its own bag determines.

This is the direction that rules out a cohort which is merely a subset of what is
ready. The empty cohort is the extreme case, and it satisfies every predicate the
actor-priority layer states, so without this property that layer's theorems all
hold of a system in which nothing ever runs.
-/
theorem readyActorsOf_complete
    (actors :
      Store ActorName DTR.GeneralActorState)
    (now : LogicalTime)
    (actorName : ActorName)
    (state : DTR.GeneralActorState)
    (arrival : LogicalTime)
    (hMember :
      (actorName, state) ∈ actors)
    (hDue :
      state.dueArrival now =
        some arrival) :
    (
      {
        actorName := actorName
        logicalTime := arrival
      } : ReadyActor
    ) ∈
      DTR.readyActorsOf
        actors
        now := by

  induction actors with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨headName, headState⟩

      simp only [
        List.mem_cons
      ] at hMember

      rcases hMember with
        hEqual |
          hRemainingMember

      · rw [← hEqual]

        rw [
          DTR.readyActorsOf_cons_some
            actorName
            state
            remaining
            now
            arrival
            hDue
        ]

        simp

      · rcases
            optionCases
              (headState.dueArrival now)
          with
            hHeadDue |
              ⟨headArrival, hHeadDue⟩

        · rw [
            DTR.readyActorsOf_cons_none
              headName
              headState
              remaining
              now
              hHeadDue
          ]

          exact
            inductionHypothesis
              hRemainingMember

        · rw [
            DTR.readyActorsOf_cons_some
              headName
              headState
              remaining
              now
              headArrival
              hHeadDue
          ]

          simp [
            inductionHypothesis
              hRemainingMember
          ]

/--
Completeness for a configuration.
-/
theorem readyActors_complete
    (config : DTR.GeneralConfiguration)
    (actorName : ActorName)
    (state : DTR.GeneralActorState)
    (arrival : LogicalTime)
    (hMember :
      (actorName, state) ∈ config.actors)
    (hDue :
      state.dueArrival config.now =
        some arrival) :
    (
      {
        actorName := actorName
        logicalTime := arrival
      } : ReadyActor
    ) ∈
      config.readyActors := by

  unfold GeneralConfiguration.readyActors

  exact
    DTR.readyActorsOf_complete
      config.actors
      config.now
      actorName
      state
      arrival
      hMember
      hDue

/-!
### Discrimination

Soundness and completeness pin the cohort to the state. This last theorem pins the
defect instead: it exhibits a cohort that the actor-priority layer's own notion of
a consistent simultaneous cohort accepts, and that the state does not license.

The claim is deliberately narrow. It does not say that no configuration produces
the fabricated cohort, because one obviously could. It says that satisfying those
predicates is not evidence of describing any particular state, so a theorem which
takes a cohort as an argument and constrains it only by them has assumed its
subject rather than derived it. Every selection statement in that layer has that
shape, which is why the defect is worth a theorem rather than a comment.

The witness is a two-actor configuration at time 5. One actor holds a message due
at 3; the other's bag is empty. The fabricated cohort claims both are ready at 3,
and under it the idle actor even qualifies as an earliest ready actor.
-/

/--
A cohort is pairwise simultaneous when every two of its members share a logical
time.

The existing predicate relates a *pair* of ready actors, so lifting it to a whole
cohort is needed to state the theorem below. Having to define that lift here is
itself part of the finding: nothing in the actor-priority layer asks whether a
cohort is internally consistent, only whether an already selected actor is
simultaneous with each candidate.
-/
def cohortSimultaneous
    (cohort : List ReadyActor) :
    Bool :=
  cohort.all fun left =>
    cohort.all fun right =>
      simultaneouslyReady
        left
        right

/--
An actor holding one message, due before the configuration's current time.
-/
def discriminatingWorkerState : DTR.GeneralActorState :=
  {
    valuation := []
    bag :=
      [
        {
          sender := ActorName.mk "worker"
          messageName := MsgName.mk "tick"
          payload := []
          arrival := 3
        }
      ]
  }

/--
An actor holding nothing at all, and so ready at no time.
-/
def discriminatingIdlerState : DTR.GeneralActorState :=
  {
    valuation := []
    bag := []
  }

/--
The configuration the theorem below is about.
-/
def discriminatingConfiguration : DTR.GeneralConfiguration :=
  {
    now := 5
    actors :=
      [
        (
          ActorName.mk "worker",
          DTR.discriminatingWorkerState
        ),
        (
          ActorName.mk "idler",
          DTR.discriminatingIdlerState
        )
      ]
  }

/--
The one record the configuration really licenses.
-/
def discriminatingWorkerRecord : ReadyActor :=
  {
    actorName := ActorName.mk "worker"
    logicalTime := 3
  }

/--
A record claiming the idle actor is ready at 3, which no message of its own
supports.
-/
def discriminatingIdlerRecord : ReadyActor :=
  {
    actorName := ActorName.mk "idler"
    logicalTime := 3
  }

/--
A cohort the layer accepts and the state contradicts.
-/
def fabricatedCohort : List ReadyActor :=
  [
    DTR.discriminatingWorkerRecord,
    DTR.discriminatingIdlerRecord
  ]

/--
The fabricated cohort is consistent by the layer's own lights, admits the idle
actor as an earliest ready actor, and is not the cohort of the configuration it
purports to describe.

The third conjunct gives the reason and the fourth pins the real answer, so this is
not merely an inequality between two lists: the idle actor has nothing due, and the
cohort of that configuration holds exactly one record.

Every application is written out rather than using field notation on these
constants, so that nothing in the statement depends on how a dotted name is split
between a constant and a projection.
-/
theorem readyActors_discriminates :
    DTR.cohortSimultaneous
          DTR.fabricatedCohort =
        true ∧
      earliestReady
          DTR.fabricatedCohort
          DTR.discriminatingIdlerRecord =
        true ∧
      GeneralActorState.dueArrival
          DTR.discriminatingIdlerState
          (GeneralConfiguration.now
            DTR.discriminatingConfiguration) =
        none ∧
      GeneralConfiguration.readyActors
          DTR.discriminatingConfiguration =
        [DTR.discriminatingWorkerRecord] ∧
      GeneralConfiguration.readyActors
          DTR.discriminatingConfiguration ≠
        DTR.fabricatedCohort := by

  decide

end DTR
end Relico
