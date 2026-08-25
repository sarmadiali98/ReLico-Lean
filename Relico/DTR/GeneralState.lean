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
### The next arrival, ignoring the due filter

`earliestDueArrival` answers *"what may this actor take now"*, and it is the wrong
question for a time step: it only looks at messages with `arrival ≤ now`, so a bag
whose every message is still in the future answers `none`. Time progress needs the
opposite — the earliest arrival **still ahead** — and nothing in the development
computed it. Its absence is what let `DTR.GeneralStep.timeProgress` advance to an
arbitrary `future`, recorded as **F74**.

The paper is explicit that this is the quantity the rule uses. Lemma 1's
time-progress case has DTR *"advance logical time to the minimum message arrival
time ar_min"*, and Theorem 1's time case says *"time progresses to the next message
arrival ar_min"*. `docs/PAPER_CORRECTIONS.md` had already transcribed
`now := ar_min` correctly before the general step relation was written, so this
module is catching up with our own record rather than revising the paper.

**One deliberate difference from the paper's comprehension, and it is not a slip.**
Table I restricts the minimum to actors whose continuation is `ϵ`, so in the paper
an actor part-way through a message server contributes no arrival. P17's closing
note already observes that the restriction is vacuous there — such an actor has a
`τ`-transition, so TIME PROGRESS could not have fired in the first place. It is not
vacuous here, because the general step relation deliberately lets the clock advance
while an actor sits mid-body, in symmetry with the target (see
`LF.GeneralStep`'s own docstring, and **F74**'s open item on whether that symmetry
should be kept). Dropping the restriction is what keeps this definition matching
the target's queue, which likewise ignores what any reactor is doing: were an
arrival in a mid-body actor's bag excluded, the source could advance past a tag the
target must stop at, which is the very failure F74 records in the other direction.

Deliberately **not** the same shape as `earliestDueArrival`. That function fuses a
filter with a minimum over one bag; this one takes a minimum over *every* bag in
the configuration, because time is global — an actor with an empty bag must not
stop the clock, and an arrival in some *other* actor's bag must. So the recursion
is over the store, and the per-bag helper is the piece that recurses over messages.
-/

/--
The earliest arrival strictly after `now` among the messages of one bag.

`none` means this bag holds nothing in the future, which covers both an empty bag
and a bag every message of which is already due. Those two are not distinguished,
for the same reason `dueArrival` does not distinguish its two `none` cases:
neither can move the clock, and no caller asks why not.

The comparison is strict. A message arriving exactly at `now` is due, not future,
and is `take`'s business rather than time progress's — `timeProgress` also carries
a quiescence premise, so a bag holding such a message blocks the clock through
that premise instead.
-/
def earliestFutureArrival :
    DTR.GeneralMessageBag →
    LogicalTime →
    Option LogicalTime

  | [], _ =>
      none

  | message :: remaining, now =>
      if now < message.arrival then
        match
          earliestFutureArrival
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
        earliestFutureArrival
          remaining
          now

/--
The earliest arrival strictly after `now` anywhere in a store of actor states.

Store order does not matter here, unlike in `readyActorsOf`: a minimum is
order-independent, and no caller reads a position out of the answer. What matters
is that *every* bag is consulted, which is what makes the answer a property of the
configuration rather than of one actor.
-/
def earliestFutureArrivalOf :
    Store ActorName DTR.GeneralActorState →
    LogicalTime →
    Option LogicalTime

  | [], _ =>
      none

  | (_, state) :: remaining, now =>
      match
        DTR.earliestFutureArrival
          state.bag
          now
      with

      | none =>
          earliestFutureArrivalOf
            remaining
            now

      | some arrival =>
          match
            earliestFutureArrivalOf
              remaining
              now
          with

          | none =>
              some arrival

          | some best =>
              if arrival ≤ best then
                some arrival
              else
                some best


/-!
### What `earliestFutureArrival` guarantees

The same two properties `earliestDueArrival` carries, for the same reason: without
soundness the answer could name a time no message occupies, and `timeProgress`
would advance to a fiction; without the lower-bound property the answer could skip
an earlier arrival, which is precisely the defect F74 records. Both are proved in
this file's established idiom — equation lemmas discharged by `simp` on the
definition plus the branch hypotheses, then an inversion lemma with no induction
hypothesis in scope, then the properties by `rcases` on it.
-/

theorem earliestFutureArrival_cons_not_future
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now : LogicalTime)
    (hNotFuture :
      ¬ now < message.arrival) :
    DTR.earliestFutureArrival
        (message :: remaining)
        now =
      DTR.earliestFutureArrival
        remaining
        now := by

  simp [
    DTR.earliestFutureArrival,
    hNotFuture
  ]

theorem earliestFutureArrival_cons_future_none
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now : LogicalTime)
    (hFuture :
      now < message.arrival)
    (hRemaining :
      DTR.earliestFutureArrival
          remaining
          now =
        none) :
    DTR.earliestFutureArrival
        (message :: remaining)
        now =
      some message.arrival := by

  simp [
    DTR.earliestFutureArrival,
    hFuture,
    hRemaining
  ]

theorem earliestFutureArrival_cons_future_some_le
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now best : LogicalTime)
    (hFuture :
      now < message.arrival)
    (hRemaining :
      DTR.earliestFutureArrival
          remaining
          now =
        some best)
    (hBetter :
      message.arrival ≤ best) :
    DTR.earliestFutureArrival
        (message :: remaining)
        now =
      some message.arrival := by

  simp [
    DTR.earliestFutureArrival,
    hFuture,
    hRemaining,
    hBetter
  ]

theorem earliestFutureArrival_cons_future_some_gt
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now best : LogicalTime)
    (hFuture :
      now < message.arrival)
    (hRemaining :
      DTR.earliestFutureArrival
          remaining
          now =
        some best)
    (hNotBetter :
      ¬ message.arrival ≤ best) :
    DTR.earliestFutureArrival
        (message :: remaining)
        now =
      some best := by

  simp [
    DTR.earliestFutureArrival,
    hFuture,
    hRemaining,
    hNotBetter
  ]

/--
An answer for a non-empty bag came either from its head or from its tail.

Mirrors `earliestDueArrival_cons_cases`, and is stated separately for the reason
recorded there: it has no induction hypothesis in scope, so the case analysis on
the recursive answer cannot interact with one.
-/
theorem earliestFutureArrival_cons_cases
    (message : DTR.GeneralMessage)
    (remaining : DTR.GeneralMessageBag)
    (now arrival : LogicalTime)
    (hEarliest :
      DTR.earliestFutureArrival
          (message :: remaining)
          now =
        some arrival) :
    (message.arrival =
          arrival ∧
        now < arrival) ∨
      DTR.earliestFutureArrival
          remaining
          now =
        some arrival := by

  by_cases hFuture :
      now < message.arrival

  · rcases
        optionCases
          (DTR.earliestFutureArrival
            remaining
            now)
      with
        hRemaining |
          ⟨best, hRemaining⟩

    · rw [
        DTR.earliestFutureArrival_cons_future_none
          message
          remaining
          now
          hFuture
          hRemaining
      ] at hEarliest

      injection hEarliest with hArrival

      refine
        Or.inl
          ⟨hArrival,
           ?_⟩

      rw [← hArrival]
      exact hFuture

    · by_cases hBetter :
          message.arrival ≤ best

      · rw [
          DTR.earliestFutureArrival_cons_future_some_le
            message
            remaining
            now
            best
            hFuture
            hRemaining
            hBetter
        ] at hEarliest

        injection hEarliest with hArrival

        refine
          Or.inl
            ⟨hArrival,
             ?_⟩

        rw [← hArrival]
        exact hFuture

      · rw [
          DTR.earliestFutureArrival_cons_future_some_gt
            message
            remaining
            now
            best
            hFuture
            hRemaining
            hBetter
        ] at hEarliest

        refine
          Or.inr
            ?_

        rw [hRemaining]
        exact hEarliest

  · rw [
      DTR.earliestFutureArrival_cons_not_future
        message
        remaining
        now
        hFuture
    ] at hEarliest

    exact
      Or.inr
        hEarliest

/--
Every answer names a real message of the bag, and that message really is ahead.

The witness shape follows `earliestDueArrival_sound`: the message is produced
existentially rather than returned, because the time step needs the *time* and a
caller wanting the message would need a different function.
-/
theorem earliestFutureArrival_sound
    (bag : DTR.GeneralMessageBag)
    (now arrival : LogicalTime)
    (hEarliest :
      DTR.earliestFutureArrival
          bag
          now =
        some arrival) :
    ∃ message,
      message ∈ bag ∧
        message.arrival = arrival ∧
        now < arrival := by

  induction bag with

  | nil =>
      simp [
        DTR.earliestFutureArrival
      ] at hEarliest

  | cons head remaining inductionHypothesis =>
      rcases
          DTR.earliestFutureArrival_cons_cases
            head
            remaining
            now
            arrival
            hEarliest
        with
          ⟨hHeadArrival, hArrivalFuture⟩ |
            hRemaining

      · exact
          ⟨head,
           ⟨by simp,
            ⟨hHeadArrival,
             hArrivalFuture⟩⟩⟩

      · rcases
            inductionHypothesis
              hRemaining
          with
            ⟨message,
             hMember,
             hMessageArrival,
             hMessageFuture⟩

        exact
          ⟨message,
           ⟨by simp [hMember],
            ⟨hMessageArrival,
             hMessageFuture⟩⟩⟩

/--
Whenever some message of the bag arrives ahead of `now`, there is an answer.

The mirror of `earliestDueArrival_complete`, and it is what stops a `timeProgress`
premise of the form `nextArrival … = some future` from being unusable: such a rule
would never fire if this function could answer `none` while a future message sat in
a bag.

As with the due version the answer need not be the arrival of the message supplied.
An earlier future arrival elsewhere wins, which is the point of taking a minimum, so
only existence is claimed here. Minimality is the theorem after this one.
-/
theorem earliestFutureArrival_complete
    (bag : DTR.GeneralMessageBag)
    (now : LogicalTime)
    (message : DTR.GeneralMessage)
    (hMember :
      message ∈ bag)
    (hFuture :
      now < message.arrival) :
    ∃ arrival,
      DTR.earliestFutureArrival
          bag
          now =
        some arrival := by

  induction bag with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      by_cases hHeadFuture :
          now < head.arrival

      · rcases
            optionCases
              (DTR.earliestFutureArrival
                remaining
                now)
          with
            hRemaining |
              ⟨best, hRemaining⟩

        · exact
            ⟨head.arrival,
             DTR.earliestFutureArrival_cons_future_none
               head
               remaining
               now
               hHeadFuture
               hRemaining⟩

        · by_cases hBetter :
              head.arrival ≤ best

          · exact
              ⟨head.arrival,
               DTR.earliestFutureArrival_cons_future_some_le
                 head
                 remaining
                 now
                 best
                 hHeadFuture
                 hRemaining
                 hBetter⟩

          · exact
              ⟨best,
               DTR.earliestFutureArrival_cons_future_some_gt
                 head
                 remaining
                 now
                 best
                 hHeadFuture
                 hRemaining
                 hBetter⟩

      · simp only [
          List.mem_cons
        ] at hMember

        rcases hMember with
          hEqual |
            hRemainingMember

        · rw [hEqual] at hFuture

          exact
            absurd
              hFuture
              hHeadFuture

        · rw [
            DTR.earliestFutureArrival_cons_not_future
              head
              remaining
              now
              hHeadFuture
          ]

          exact
            inductionHypothesis
              hRemainingMember

/--
Nothing in the bag arrives strictly between `now` and the answer.

**This is the theorem F74 exists for.** Soundness alone would still let a time step
land on *some* real future arrival while stepping over an earlier one; this says the
answer really is the minimum, which is what makes `DTR.GeneralStep.timeProgress`
*match* the target's `timeAdvance` rather than merely resemble it.

It is also the theorem the due-arrival machinery never had. That family proves
soundness and completeness and stops there, so `earliest` was a name rather than a
claim, and nothing in the development ever asked a minimum to be minimal until a
source clock had to agree with a target tag.

The arrival is quantified inside the statement rather than taken as a parameter,
because the induction needs a fresh one for the tail: the minimum of a tail is not in
general the minimum of the whole bag, so an arrival fixed before the induction would
give an induction hypothesis too weak to use.
-/
theorem earliestFutureArrival_minimal
    (bag : DTR.GeneralMessageBag)
    (now : LogicalTime)
    (message : DTR.GeneralMessage)
    (hMember :
      message ∈ bag)
    (hFuture :
      now < message.arrival) :
    ∀ arrival,
      DTR.earliestFutureArrival
            bag
            now =
          some arrival →
        arrival ≤ message.arrival := by

  induction bag with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      intro arrival hEarliest

      simp only [
        List.mem_cons
      ] at hMember

      rcases hMember with
        hEqual |
          hRemainingMember

      · rw [← hEqual] at hEarliest

        rcases
            optionCases
              (DTR.earliestFutureArrival
                remaining
                now)
          with
            hRemaining |
              ⟨best, hRemaining⟩

        · rw [
            DTR.earliestFutureArrival_cons_future_none
              message
              remaining
              now
              hFuture
              hRemaining
          ] at hEarliest

          simp only [
            Option.some.injEq
          ] at hEarliest

          exact
            Nat.le_of_eq
              hEarliest.symm

        · by_cases hBetter :
              message.arrival ≤ best

          · rw [
              DTR.earliestFutureArrival_cons_future_some_le
                message
                remaining
                now
                best
                hFuture
                hRemaining
                hBetter
            ] at hEarliest

            simp only [
              Option.some.injEq
            ] at hEarliest

            exact
              Nat.le_of_eq
                hEarliest.symm

          · rw [
              DTR.earliestFutureArrival_cons_future_some_gt
                message
                remaining
                now
                best
                hFuture
                hRemaining
                hBetter
            ] at hEarliest

            simp only [
              Option.some.injEq
            ] at hEarliest

            rcases
                Nat.lt_or_ge
                  message.arrival
                  best
              with
                hLess |
                  hAtLeast

            · exact
                absurd
                  (Nat.le_of_lt
                    hLess)
                  hBetter

            · exact
                Nat.le_trans
                  (Nat.le_of_eq
                    hEarliest.symm)
                  hAtLeast

      · rcases
            DTR.earliestFutureArrival_complete
              remaining
              now
              message
              hRemainingMember
              hFuture
          with
            ⟨best, hRemaining⟩

        have hBestAtMost :
            best ≤ message.arrival :=
          inductionHypothesis
            hRemainingMember
            best
            hRemaining

        by_cases hHeadFuture :
            now < head.arrival

        · by_cases hBetter :
              head.arrival ≤ best

          · rw [
              DTR.earliestFutureArrival_cons_future_some_le
                head
                remaining
                now
                best
                hHeadFuture
                hRemaining
                hBetter
            ] at hEarliest

            simp only [
              Option.some.injEq
            ] at hEarliest

            exact
              Nat.le_trans
                (Nat.le_of_eq
                  hEarliest.symm)
                (Nat.le_trans
                  hBetter
                  hBestAtMost)

          · rw [
              DTR.earliestFutureArrival_cons_future_some_gt
                head
                remaining
                now
                best
                hHeadFuture
                hRemaining
                hBetter
            ] at hEarliest

            simp only [
              Option.some.injEq
            ] at hEarliest

            exact
              Nat.le_trans
                (Nat.le_of_eq
                  hEarliest.symm)
                hBestAtMost

        · rw [
            DTR.earliestFutureArrival_cons_not_future
              head
              remaining
              now
              hHeadFuture,
            hRemaining
          ] at hEarliest

          simp only [
            Option.some.injEq
          ] at hEarliest

          exact
            Nat.le_trans
              (Nat.le_of_eq
                hEarliest.symm)
              hBestAtMost


/-!
### What `earliestFutureArrivalOf` guarantees

The bag-level development above is not enough for Lemma 1. `timeProgress` reads the
*configuration*, through `GeneralConfiguration.nextArrival`, so all three properties
have to travel from one bag to the whole store — and the store's minimum is folded
over a different shape. `earliestFutureArrival` filters messages and keeps a running
best; `earliestFutureArrivalOf` combines two `Option`s per key-value pair, one from
the head bag and one from the tail store. Neither the statements nor the proofs
transfer by renaming, which is why §13 of `docs/STAGE_G_DESIGN.md` makes this row 7's
work rather than part of the F74 repair that introduced the definition.

Soundness produces *three* witnesses here instead of one — an actor name, that
actor's state, and a message of its bag. The extra two are not decoration: Lemma 1's
backward direction starts from a target event, and what it needs from the source side
is the actor that owns the corresponding message, not only the time.
-/

/--
A head actor with nothing ahead of `now` contributes nothing, and the answer is the
tail's.
-/
theorem earliestFutureArrivalOf_cons_none
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (remaining : Store ActorName DTR.GeneralActorState)
    (now : LogicalTime)
    (hHead :
      DTR.earliestFutureArrival
          state.bag
          now =
        none) :
    DTR.earliestFutureArrivalOf
        ((name, state) :: remaining)
        now =
      DTR.earliestFutureArrivalOf
        remaining
        now := by
  simp [
    DTR.earliestFutureArrivalOf,
    hHead
  ]

/--
A head actor with something ahead of `now`, and a tail with nothing, answers with the
head's arrival.
-/
theorem earliestFutureArrivalOf_cons_some_none
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (remaining : Store ActorName DTR.GeneralActorState)
    (now arrival : LogicalTime)
    (hHead :
      DTR.earliestFutureArrival
          state.bag
          now =
        some arrival)
    (hRemaining :
      DTR.earliestFutureArrivalOf
          remaining
          now =
        none) :
    DTR.earliestFutureArrivalOf
        ((name, state) :: remaining)
        now =
      some arrival := by
  simp [
    DTR.earliestFutureArrivalOf,
    hHead,
    hRemaining
  ]

/--
Both sides answer, and the head's arrival is no later, so the head's arrival wins.
-/
theorem earliestFutureArrivalOf_cons_some_le
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (remaining : Store ActorName DTR.GeneralActorState)
    (now arrival best : LogicalTime)
    (hHead :
      DTR.earliestFutureArrival
          state.bag
          now =
        some arrival)
    (hRemaining :
      DTR.earliestFutureArrivalOf
          remaining
          now =
        some best)
    (hBetter :
      arrival ≤ best) :
    DTR.earliestFutureArrivalOf
        ((name, state) :: remaining)
        now =
      some arrival := by
  simp [
    DTR.earliestFutureArrivalOf,
    hHead,
    hRemaining,
    hBetter
  ]

/--
Both sides answer and the tail's is strictly earlier, so the tail's answer stands.
-/
theorem earliestFutureArrivalOf_cons_some_gt
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (remaining : Store ActorName DTR.GeneralActorState)
    (now arrival best : LogicalTime)
    (hHead :
      DTR.earliestFutureArrival
          state.bag
          now =
        some arrival)
    (hRemaining :
      DTR.earliestFutureArrivalOf
          remaining
          now =
        some best)
    (hNotBetter :
      ¬ arrival ≤ best) :
    DTR.earliestFutureArrivalOf
        ((name, state) :: remaining)
        now =
      some best := by
  simp [
    DTR.earliestFutureArrivalOf,
    hHead,
    hRemaining,
    hNotBetter
  ]

/--
An answer for a non-empty store came either from the head actor's bag or from the
tail store.

Mirrors `earliestFutureArrival_cons_cases` and is stated for the same reason: no
induction hypothesis is in scope, so the case analysis on the two recursive answers
cannot interact with one.

What this lemma deliberately *loses* is why a branch was taken. `earliestFutureArrivalOf_minimal`
therefore does not use it, and splits inline instead — in the branch where the tail
wins, minimality needs the rejected head answer, and this disjunction has thrown it
away.
-/
theorem earliestFutureArrivalOf_cons_cases
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (remaining : Store ActorName DTR.GeneralActorState)
    (now answer : LogicalTime)
    (hEarliest :
      DTR.earliestFutureArrivalOf
          ((name, state) :: remaining)
          now =
        some answer) :
    DTR.earliestFutureArrival
          state.bag
          now =
        some answer ∨
      DTR.earliestFutureArrivalOf
          remaining
          now =
        some answer := by

  rcases
      optionCases
        (DTR.earliestFutureArrival
          state.bag
          now)
    with
      hHead |
        ⟨arrival, hHead⟩

  · rw [
      DTR.earliestFutureArrivalOf_cons_none
        name
        state
        remaining
        now
        hHead
    ] at hEarliest

    exact
      Or.inr
        hEarliest

  · rcases
        optionCases
          (DTR.earliestFutureArrivalOf
            remaining
            now)
      with
        hRemaining |
          ⟨best, hRemaining⟩

    · rw [
        DTR.earliestFutureArrivalOf_cons_some_none
          name
          state
          remaining
          now
          arrival
          hHead
          hRemaining
      ] at hEarliest

      simp only [
        Option.some.injEq
      ] at hEarliest

      refine
        Or.inl
          ?_

      rw [hHead, hEarliest]

    · by_cases hBetter :
          arrival ≤ best

      · rw [
          DTR.earliestFutureArrivalOf_cons_some_le
            name
            state
            remaining
            now
            arrival
            best
            hHead
            hRemaining
            hBetter
        ] at hEarliest

        simp only [
          Option.some.injEq
        ] at hEarliest

        refine
          Or.inl
            ?_

        rw [hHead, hEarliest]

      · rw [
          DTR.earliestFutureArrivalOf_cons_some_gt
            name
            state
            remaining
            now
            arrival
            best
            hHead
            hRemaining
            hBetter
        ] at hEarliest

        simp only [
          Option.some.injEq
        ] at hEarliest

        refine
          Or.inr
            ?_

        rw [hRemaining, hEarliest]

/--
Whatever the head bag answers, a store whose *tail* has an answer has one too.

Split out of `earliestFutureArrivalOf_complete` because both of its cases need it and
neither needs the answer itself. The three-way branch on the head is the whole content.
-/
theorem earliestFutureArrivalOf_cons_of_remaining
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (remaining : Store ActorName DTR.GeneralActorState)
    (now best : LogicalTime)
    (hRemaining :
      DTR.earliestFutureArrivalOf
          remaining
          now =
        some best) :
    ∃ answer,
      DTR.earliestFutureArrivalOf
          ((name, state) :: remaining)
          now =
        some answer := by

  rcases
      optionCases
        (DTR.earliestFutureArrival
          state.bag
          now)
    with
      hHead |
        ⟨arrival, hHead⟩

  · exact
      ⟨best,
       by
         rw [
           DTR.earliestFutureArrivalOf_cons_none
             name
             state
             remaining
             now
             hHead
         ]
         exact hRemaining⟩

  · by_cases hBetter :
        arrival ≤ best

    · exact
        ⟨arrival,
         DTR.earliestFutureArrivalOf_cons_some_le
           name
           state
           remaining
           now
           arrival
           best
           hHead
           hRemaining
           hBetter⟩

    · exact
        ⟨best,
         DTR.earliestFutureArrivalOf_cons_some_gt
           name
           state
           remaining
           now
           arrival
           best
           hHead
           hRemaining
           hBetter⟩

/--
Whatever the tail answers, a store whose *head bag* has an answer has one too.

The mirror of the lemma above, and the reason both exist rather than one: the head and
the tail enter `earliestFutureArrivalOf` through different `match` scrutinees, so a
single lemma would have to case on both anyway.
-/
theorem earliestFutureArrivalOf_cons_of_head
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (remaining : Store ActorName DTR.GeneralActorState)
    (now arrival : LogicalTime)
    (hHead :
      DTR.earliestFutureArrival
          state.bag
          now =
        some arrival) :
    ∃ answer,
      DTR.earliestFutureArrivalOf
          ((name, state) :: remaining)
          now =
        some answer := by

  rcases
      optionCases
        (DTR.earliestFutureArrivalOf
          remaining
          now)
    with
      hRemaining |
        ⟨best, hRemaining⟩

  · exact
      ⟨arrival,
       DTR.earliestFutureArrivalOf_cons_some_none
         name
         state
         remaining
         now
         arrival
         hHead
         hRemaining⟩

  · by_cases hBetter :
        arrival ≤ best

    · exact
        ⟨arrival,
         DTR.earliestFutureArrivalOf_cons_some_le
           name
           state
           remaining
           now
           arrival
           best
           hHead
           hRemaining
           hBetter⟩

    · exact
        ⟨best,
         DTR.earliestFutureArrivalOf_cons_some_gt
           name
           state
           remaining
           now
           arrival
           best
           hHead
           hRemaining
           hBetter⟩

/--
Every store-level answer names a real message of a real actor's bag, and that message
really is ahead.

Three witnesses, for the reason the section header gives. The name is what makes this
usable from the correspondence relation, whose per-actor components are indexed by
exactly this key.
-/
theorem earliestFutureArrivalOf_sound
    (actors :
      Store ActorName DTR.GeneralActorState)
    (now answer : LogicalTime)
    (hEarliest :
      DTR.earliestFutureArrivalOf
          actors
          now =
        some answer) :
    ∃ name state message,
      (name, state) ∈ actors ∧
        message ∈ state.bag ∧
          message.arrival = answer ∧
            now < answer := by

  induction actors with

  | nil =>
      simp [
        DTR.earliestFutureArrivalOf
      ] at hEarliest

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨name, state⟩

      rcases
          DTR.earliestFutureArrivalOf_cons_cases
            name
            state
            remaining
            now
            answer
            hEarliest
        with
          hHead |
            hRemaining

      · rcases
            DTR.earliestFutureArrival_sound
              state.bag
              now
              answer
              hHead
          with
            ⟨message,
             hMember,
             hArrival,
             hFuture⟩

        exact
          ⟨name,
           state,
           message,
           by simp,
           hMember,
           hArrival,
           hFuture⟩

      · rcases
            inductionHypothesis
              hRemaining
          with
            ⟨witnessName,
             witnessState,
             witnessMessage,
             hWitnessMember,
             hWitnessBag,
             hWitnessArrival,
             hWitnessFuture⟩

        exact
          ⟨witnessName,
           witnessState,
           witnessMessage,
           by simp [hWitnessMember],
           hWitnessBag,
           hWitnessArrival,
           hWitnessFuture⟩

/--
Any actor of the store with anything ahead of `now` forces an answer.

This is the direction `timeProgress` needs in order to be *enabled*: without it the
rule could be blocked by a `none` while a message sat in some bag ahead of the clock,
and the source would deadlock where the target advances.
-/
theorem earliestFutureArrivalOf_complete
    (actors :
      Store ActorName DTR.GeneralActorState)
    (now : LogicalTime)
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (message : DTR.GeneralMessage)
    (hMember :
      (name, state) ∈ actors)
    (hBagMember :
      message ∈ state.bag)
    (hFuture :
      now < message.arrival) :
    ∃ answer,
      DTR.earliestFutureArrivalOf
          actors
          now =
        some answer := by

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

      · have hStates :
            state = headState := by
          simp only [
            Prod.mk.injEq
          ] at hEqual
          exact hEqual.right

        have hHeadBag :
            message ∈ headState.bag := by
          rw [← hStates]
          exact hBagMember

        rcases
            DTR.earliestFutureArrival_complete
              headState.bag
              now
              message
              hHeadBag
              hFuture
          with
            ⟨arrival, hHead⟩

        exact
          DTR.earliestFutureArrivalOf_cons_of_head
            headName
            headState
            remaining
            now
            arrival
            hHead

      · rcases
            inductionHypothesis
              hRemainingMember
          with
            ⟨best, hRemaining⟩

        exact
          DTR.earliestFutureArrivalOf_cons_of_remaining
            headName
            headState
            remaining
            now
            best
            hRemaining

/--
The store-level answer really is the minimum, over every bag of every actor.

This is the theorem F74 was missing at the configuration level, and it is what makes
`DTR.GeneralStep.timeProgress` *match* `LF.GeneralStep.timeAdvance` rather than merely
resemble it: without it the source clock could name a real arrival while skipping an
earlier one in a different actor's bag, which is precisely the defect in its
cross-actor form.

`earliestFutureArrivalOf_cons_cases` is deliberately unused here. In the branch where
the tail's answer wins, minimality needs the head's rejected answer and the inequality
that rejected it, and the disjunction has discarded both — so the four-way split is
written out, exactly as `earliestFutureArrival_minimal` writes out its own.
-/
theorem earliestFutureArrivalOf_minimal
    (actors :
      Store ActorName DTR.GeneralActorState)
    (now : LogicalTime)
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (message : DTR.GeneralMessage)
    (hMember :
      (name, state) ∈ actors)
    (hBagMember :
      message ∈ state.bag)
    (hFuture :
      now < message.arrival) :
    ∀ answer,
      DTR.earliestFutureArrivalOf
            actors
            now =
          some answer →
        answer ≤ message.arrival := by

  induction actors with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨headName, headState⟩

      intro answer hEarliest

      simp only [
        List.mem_cons
      ] at hMember

      rcases hMember with
        hEqual |
          hRemainingMember

      · have hStates :
            state = headState := by
          simp only [
            Prod.mk.injEq
          ] at hEqual
          exact hEqual.right

        have hHeadBag :
            message ∈ headState.bag := by
          rw [← hStates]
          exact hBagMember

        rcases
            DTR.earliestFutureArrival_complete
              headState.bag
              now
              message
              hHeadBag
              hFuture
          with
            ⟨arrival, hHead⟩

        have hArrivalAtMost :
            arrival ≤ message.arrival :=
          DTR.earliestFutureArrival_minimal
            headState.bag
            now
            message
            hHeadBag
            hFuture
            arrival
            hHead

        rcases
            optionCases
              (DTR.earliestFutureArrivalOf
                remaining
                now)
          with
            hRemaining |
              ⟨best, hRemaining⟩

        · rw [
            DTR.earliestFutureArrivalOf_cons_some_none
              headName
              headState
              remaining
              now
              arrival
              hHead
              hRemaining
          ] at hEarliest

          simp only [
            Option.some.injEq
          ] at hEarliest

          exact
            Nat.le_trans
              (Nat.le_of_eq
                hEarliest.symm)
              hArrivalAtMost

        · by_cases hBetter :
              arrival ≤ best

          · rw [
              DTR.earliestFutureArrivalOf_cons_some_le
                headName
                headState
                remaining
                now
                arrival
                best
                hHead
                hRemaining
                hBetter
            ] at hEarliest

            simp only [
              Option.some.injEq
            ] at hEarliest

            exact
              Nat.le_trans
                (Nat.le_of_eq
                  hEarliest.symm)
                hArrivalAtMost

          · rw [
              DTR.earliestFutureArrivalOf_cons_some_gt
                headName
                headState
                remaining
                now
                arrival
                best
                hHead
                hRemaining
                hBetter
            ] at hEarliest

            simp only [
              Option.some.injEq
            ] at hEarliest

            rcases
                Nat.lt_or_ge
                  arrival
                  best
              with
                hLess |
                  hAtLeast

            · exact
                absurd
                  (Nat.le_of_lt
                    hLess)
                  hBetter

            · exact
                Nat.le_trans
                  (Nat.le_of_eq
                    hEarliest.symm)
                  (Nat.le_trans
                    hAtLeast
                    hArrivalAtMost)

      · rcases
            DTR.earliestFutureArrivalOf_complete
              remaining
              now
              name
              state
              message
              hRemainingMember
              hBagMember
              hFuture
          with
            ⟨best, hRemaining⟩

        have hBestAtMost :
            best ≤ message.arrival :=
          inductionHypothesis
            hRemainingMember
            best
            hRemaining

        rcases
            optionCases
              (DTR.earliestFutureArrival
                headState.bag
                now)
          with
            hHead |
              ⟨arrival, hHead⟩

        · rw [
            DTR.earliestFutureArrivalOf_cons_none
              headName
              headState
              remaining
              now
              hHead,
            hRemaining
          ] at hEarliest

          simp only [
            Option.some.injEq
          ] at hEarliest

          exact
            Nat.le_trans
              (Nat.le_of_eq
                hEarliest.symm)
              hBestAtMost

        · by_cases hBetter :
              arrival ≤ best

          · rw [
              DTR.earliestFutureArrivalOf_cons_some_le
                headName
                headState
                remaining
                now
                arrival
                best
                hHead
                hRemaining
                hBetter
            ] at hEarliest

            simp only [
              Option.some.injEq
            ] at hEarliest

            exact
              Nat.le_trans
                (Nat.le_of_eq
                  hEarliest.symm)
                (Nat.le_trans
                  hBetter
                  hBestAtMost)

          · rw [
              DTR.earliestFutureArrivalOf_cons_some_gt
                headName
                headState
                remaining
                now
                arrival
                best
                hHead
                hRemaining
                hBetter
            ] at hEarliest

            simp only [
              Option.some.injEq
            ] at hEarliest

            exact
              Nat.le_trans
                (Nat.le_of_eq
                  hEarliest.symm)
                hBestAtMost


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

/--
The next arrival ahead of a configuration's current time, if there is one.

This is the paper's `ar_min` with the `π_x = ϵ` restriction dropped for the reason
the section header gives, and `DTR.GeneralStep.timeProgress` advances to exactly
this time rather than to any later one (**F74**). `none` means no message is pending
anywhere ahead of `now`, and then the clock does not move at all — matching the
target, whose `timeAdvance` needs an event in its queue to advance to.
-/
def nextArrival
    (config : DTR.GeneralConfiguration) :
    Option LogicalTime :=
  DTR.earliestFutureArrivalOf
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

/--
Under quiescence every waiting message is strictly in the future.

The contrapositive of completeness, and the bridge between the two things the source's time rule is
premised on. `DTR.GeneralStep.timeProgress` carries quiescence — an empty cohort — while the arrival
minimum `nextArrival` is taken over messages *strictly after* `now`. Nothing connects those two on its
own: a bag could hold a message that is already due, which quiescence would then have to rule out, and
`earliestDueArrival` is the function that knows the difference. This theorem spends that knowledge once,
here, so that the correspondence development can treat "quiescent" as "every bagged message is future"
without re-deriving it at each use.

It is the source-side half of Lemma 1's time case. The target-side half is
`LF.GeneralRuntimeState.earliestPendingEvent?_precedesOrEqual_of_mem`; between them the two languages'
notions of *the next instant* are comparable in both directions.

Proved by the comparison split rather than by `omega`, because **F72** measured that `omega` does not see
through the `LogicalTime` abbreviation. The due branch builds the cohort member that quiescence forbids:
`earliestDueArrival_complete` turns one due message into an answer for the whole bag, `readyActors_complete`
turns that answer into a cohort entry, and rewriting by the quiescence hypothesis leaves a membership in the
empty list, which has no constructors.
-/
theorem arrival_future_of_readyActors_nil
    (config : DTR.GeneralConfiguration)
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (message : DTR.GeneralMessage)
    (hQuiescent :
      config.readyActors = [])
    (hMember :
      (name, state) ∈ config.actors)
    (hBagMember :
      message ∈ state.bag) :
    config.now < message.arrival := by

  rcases Nat.lt_or_ge config.now message.arrival with
    hFuture |
      hAtLeast

  · exact hFuture

  · obtain ⟨arrival, hArrival⟩ :=
      DTR.earliestDueArrival_complete
        state.bag
        config.now
        message
        hBagMember
        hAtLeast

    have hDueArrival :
        state.dueArrival config.now =
          some arrival :=
      hArrival

    have hReady :
        (
          {
            actorName := name
            logicalTime := arrival
          } : ReadyActor
        ) ∈
          config.readyActors :=
      DTR.readyActors_complete
        config
        name
        state
        arrival
        hMember
        hDueArrival

    rw [hQuiescent] at hReady

    cases hReady

/-!
### What nextArrival guarantees

Three theorems, one per direction the correspondence needs, each delegating to the
store-level development above in the same way the cohort theorems delegate to
`readyActorsOf`.

These are the theorems `DTR.GeneralStep.timeProgress`'s third premise was added for.
On their own the premise is only a constraint; with them it is the paper's `ar_min`,
and Lemma 1's time case can pair a source advance with the target's `timeAdvance`
because both name the same instant: the target's by construction, ours by
`nextArrival_sound` and `nextArrival_minimal` together.
-/

/--
Whatever the clock advances to, some actor really is waiting for a message then.

Both the actor and the message are produced, not just the time, because the
correspondence relation is indexed per actor: the reactor whose pending event must
match this arrival is found through the actor's name.
-/
theorem nextArrival_sound
    (config : DTR.GeneralConfiguration)
    (answer : LogicalTime)
    (hNext :
      config.nextArrival =
        some answer) :
    ∃ name state message,
      (name, state) ∈ config.actors ∧
        message ∈ state.bag ∧
          message.arrival = answer ∧
            config.now < answer := by

  unfold GeneralConfiguration.nextArrival at hNext

  exact
    DTR.earliestFutureArrivalOf_sound
      config.actors
      config.now
      answer
      hNext

/--
The clock can always advance when anything at all is waiting ahead of it.

Together with quiescence this is what rules out a source deadlock at a
configuration whose target still has a queue to drain.
-/
theorem nextArrival_complete
    (config : DTR.GeneralConfiguration)
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (message : DTR.GeneralMessage)
    (hMember :
      (name, state) ∈ config.actors)
    (hBagMember :
      message ∈ state.bag)
    (hFuture :
      config.now < message.arrival) :
    ∃ answer,
      config.nextArrival =
        some answer := by

  unfold GeneralConfiguration.nextArrival

  exact
    DTR.earliestFutureArrivalOf_complete
      config.actors
      config.now
      name
      state
      message
      hMember
      hBagMember
      hFuture

/--
The clock never steps over a waiting message, in any actor's bag.

This is the theorem whose absence made **F74**: with `timeProgress` premised only on
`config.now < future` and quiescence, a configuration holding one message arriving at
5 could advance to 100, while the target could only ever reach 5. The cross-actor
form is the one that matters, and it is why the minimum is taken over the whole
store rather than one bag at a time.
-/
theorem nextArrival_minimal
    (config : DTR.GeneralConfiguration)
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (message : DTR.GeneralMessage)
    (hMember :
      (name, state) ∈ config.actors)
    (hBagMember :
      message ∈ state.bag)
    (hFuture :
      config.now < message.arrival) :
    ∀ answer,
      config.nextArrival =
          some answer →
        answer ≤ message.arrival := by

  unfold GeneralConfiguration.nextArrival

  exact
    DTR.earliestFutureArrivalOf_minimal
      config.actors
      config.now
      name
      state
      message
      hMember
      hBagMember
      hFuture

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
