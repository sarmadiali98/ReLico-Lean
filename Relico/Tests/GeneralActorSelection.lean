import Relico.DTR.GeneralActorSelection

set_option autoImplicit false

/-!
# Value-level pins for general actor selection

`docs/STAGE_G_DESIGN.md` §5. `Relico/DTR/GeneralActorSelection.lean` proves that the selected actor is a
member of the cohort, that it precedes every member, that selection succeeds exactly when the cohort is
non-empty, and — under a distinctness guard — that it is the only minimum. This module pins the things
those theorems are structurally unable to see.

## Why the theorems are not enough

**Minimality cannot see which key is compared first.** `selectedActor_minimal` is a statement *relative to*
`PrecedesOrEqual`. If that relation compared priority first and arrival second, the selected actor would
still precede every member of the cohort and the theorem would still be true. The lexicographic order is
therefore a claim no theorem in the definition module states, and only a value pin can fix it. That claim
is the one the design settled by measurement: `earliestDueArrival` minimises arrival *among the messages
due at now* rather than requiring a unique arrival, so a cohort with mixed arrivals is reachable, and a
priority-first rule would let a later-arriving message overtake an earlier one.
`selection_minimum_prefers_earlier_arrival` and `selection_selected_actor_prefers_earlier_arrival` are that
counterexample as a regression: both hold a cohort in which the *worse-prioritised* actor is selected
because it arrived first, so a priority-first reading fails them.

**Nothing in the definition module can see tie order.** `PrecedesOrEqual` is reflexive, so when two actors
tie on both keys each precedes the other and `selectedActor_minimal` is satisfied by either choice.
`selectedActor_unique` does not close the gap either: it applies only under the distinctness guard, which a
tie violates by construction. So the tie-breaking rule — first position in the cohort, which
`readyActorsOf` inherits from the configuration's actor store — is pinned only by
`selection_minimum_tie_stability` and its swapped twin, in the same shape decision `0041` fixed for the
stage F sorts.

**Nothing states the direction of the absence convention.** Selection inherits it from
`GeneralPriority.PriorityPrecedesOrEqual`, which places `none` last. Were that relation reversed, every
theorem in the definition module would still hold, with unannotated actors selected first.
`selection_unannotated_does_not_precede_explicit` pins the direction at the relation level and
`selection_minimum_prefers_explicit_over_unannotated` pins it at the value level.

## Why the guard is pinned in both directions

`selectedActor_unique`'s hypotheses are a distinctness guard and a cohort-declaredness side condition, and
a theorem whose hypotheses are unsatisfiable proves nothing. `selection_model_priorities_nodup` shows the
guard holds of a model with three actors, and `selection_tied_model_priorities_not_nodup` shows it fails of
a four-actor model whose only defect is a second unannotated actor — so the guard is neither vacuous nor
unsatisfiable, and the `Nodup`-over-`Option Nat` reading that forbids two absences as well as two equal
numbers is pinned as intended rather than assumed.
`selection_unique_at_mixed_configuration` then discharges every non-quantified hypothesis at the fixtures,
which is the anti-vacuity witness for the theorem as a whole.
-/

namespace Relico
namespace Tests

open DTR.GlobalMultiStorePayloadActorPriority

/-!
## Actor-instance fixtures

Three instances of one class differing only in name and priority, plus a fourth that duplicates the third's
absent priority. `bindings` and `arguments` are empty because selection reads neither; `className` is shared
because selection never resolves a class. The names carry the priority rather than the arrival, because an
instance has a priority and an arrival belongs to a message.
-/

def selectionClassName :
    ClassName :=
  ⟨"SelectionSubject"⟩

def selectionActorFast :
    DTR.GeneralActorInstance where

  name :=
    ⟨"selectionActorFast"⟩

  className :=
    selectionClassName

  bindings :=
    []

  arguments :=
    []

  priority :=
    some 1

def selectionActorSlow :
    DTR.GeneralActorInstance where

  name :=
    ⟨"selectionActorSlow"⟩

  className :=
    selectionClassName

  bindings :=
    []

  arguments :=
    []

  priority :=
    some 4

def selectionActorPlain :
    DTR.GeneralActorInstance where

  name :=
    ⟨"selectionActorPlain"⟩

  className :=
    selectionClassName

  bindings :=
    []

  arguments :=
    []

  priority :=
    none

def selectionActorPlainSecond :
    DTR.GeneralActorInstance where

  name :=
    ⟨"selectionActorPlainSecond"⟩

  className :=
    selectionClassName

  bindings :=
    []

  arguments :=
    []

  priority :=
    none

/-!
## Models

`classes` is empty in both. Selection resolves a priority through `DTR.GeneralModel.actor?`, which reads
`instances` only, so a class list would be dead fixture weight — and leaving it empty also records that
none of these pins depends on well-formedness, which selection does not require.

The two models differ by exactly one instance, and that instance's only distinguishing feature is that its
priority is absent like `selectionActorPlain`'s. That is what makes the pair a pin on the distinctness
guard rather than on anything else.
-/

def selectionModel :
    DTR.GeneralModel where

  classes :=
    []

  instances := [
    selectionActorFast,
    selectionActorSlow,
    selectionActorPlain
  ]

def selectionTiedModel :
    DTR.GeneralModel where

  classes :=
    []

  instances := [
    selectionActorFast,
    selectionActorSlow,
    selectionActorPlain,
    selectionActorPlainSecond
  ]

/-!
## Ready-actor fixtures

A `ReadyActor` pairs a name with the arrival its own bag determined, so these are the cohort entries a
configuration would produce. They are written directly here so that the ordering pins below are about the
order and not about the cohort computation; the configurations in section 6 exercise that separately.

`selectionFastLate` is the fixture that matters: the best priority in the file paired with the latest
arrival.
-/

def selectionFastLate :
    ReadyActor where

  actorName :=
    ⟨"selectionActorFast"⟩

  logicalTime :=
    5

def selectionFastEarly :
    ReadyActor where

  actorName :=
    ⟨"selectionActorFast"⟩

  logicalTime :=
    3

def selectionSlowEarly :
    ReadyActor where

  actorName :=
    ⟨"selectionActorSlow"⟩

  logicalTime :=
    3

def selectionPlainEarly :
    ReadyActor where

  actorName :=
    ⟨"selectionActorPlain"⟩

  logicalTime :=
    3

def selectionPlainSecondEarly :
    ReadyActor where

  actorName :=
    ⟨"selectionActorPlainSecond"⟩

  logicalTime :=
    3

/-!
## The order relation, at concrete pairs

These three pins fix the shape of the key. The first is the refutation of the priority-first reading stated
at the relation level; the second says priority is consulted at all; the third fixes the direction of the
absence convention, which is inherited rather than restated and so has no pin of its own in the definition
module.
-/

/--
An earlier arrival precedes a better priority.

`selectionPlainEarly` carries no priority and `selectionFastLate` carries the best one in the file, and the
earlier arrival still wins. A priority-first order would make this false.
-/
theorem selection_earlier_arrival_precedes_better_priority :
    DTR.GeneralActorSelection.PrecedesOrEqual
      selectionModel
      selectionPlainEarly
      selectionFastLate :=
  Or.inl
    (by decide)

/--
At equal arrival, the smaller numeric priority precedes.
-/
theorem selection_better_priority_precedes_at_equal_arrival :
    DTR.GeneralActorSelection.PrecedesOrEqual
      selectionModel
      selectionFastEarly
      selectionSlowEarly := by

  refine
    Or.inr
      ⟨rfl, ?_⟩

  show
    DTR.GeneralPriority.PriorityPrecedesOrEqual
      (some 1)
      (some 4)

  exact
    DTR.GeneralPriority.priority_lower_numeric_precedes
      (by decide)

/--
An unannotated actor does not precede an explicitly prioritized one at equal arrival.

This is the direction of the convention. Were `PriorityPrecedesOrEqual` reversed, every theorem in
`Relico/DTR/GeneralActorSelection.lean` would still hold and this pin would fail.
-/
theorem selection_unannotated_does_not_precede_explicit :
    ¬ DTR.GeneralActorSelection.PrecedesOrEqual
        selectionModel
        selectionPlainEarly
        selectionSlowEarly := by
  decide

/-!
## `selectMinimum`, at concrete cohorts

The value pins. Each is a two-element cohort so that the expected output reads as an ordering claim, and in
each the input order is the one a wrong rule would return.
-/

/--
The earlier arrival is selected even though the other candidate has the better priority.

This is the pin the design's measurement forced. The cohort is mixed-arrival, which is reachable because
`earliestDueArrival` does not require a unique arrival among the messages due at now; a priority-first rule
would return `selectionFastLate` here.

`selectionFastLate` is also the element held first, so this pin additionally shows that the held element is
displaced when it should be, rather than surviving by position.
-/
theorem selection_minimum_prefers_earlier_arrival :
    DTR.GeneralActorSelection.selectMinimum
      selectionModel
      selectionFastLate [
        selectionPlainEarly
      ] =
      selectionPlainEarly := by
  rfl

/--
At equal arrival, priority decides, against cohort position.
-/
theorem selection_minimum_prefers_better_priority_at_equal_arrival :
    DTR.GeneralActorSelection.selectMinimum
      selectionModel
      selectionSlowEarly [
        selectionFastEarly
      ] =
      selectionFastEarly := by
  rfl

/--
At equal arrival, an explicit priority beats an absent one, against cohort position.
-/
theorem selection_minimum_prefers_explicit_over_unannotated :
    DTR.GeneralActorSelection.selectMinimum
      selectionModel
      selectionPlainEarly [
        selectionSlowEarly
      ] =
      selectionSlowEarly := by
  rfl

/--
A genuine tie falls back on cohort position.

Two unannotated actors at one arrival tie under both keys, so this is the case no theorem in the definition
module decides: minimality holds of either choice, and the uniqueness theorem excludes the case by its
guard. The model here is the tied one precisely because the guard fails of it.
-/
theorem selection_minimum_tie_stability :
    DTR.GeneralActorSelection.selectMinimum
      selectionTiedModel
      selectionPlainEarly [
        selectionPlainSecondEarly
      ] =
      selectionPlainEarly := by
  rfl

/--
The same tie, declared the other way round, selects the other actor.

Swapping the input swaps the output, which is what makes the previous pin a claim about position rather than
about the two actors.
-/
theorem selection_minimum_tie_stability_swapped :
    DTR.GeneralActorSelection.selectMinimum
      selectionTiedModel
      selectionPlainSecondEarly [
        selectionPlainEarly
      ] =
      selectionPlainSecondEarly := by
  rfl

/-!
## Configurations

The pins above are about the order. These are about the whole of `selectedActor`, which derives its cohort
from the configuration rather than receiving one: `readyActorsOf` walks the actor store in order and keeps
each actor whose bag has a message due at `now`, tagged with that message's arrival. So a configuration pin
also exercises `DTR.GeneralActorState.dueArrival` and the `now` gate, which no `selectMinimum` pin reaches.

One message per actor is enough, because the cohort records one arrival per actor whatever the bag holds.
The message's `sender` and `messageName` are never read by anything under test and are constant.
-/

def selectionTriggerAt
    (arrival : LogicalTime) :
    DTR.GeneralMessage where

  sender :=
    ⟨"selectionActorPlain"⟩

  messageName :=
    ⟨"selectionTrigger"⟩

  payload :=
    []

  arrival :=
    arrival

def selectionStateAt
    (arrival : LogicalTime) :
    DTR.GeneralActorState where

  valuation :=
    []

  bag := [
    selectionTriggerAt
      arrival
  ]

/--
Two actors due at different times, with the better-prioritized one arriving later.

The store order also favours the better-prioritized actor, so both position and priority point one way and
arrival points the other. This is the mixed-arrival configuration the design's measurement showed to be
reachable.

The fast actor's message arrives at `selectionFastLate`'s time, so the cohort this configuration derives is
exactly the two ready-actor fixtures the ordering pins above are stated at. That is what makes those pins
claims about a *reachable* cohort rather than about hand-built lists that no configuration produces.
-/
def selectionMixedConfiguration :
    DTR.GeneralConfiguration where

  now :=
    10

  actors := [
    (⟨"selectionActorFast"⟩,
      selectionStateAt
        5),
    (⟨"selectionActorPlain"⟩,
      selectionStateAt
        4)
  ]

/--
Two actors due at the same time, with the unannotated one first in the store.

Position and priority disagree, and arrival is silent, so this configuration isolates priority.
-/
def selectionEqualArrivalConfiguration :
    DTR.GeneralConfiguration where

  now :=
    10

  actors := [
    (⟨"selectionActorPlain"⟩,
      selectionStateAt
        4),
    (⟨"selectionActorFast"⟩,
      selectionStateAt
        4)
  ]

/--
Two actors with messages, neither due yet.

The bags are non-empty, so this distinguishes "nothing to do" from "no messages at all".
-/
def selectionIdleConfiguration :
    DTR.GeneralConfiguration where

  now :=
    2

  actors := [
    (⟨"selectionActorFast"⟩,
      selectionStateAt
        7),
    (⟨"selectionActorPlain"⟩,
      selectionStateAt
        4)
  ]

/--
The expected selection from `selectionMixedConfiguration`.
-/
def selectionPlainDue :
    ReadyActor where

  actorName :=
    ⟨"selectionActorPlain"⟩

  logicalTime :=
    4

/--
The expected selection from `selectionEqualArrivalConfiguration`.
-/
def selectionFastDue :
    ReadyActor where

  actorName :=
    ⟨"selectionActorFast"⟩

  logicalTime :=
    4

/-!
## `selectedActor`, at concrete configurations
-/

/--
The cohort of the mixed configuration, pinned separately from the selection.

Stated so that a failure below can be attributed: if this holds and the selection pin fails, the order is
wrong; if this fails, the cohort computation is.
-/
theorem selection_mixed_cohort :
    selectionMixedConfiguration.readyActors = [
      selectionFastLate,
      selectionPlainDue
    ] := by
  rfl

/--
The later-arriving actor is not selected, though it has the better priority and the earlier store position.

This is the file's central pin. A priority-first order returns `selectionFastLate`; the lexicographic order
returns `selectionPlainDue`.
-/
theorem selection_selected_actor_prefers_earlier_arrival :
    DTR.GeneralActorSelection.selectedActor
      selectionModel
      selectionMixedConfiguration =
      some selectionPlainDue := by
  rfl

/--
At equal arrival the better priority is selected, against store order.

Together with the previous pin this fixes both components of the key: arrival dominates, and priority is
consulted when arrival cannot decide. Neither pin alone excludes an order that ignores one of the two.
-/
theorem selection_selected_actor_prefers_priority_at_equal_arrival :
    DTR.GeneralActorSelection.selectedActor
      selectionModel
      selectionEqualArrivalConfiguration =
      some selectionFastDue := by
  rfl

/--
Nothing is selected when nothing is due, even though every bag is non-empty.
-/
theorem selection_selected_actor_none_when_nothing_due :
    DTR.GeneralActorSelection.selectedActor
      selectionModel
      selectionIdleConfiguration =
      none := by
  rfl

/-!
## The uniqueness guard

`DTR.GeneralActorSelection.selectedActor_unique` is guard-relative, so its hypotheses are worth pinning as
satisfiable *and* as refutable. A guard that always held would make the theorem unconditional and the
`Nodup` hypothesis decorative; a guard that never held would make it vacuous.
-/

/--
Three actors with distinct priorities satisfy the guard.
-/
theorem selection_model_priorities_nodup :
    selectionModel.actorPriorities.Nodup := by
  decide

/--
Adding a second unannotated actor breaks it.

This is the `Nodup`-over-`Option Nat` reading: two absences collide exactly as two equal numbers would. It
is also why the guard cannot be a well-formedness clause — models with several unannotated actors are
legal, and the tied model here is otherwise indistinguishable from the passing one.
-/
theorem selection_tied_model_priorities_not_nodup :
    ¬ selectionTiedModel.actorPriorities.Nodup := by
  decide

/--
Every member of the mixed configuration's cohort is a declared actor of the model.
-/
theorem selection_cohort_declared :
    DTR.GeneralActorSelection.CohortDeclared
      selectionModel
      selectionMixedConfiguration := by
  decide

/--
Uniqueness, with every non-quantified hypothesis discharged at the fixtures.

The anti-vacuity witness for `selectedActor_unique`: the guard, the declaredness condition and the selection
equation all hold simultaneously of one model and one configuration, so what remains is exactly the content
of the theorem — any ready actor that precedes the selected one *is* the selected one.
-/
theorem selection_unique_at_mixed_configuration
    (other : ReadyActor)
    (hMember :
      other ∈ selectionMixedConfiguration.readyActors)
    (hPrecedes :
      DTR.GeneralActorSelection.PrecedesOrEqual
        selectionModel
        other
        selectionPlainDue) :
    other = selectionPlainDue :=
  DTR.GeneralActorSelection.selectedActor_unique
    selection_model_priorities_nodup
    selection_cohort_declared
    selection_selected_actor_prefers_earlier_arrival
    hMember
    hPrecedes

end Tests
end Relico
