import Relico.DTR.GeneralState
import Relico.DTR.GeneralPriority

/-!
# Which ready actor takes the next step

Stage G's first obligation. `docs/STAGE_G_DESIGN.md` §5 owes a deterministic choice of the actor that
takes the next source transition, because the correctness statement stage G proves — the paper's
Theorem 1, weak bisimilarity — quantifies over source executions, and an execution is not determined
until the schedule is.

## Why the order is lexicographic rather than by priority

The obvious reading of the paper's actor priority is "the ready actor of least priority acts next".
That reading is **refuted by this repository's own state layer**. `DTR.GeneralActorState.dueArrival`
(`Relico/DTR/GeneralState.lean`) reports the earliest arrival *among the messages that are due at the
current time*; it does not require that arrival to be unique, and `DTR.readyActorsOf` records whatever
arrival each actor's own bag determines. A cohort whose members carry **different** arrivals is
therefore reachable, and in such a cohort a priority-first rule would let a message that arrived later
overtake one that arrived earlier — which contradicts the paper's arrival-ordered semantics, not just
this implementation.

So arrival is compared first and priority breaks arrival ties. That is exactly the shape of
`Relico/LF/Scheduling.lean`'s `LF.Tag.PrecedesOrEqual`, which compares logical time first and
microsteps second. The symmetry is deliberate: the source's selection order and the target's tag order
have the same structure, which is what stage G's Lemma 1 correspondence has to line up.

## Absence of a priority

`DTR.GeneralActorInstance.priority` is `Option Nat` and defaults to `none`, so an actor need not be
annotated. The convention is **not** chosen here: `GeneralPriority.PriorityPrecedesOrEqual` already
fixes it, and every explicit priority precedes an absent one. Reusing that relation rather than
restating it is what keeps selection order and the order stage F emits from drifting apart —
`Relico/Translation/GeneralRouting.lean`'s `priorityOrderedInstances` sorts by the same relation
through `DTR.GeneralActorPriority.normalize`.

## Priority is model data, and the cohort is not

`GlobalMultiStorePayloadActorPriority.ReadyActor` carries `actorName` and `logicalTime` and **no
priority field**, and `DTR.GeneralConfiguration.readyActors`'s docstring is explicit that the cohort is
a function of the configuration alone with nothing about the model consulted. Priority lives on
`DTR.GeneralActorInstance`. Selection therefore cannot be a function of the configuration alone: every
declaration below takes the model as well, and resolves a ready actor's priority through it.

For the same reason the cohort is **not** a parameter. It is derived from the configuration at the one
place it is needed. The four-module multi-store precedent under `Relico/DTR/` and `Relico/Correctness/`
does take a `ready` argument, and that argument is the defect
`DTR.readyActorsOf`'s discrimination theorem was written to pin: a caller may pass any list. Stage G
does not inherit it.

## The distinctness guard is stated raw

`selectedActor_unique` needs the priorities to be pairwise distinct, which is
`Relico/DTR/GeneralWellFormed.lean`'s `ActorPrioritiesDistinct`. It is stated here as the underlying
`List.Nodup` instead, for the reason `GeneralPriority.priorities_nodup_normalize` records for itself:
keeping the import surface at the syntax and state layers. Connecting the raw form to the named
predicate belongs in `Relico/Correctness/`, with stage G's other correspondence bridges.
-/

namespace Relico

namespace DTR

namespace GeneralActorSelection

open GlobalMultiStorePayloadActorPriority

/--
The priority a ready actor inherits from the model.

`ReadyActor` carries no priority field, so the model is consulted. The binder is `actor` rather than
`instance`, which is a Lean keyword — the same spelling `DTR.GeneralActorPriority.priorityOf` already
uses.

A ready actor whose name the model does not declare resolves to `none`, which the order below then
treats as an absent priority. That conflation is deliberate, and it is why `CohortDeclared` exists: the
theorem that needs to tell an unannotated actor apart from an undeclared one takes that hypothesis
instead of this definition pretending the case cannot arise.

The lookup goes through `DTR.GeneralModel.actor?` rather than reaching into `model.instances`, so this
definition inherits whatever that accessor is proved about — `DTR.GeneralModel.lookup_topology` is the
existing example.
-/
def priorityOf
    (model :
      DTR.GeneralModel)
    (ready :
      ReadyActor) :
    Option Nat :=
  match
      model.actor?
        ready.actorName with

  | none =>
      none

  | some actor =>
      actor.priority

/--
Every actor that a configuration reports ready is declared by the model.

This is an agreement condition between a configuration and a model, and nothing in the state layer
enforces it: `DTR.GeneralConfiguration.readyActors` reads the actor store, whose keys are whatever the
store was built with, while priorities live on `model.instances`. A configuration reached by running a
model satisfies it; an arbitrary pair of a model and a configuration need not.

It is a hypothesis rather than a clause of well-formedness because well-formedness in this project is
a predicate on *syntax*, and this is a statement about a reachable runtime value.
-/
def CohortDeclared
    (model :
      DTR.GeneralModel)
    (config :
      DTR.GeneralConfiguration) :
    Prop :=
  ∀ ready ∈ config.readyActors,
    (model.actor?
      ready.actorName).isSome

/--
Decidable, because the cohort is a list and the lookup returns an `Option`.

The instance is needed rather than merely available: instance search does not unfold a plain definition, so
without it a concrete `CohortDeclared` goal cannot be closed by `decide` even though everything under it is
computable. The shape follows `DTR.GeneralModel.actorPrioritiesDistinctDecidable`.
-/
instance instDecidableCohortDeclared
    (model :
      DTR.GeneralModel)
    (config :
      DTR.GeneralConfiguration) :
    Decidable
      (CohortDeclared
        model
        config) := by

  unfold CohortDeclared

  infer_instance

/--
Ready actor `left` takes its step no later than ready actor `right`.

Arrival first, priority second. The module header records why the reverse reading is refuted by
`DTR.GeneralActorState.dueArrival` rather than merely disliked. The second component is
`GeneralPriority.PriorityPrecedesOrEqual`, so the convention for an absent priority is **inherited**
from the relation stage F sorts with, not restated here where it could drift.

Like the relations it is built from, this is a total **preorder** rather than a total order: two ready
actors with the same arrival and the same priority tie, and two unannotated actors at one arrival are
the ordinary way that happens. `selectMinimum` below resolves ties by cohort position — the order
`DTR.readyActorsOf` produces — which is the same stability convention decision `0041` fixed for equal
LF microsteps.
-/
def PrecedesOrEqual
    (model :
      DTR.GeneralModel)
    (left right :
      ReadyActor) :
    Prop :=
  left.logicalTime <
      right.logicalTime ∨
    (left.logicalTime =
        right.logicalTime ∧
      GeneralPriority.PriorityPrecedesOrEqual
        (priorityOf
          model
          left)
        (priorityOf
          model
          right))

/--
Decidable, because both components are: arrival is `Nat`, and the priority component carries
`GeneralPriority.instDecidablePriorityPrecedesOrEqual`.
-/
instance instDecidablePrecedesOrEqual
    (model :
      DTR.GeneralModel)
    (left right :
      ReadyActor) :
    Decidable
      (PrecedesOrEqual
        model
        left
        right) := by

  unfold PrecedesOrEqual

  infer_instance

/--
Reflexivity. The right disjunct, with the priority component's own reflexivity.
-/
theorem precedesOrEqual_refl
    (model :
      DTR.GeneralModel)
    (ready :
      ReadyActor) :
    PrecedesOrEqual
      model
      ready
      ready :=
  Or.inr
    ⟨rfl,
      GeneralPriority.priorityPrecedesOrEqual_refl
        (priorityOf
          model
          ready)⟩

/--
Transitivity.

The arithmetic legs go through `omega` rather than a rewrite, so the proof does not depend on the
direction a `▸` happens to fire in; the priority leg is the component lemma.
-/
theorem precedesOrEqual_trans
    {model :
      DTR.GeneralModel}
    {left middle right :
      ReadyActor}
    (hLeft :
      PrecedesOrEqual
        model
        left
        middle)
    (hRight :
      PrecedesOrEqual
        model
        middle
        right) :
    PrecedesOrEqual
      model
      left
      right := by

  unfold PrecedesOrEqual at hLeft hRight ⊢

  rcases hLeft with
    hTimeLeft |
    ⟨hTimeEqLeft, hPriorityLeft⟩

  · rcases hRight with
      hTimeRight |
      ⟨hTimeEqRight, _⟩

    · exact
        Or.inl
          (by omega)

    · exact
        Or.inl
          (by omega)

  · rcases hRight with
      hTimeRight |
      ⟨hTimeEqRight, hPriorityRight⟩

    · exact
        Or.inl
          (by omega)

    · exact
        Or.inr
          ⟨hTimeEqLeft.trans
            hTimeEqRight,
            GeneralPriority.priorityPrecedesOrEqual_trans
              hPriorityLeft
              hPriorityRight⟩

/--
Totality, which is what makes `selectMinimum` below a genuine minimum rather than a first-fit.

The split is on arrival equality rather than on a trichotomy lemma, so the proof rests only on
`Nat.lt_or_ge` and `omega`.
-/
theorem precedesOrEqual_total
    (model :
      DTR.GeneralModel)
    (left right :
      ReadyActor) :
    PrecedesOrEqual
      model
      left
      right ∨
    PrecedesOrEqual
      model
      right
      left := by

  unfold PrecedesOrEqual

  by_cases hTime :
      left.logicalTime =
        right.logicalTime

  · rcases
        GeneralPriority.priorityPrecedesOrEqual_total
          (priorityOf
            model
            left)
          (priorityOf
            model
            right) with
      hPriority |
      hPriority

    · exact
        Or.inl
          (Or.inr
            ⟨hTime,
              hPriority⟩)

    · exact
        Or.inr
          (Or.inr
            ⟨hTime.symm,
              hPriority⟩)

  · rcases
        Nat.lt_or_ge
          left.logicalTime
          right.logicalTime with
      hLess |
      hGreaterEqual

    · exact
        Or.inl
          (Or.inl
            hLess)

    · exact
        Or.inr
          (Or.inl
            (by omega))

/--
The minimum of a non-empty cohort, carried as a running best.

Ties go to the element already held, and the cohort is walked left to right, so a tie is resolved by
**cohort position** — the order `DTR.readyActorsOf` produces from the actor store. That is the same
first-wins stability `DTR.GeneralPriority.normalize` uses, so a tie is resolved rather than left to an
arbitrary choice, and the resolution is the one the rest of the project already commits to.

Written as explicit recursion with the model fixed before the match, rather than through a `List.foldl`
with a comparator, because every theorem below is proved by induction on this exact recursion.
-/
def selectMinimum
    (model :
      DTR.GeneralModel) :
    ReadyActor →
    List ReadyActor →
    ReadyActor

  | best, [] =>
      best

  | best, candidate :: remaining =>
      if
          PrecedesOrEqual
            model
            best
            candidate then
        selectMinimum
          model
          best
          remaining
      else
        selectMinimum
          model
          candidate
          remaining

/--
The actor that takes the next step, or `none` when nothing is ready.

The cohort is **derived here** from the configuration rather than accepted as a parameter. That is the
one deliberate departure from the multi-store precedent, and the module header records why: a cohort
parameter lets a caller pass a list the configuration does not justify.

`none` is the terminated case, not an error: a configuration with no due message has no next step, and
stage G's finite executions end there.
-/
def selectedActor
    (model :
      DTR.GeneralModel)
    (config :
      DTR.GeneralConfiguration) :
    Option ReadyActor :=
  match
      config.readyActors with

  | [] =>
      none

  | first :: remaining =>
      some
        (selectMinimum
          model
          first
          remaining)

/--
The running minimum is one of the elements it was chosen from.

This is what rules out a selection function that invents an actor. It is proved before minimality
because minimality on its own would be satisfied by a fabricated element that precedes everything.
-/
theorem selectMinimum_mem
    (model :
      DTR.GeneralModel)
    (best :
      ReadyActor)
    (candidates :
      List ReadyActor) :
    selectMinimum
        model
        best
        candidates ∈
      best :: candidates := by

  induction candidates generalizing best with

  | nil =>
      simp [selectMinimum]

  | cons candidate remaining inductionHypothesis =>
      simp only [selectMinimum]

      by_cases hPrecedes :
          PrecedesOrEqual
            model
            best
            candidate

      · rw [if_pos hPrecedes]

        rcases List.mem_cons.mp
            (inductionHypothesis
              best) with
          hEq |
          hMem

        · rw [hEq]
          simp

        · exact
            List.mem_cons_of_mem
              _
              (List.mem_cons_of_mem
                _
                hMem)

      · rw [if_neg hPrecedes]

        rcases List.mem_cons.mp
            (inductionHypothesis
              candidate) with
          hEq |
          hMem

        · rw [hEq]
          simp

        · exact
            List.mem_cons_of_mem
              _
              (List.mem_cons_of_mem
                _
                hMem)

/--
The running minimum precedes every element it was chosen from.

This is the module's substantive proof. The induction is on the cohort tail, generalizing the running
best, and the two interesting branches are the ones that must reach *outside* the induction hypothesis:

* when the held best wins, the discarded candidate is not in the induction hypothesis's list, so the
  bound comes from **transitivity** through the held best;
* when the candidate wins, the discarded best is not in it either, and the bound comes from
  **totality** — the negated test is what supplies the reverse comparison.

Neither branch would close for a mere first-fit, which is why the order facts above are stated.
-/
theorem selectMinimum_precedes
    (model :
      DTR.GeneralModel)
    (best :
      ReadyActor)
    (candidates :
      List ReadyActor) :
    ∀ other ∈ best :: candidates,
      PrecedesOrEqual
        model
        (selectMinimum
          model
          best
          candidates)
        other := by

  induction candidates generalizing best with

  | nil =>
      intro other hMember

      have hEq :
          other = best := by
        simpa using hMember

      rw [hEq]

      simp only [selectMinimum]

      exact
        precedesOrEqual_refl
          model
          best

  | cons candidate remaining inductionHypothesis =>
      intro other hMember

      simp only [selectMinimum]

      by_cases hPrecedes :
          PrecedesOrEqual
            model
            best
            candidate

      · rw [if_pos hPrecedes]

        have hBest :
            PrecedesOrEqual
              model
              (selectMinimum
                model
                best
                remaining)
              best :=
          inductionHypothesis
            best
            best
            (by simp)

        rcases List.mem_cons.mp hMember with
          hEqBest |
          hRest

        · rw [hEqBest]
          exact hBest

        · rcases List.mem_cons.mp hRest with
            hEqCandidate |
            hMem

          · rw [hEqCandidate]
            exact
              precedesOrEqual_trans
                hBest
                hPrecedes

          · exact
              inductionHypothesis
                best
                other
                (List.mem_cons_of_mem
                  _
                  hMem)

      · rw [if_neg hPrecedes]

        have hCandidate :
            PrecedesOrEqual
              model
              (selectMinimum
                model
                candidate
                remaining)
              candidate :=
          inductionHypothesis
            candidate
            candidate
            (by simp)

        have hCandidateBest :
            PrecedesOrEqual
              model
              candidate
              best := by
          rcases
              precedesOrEqual_total
                model
                best
                candidate with
            hForward |
            hBackward

          · exact
              absurd
                hForward
                hPrecedes

          · exact hBackward

        rcases List.mem_cons.mp hMember with
          hEqBest |
          hRest

        · rw [hEqBest]
          exact
            precedesOrEqual_trans
              hCandidate
              hCandidateBest

        · rcases List.mem_cons.mp hRest with
            hEqCandidate |
            hMem

          · rw [hEqCandidate]
            exact hCandidate

          · exact
              inductionHypothesis
                candidate
                other
                (List.mem_cons_of_mem
                  _
                  hMem)

/--
What the instance lookup returns is one of the instances searched.

`DTR.findActor?` had no lemmas at all before this module — only the definition and the private
`lookup_topologyOf` that consumes it — so the two facts below are stated here. Both follow that
lemma's shape: induction on the list, `by_cases` on the head's name, `simp` with the definition.
-/
private theorem findActor?_mem
    (instances :
      List DTR.GeneralActorInstance)
    (actorName :
      ActorName) :
    ∀ actor,
      DTR.findActor?
          instances
          actorName =
        some actor →
      actor ∈ instances := by

  induction instances with

  | nil =>
      intro actor hFound
      simp [DTR.findActor?] at hFound

  | cons head remaining inductionHypothesis =>
      intro actor hFound

      by_cases hHead :
          head.name = actorName

      · simp [
          DTR.findActor?,
          hHead
        ] at hFound

        subst hFound
        simp

      · simp [
          DTR.findActor?,
          hHead
        ] at hFound

        exact
          List.mem_cons_of_mem
            _
            (inductionHypothesis
              actor
              hFound)

/--
The instance the lookup returns is the one whose name was searched for.

This is what turns an equality of *instances* into an equality of ready-actor names in
`selectedActor_unique`, and without it that theorem would prove only that the two selections agree on
their priorities.
-/
private theorem findActor?_name
    (instances :
      List DTR.GeneralActorInstance)
    (actorName :
      ActorName) :
    ∀ actor,
      DTR.findActor?
          instances
          actorName =
        some actor →
      actor.name = actorName := by

  induction instances with

  | nil =>
      intro actor hFound
      simp [DTR.findActor?] at hFound

  | cons head remaining inductionHypothesis =>
      intro actor hFound

      by_cases hHead :
          head.name = actorName

      · simp [
          DTR.findActor?,
          hHead
        ] at hFound

        subst hFound
        exact hHead

      · simp [
          DTR.findActor?,
          hHead
        ] at hFound

        exact
          inductionHypothesis
            actor
            hFound

/--
Distinct declared priorities make the priority projection injective on the instance list.

This is the step that upgrades the total preorder to a strict total order, and it is the reason
`selectedActor_unique` needs a guard at all. The hypothesis is the raw `List.Nodup` that
`DTR.GeneralModel.actorPriorities` produces, for the reason
`GeneralPriority.priorities_nodup_normalize` gives for stating its own guard raw.

Note what the hypothesis forbids: `Nodup` on a list of `Option Nat` rules out **two absent
priorities** as well as two equal explicit ones. A model with two unannotated actors does not satisfy
it, which is exactly why this cannot be a well-formedness clause — the same conclusion
`docs/STAGE_F_DESIGN.md` §6 reached for message servers.
-/
private theorem instance_eq_of_priority_eq
    (instances :
      List DTR.GeneralActorInstance) :
    (instances.map
        (fun actor =>
          actor.priority)).Nodup →
    ∀ left ∈ instances,
      ∀ right ∈ instances,
        left.priority =
            right.priority →
          left = right := by

  induction instances with

  | nil =>
      intro _ left hLeft
      simp at hLeft

  | cons head remaining inductionHypothesis =>
      intro hNodup left hLeft right hRight hPriority

      simp only [
        List.map_cons,
        List.nodup_cons
      ] at hNodup

      obtain ⟨hHead, hRemaining⟩ :=
        hNodup

      rcases List.mem_cons.mp hLeft with
        hLeftEq |
        hLeftMem

      · rcases List.mem_cons.mp hRight with
          hRightEq |
          hRightMem

        · rw [hLeftEq, hRightEq]

        · exfalso
          apply hHead

          refine
            List.mem_map.mpr
              ⟨right,
                hRightMem,
                ?_⟩

          show
            right.priority =
              head.priority

          rw [← hPriority, hLeftEq]

      · rcases List.mem_cons.mp hRight with
          hRightEq |
          hRightMem

        · exfalso
          apply hHead

          refine
            List.mem_map.mpr
              ⟨left,
                hLeftMem,
                ?_⟩

          show
            left.priority =
              head.priority

          rw [hPriority, hRightEq]

        · exact
            inductionHypothesis
              hRemaining
              left
              hLeftMem
              right
              hRightMem
              hPriority

/--
Two ready actors that agree on both fields are equal.

`ReadyActor` has no `ext` lemma, so this is stated once here rather than repeated inside a proof where
other hypotheses mention the actors being taken apart.
-/
private theorem readyActor_eq
    {left right :
      ReadyActor}
    (hName :
      left.actorName =
        right.actorName)
    (hTime :
      left.logicalTime =
        right.logicalTime) :
    left = right := by

  cases left
  cases right

  simp only [
    ReadyActor.mk.injEq
  ]

  exact ⟨hName, hTime⟩

/--
The selection at a cohort known to be empty.

Stated so that every theorem below can case on the cohort and rewrite, instead of reasoning through
the `match` in `selectedActor`'s body.
-/
theorem selectedActor_eq_none_of_cohort_nil
    (model :
      DTR.GeneralModel)
    (config :
      DTR.GeneralConfiguration)
    (hCohort :
      config.readyActors = []) :
    selectedActor
        model
        config =
      none := by

  unfold selectedActor
  rw [hCohort]

/--
The selection at a cohort known to be non-empty.
-/
theorem selectedActor_eq_of_cohort_cons
    (model :
      DTR.GeneralModel)
    (config :
      DTR.GeneralConfiguration)
    (first :
      ReadyActor)
    (remaining :
      List ReadyActor)
    (hCohort :
      config.readyActors =
        first :: remaining) :
    selectedActor
        model
        config =
      some
        (selectMinimum
          model
          first
          remaining) := by

  unfold selectedActor
  rw [hCohort]

/--
A step is selected exactly when something is ready.

The right-to-left direction is the one that matters for stage G: it says selection never gets stuck
while work remains, which is what stops the LTS from having a spurious terminal state.
-/
theorem selectedActor_isSome_iff
    (model :
      DTR.GeneralModel)
    (config :
      DTR.GeneralConfiguration) :
    (selectedActor
        model
        config).isSome ↔
      config.readyActors ≠ [] := by

  cases hCohort :
      config.readyActors with

  | nil =>
      rw [
        selectedActor_eq_none_of_cohort_nil
          model
          config
          hCohort
      ]
      simp

  | cons first remaining =>
      rw [
        selectedActor_eq_of_cohort_cons
          model
          config
          first
          remaining
          hCohort
      ]
      simp

/--
The selected actor is a member of the cohort.

Nothing is invented. `selectedActor_minimal` on its own would be satisfied by a fabricated actor that
precedes everything, so this is the theorem that gives that one its content.
-/
theorem selectedActor_mem
    {model :
      DTR.GeneralModel}
    {config :
      DTR.GeneralConfiguration}
    {ready :
      ReadyActor}
    (hSelected :
      selectedActor
          model
          config =
        some ready) :
    ready ∈ config.readyActors := by

  cases hCohort :
      config.readyActors with

  | nil =>
      rw [
        selectedActor_eq_none_of_cohort_nil
          model
          config
          hCohort
      ] at hSelected
      simp at hSelected

  | cons first remaining =>
      rw [
        selectedActor_eq_of_cohort_cons
          model
          config
          first
          remaining
          hCohort
      ] at hSelected

      injection hSelected with hEq

      rw [← hEq]

      exact
        selectMinimum_mem
          model
          first
          remaining

/--
The selected actor precedes every ready actor.

This is stage G's scheduling obligation in its weakest honest form: it fixes *an* order, and it does
not claim that order is the only admissible one. The uniqueness theorem below is what adds that, and
only under a guard.
-/
theorem selectedActor_minimal
    {model :
      DTR.GeneralModel}
    {config :
      DTR.GeneralConfiguration}
    {ready :
      ReadyActor}
    (hSelected :
      selectedActor
          model
          config =
        some ready) :
    ∀ other ∈ config.readyActors,
      PrecedesOrEqual
        model
        ready
        other := by

  cases hCohort :
      config.readyActors with

  | nil =>
      rw [
        selectedActor_eq_none_of_cohort_nil
          model
          config
          hCohort
      ] at hSelected
      simp at hSelected

  | cons first remaining =>
      rw [
        selectedActor_eq_of_cohort_cons
          model
          config
          first
          remaining
          hCohort
      ] at hSelected

      injection hSelected with hEq

      intro other hMember

      rw [← hEq]

      exact
        selectMinimum_precedes
          model
          first
          remaining
          other
          hMember

/--
The selected actor is a real actor of the configuration, with the arrival its own bag determines.

This is the anti-fabrication statement in the form the state layer already proves, obtained by handing
`selectedActor_mem` to `DTR.readyActors_sound`. It is strictly stronger than "the name exists": it also
pins the selected `logicalTime` to the actor's own earliest due arrival, so a selection cannot invent a
time either.
-/
theorem selectedActor_ne_fabricated
    {model :
      DTR.GeneralModel}
    {config :
      DTR.GeneralConfiguration}
    {ready :
      ReadyActor}
    (hSelected :
      selectedActor
          model
          config =
        some ready) :
    ∃ state,
      (ready.actorName, state) ∈
          config.actors ∧
        state.dueArrival
            config.now =
          some ready.logicalTime :=
  DTR.readyActors_sound
    config
    ready
    (selectedActor_mem
      hSelected)

/--
Under distinct declared priorities, the selected actor is the *only* minimum.

Guard-relative, and deliberately so. Without the guard the order is a total preorder with real ties —
two unannotated actors at one arrival tie — and `selectMinimum` resolves such a tie by cohort position,
which is a choice rather than a consequence. `model.actorPriorities.Nodup` is what removes the ties;
`CohortDeclared` is what lets an equality of priorities be turned back into an equality of names,
since an undeclared actor would otherwise be indistinguishable from an unannotated one.

For stage G this is the determinism result: with the guard, the source schedule is forced, so a target
execution has exactly one source execution to correspond to.
-/
theorem selectedActor_unique
    {model :
      DTR.GeneralModel}
    {config :
      DTR.GeneralConfiguration}
    {ready other :
      ReadyActor}
    (hNodup :
      model.actorPriorities.Nodup)
    (hDeclared :
      CohortDeclared
        model
        config)
    (hSelected :
      selectedActor
          model
          config =
        some ready)
    (hMember :
      other ∈ config.readyActors)
    (hPrecedes :
      PrecedesOrEqual
        model
        other
        ready) :
    other = ready := by

  have hMinimal :
      PrecedesOrEqual
        model
        ready
        other :=
    selectedActor_minimal
      hSelected
      other
      hMember

  unfold PrecedesOrEqual at hPrecedes hMinimal

  have hTime :
      other.logicalTime =
        ready.logicalTime := by
    rcases hPrecedes with
      hForward |
      ⟨hForward, _⟩

    · rcases hMinimal with
        hBackward |
        ⟨hBackward, _⟩

      · exfalso
        omega

      · exfalso
        omega

    · exact hForward

  have hPriorityForward :
      GeneralPriority.PriorityPrecedesOrEqual
        (priorityOf
          model
          other)
        (priorityOf
          model
          ready) := by
    rcases hPrecedes with
      hForward |
      ⟨_, hForward⟩

    · exfalso
      omega

    · exact hForward

  have hPriorityBackward :
      GeneralPriority.PriorityPrecedesOrEqual
        (priorityOf
          model
          ready)
        (priorityOf
          model
          other) := by
    rcases hMinimal with
      hBackward |
      ⟨_, hBackward⟩

    · exfalso
      omega

    · exact hBackward

  have hPriorityEq :
      priorityOf
          model
          other =
        priorityOf
          model
          ready :=
    GeneralPriority.priorityPrecedesOrEqual_antisymm
      hPriorityForward
      hPriorityBackward

  have hReadyMember :
      ready ∈ config.readyActors :=
    selectedActor_mem
      hSelected

  have hOtherSome :=
    hDeclared
      other
      hMember

  have hReadySome :=
    hDeclared
      ready
      hReadyMember

  cases hOtherFound :
      model.actor?
        other.actorName with

  | none =>
      rw [hOtherFound] at hOtherSome
      simp at hOtherSome

  | some actorOther =>
      cases hReadyFound :
          model.actor?
            ready.actorName with

      | none =>
          rw [hReadyFound] at hReadySome
          simp at hReadySome

      | some actorReady =>
          have hPriorityOther :
              priorityOf
                  model
                  other =
                actorOther.priority := by
            unfold priorityOf
            rw [hOtherFound]

          have hPriorityReady :
              priorityOf
                  model
                  ready =
                actorReady.priority := by
            unfold priorityOf
            rw [hReadyFound]

          have hInstanceEq :
              actorOther = actorReady :=
            instance_eq_of_priority_eq
              model.instances
              hNodup
              actorOther
              (findActor?_mem
                model.instances
                other.actorName
                actorOther
                hOtherFound)
              actorReady
              (findActor?_mem
                model.instances
                ready.actorName
                actorReady
                hReadyFound)
              (by
                rw [
                  ← hPriorityOther,
                  ← hPriorityReady
                ]
                exact hPriorityEq)

          have hNameOther :
              actorOther.name =
                other.actorName :=
            findActor?_name
              model.instances
              other.actorName
              actorOther
              hOtherFound

          have hNameReady :
              actorReady.name =
                ready.actorName :=
            findActor?_name
              model.instances
              ready.actorName
              actorReady
              hReadyFound

          have hName :
              other.actorName =
                ready.actorName := by
            rw [
              ← hNameOther,
              ← hNameReady,
              hInstanceEq
            ]

          exact
            readyActor_eq
              hName
              hTime

end GeneralActorSelection

end DTR

end Relico
