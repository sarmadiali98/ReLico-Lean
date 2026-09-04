import Relico.Common.Store
import Relico.LF.GeneralSyntax
import Relico.LF.Scheduling

set_option autoImplicit false

namespace Relico
namespace LF

/-!
# Target runtime state and observable labels for the general family

Obligation G2a-ii, target side. Like its source counterpart in `Relico/DTR/GeneralRuntime.lean`, this
module holds the runtime **state** a target program needs in order to execute one statement at a time
and the **label** an observable step carries, and it holds no step rules — those are G2a-iii, in
`Relico/LF/GeneralSemantics.lean`. The split follows
`Relico/DTR/DetailedMultiStorePayloadRuntime.lean` and its `…Semantics.lean` companion, which divide
state-and-labels from the step inductive exactly here.

## The tag, `upd`, and the tag order are all reused, not rebuilt

`docs/STAGE_G_DESIGN.md` §13 **listed** "the superdense tag and `upd`" as work this obligation introduces —
§7's module table said the same. That was wrong, and wrong by more than it looks. Both sections now say
"reused, not built"; the correction is recorded as **F69**. Four things the design treated as new already
exist, proved, from vertical slice v0:

* `Relico/LF/State.lean` declares `structure Tag` with `time : LogicalTime` and `microstep : Nat`.
* `Tag.schedule` **is** P24's `upd`: a zero delay keeps the time and advances the microstep, a positive
  delay advances the time and resets the microstep to zero. It carries `@[simp] schedule_zero`,
  `schedule_positive`, and `@[simp] schedule_time`.
* `Relico/LF/Scheduling.lean` declares `Tag.PrecedesOrEqual`, the lexicographic tag order — time first,
  microstep second — with `precedesOrEqual_refl`, `precedesOrEqual_same_time`,
  `eq_of_time_eq_of_microstep`, `not_precedesOrEqual_same_time_of_microstep_lt` and
  `time_le_of_precedesOrEqual`. Thirty-three modules besides this one already use it, and G1's own docstring in
  `Relico/DTR/GeneralActorSelection.lean` names it as the shape `DTR.GeneralActorSelection` mirrors.
* `Relico/LF/PendingNotPast.lean` declares `Tag.precedesOrEqual_schedule`: scheduling never produces an
  earlier tag. That is the monotonicity fact G2a-iii's time-progress rule rests on, so G2a-iii should
  import that module rather than restate it. It is deliberately **not** imported here, because its own
  import closure reaches `Relico.LF.MultiStoreSemantics` and this module needs none of that.

So this module reuses all four. Redeclaring any of them would be the defect this project keeps finding:
two definitions of one convention, free to drift, with nothing type-checked holding them together.

## What is genuinely missing is narrower, and it is scheduler-shaped

`Tag.PrecedesOrEqual` has no `Decidable` instance, no transitivity, and no totality. Verified absent under
any name, not merely absent from `Relico/LF/Scheduling.lean`.

The reason they are missing is worth stating, because it says which obligation owes them. Every existing
consumer proves **one specific inequality** — this pending action is not before the current tag, that
microstep cannot precede this one. None of them **computes a minimum**. A scheduler does, and a scheduler
needs all three: decidability to compute, totality to know a minimum exists, transitivity to know the
computed one really is least. G1 needed exactly the same three of its source-side counterpart and
declared them there; this is the target-side other half.

They are added below by **reopening `namespace Tag`**, which is this repository's convention rather than a
liberty: besides this file, `namespace Tag` is opened in four others — `Relico/LF/State.lean`,
`Relico/LF/Scheduling.lean`, `Relico/LF/PendingNotPast.lean` and `Relico/LF/PriorityTimingInvariant.lean` —
and the last two exist precisely to add tag lemmas from outside the declaring module. Adding them here keeps
one name for one convention and leaves every existing call site untouched.

## The label type is `GeneralLabel`

Not `GeneralLfAction`, which `docs/STAGE_G_DESIGN.md` §7 specified first and no longer does. The full
argument, with its three measurements, is recorded once in
`Relico/DTR/GeneralRuntime.lean` and deliberately not repeated here. The short form: `Label` is the
house word, and `LF.GeneralLabel` removes a collision with the syntactic `LF.GeneralAction` that
`LF.GeneralLfAction` would have kept. This is still **two** label types, one per language, so G2b's
`ϕ : Act_1 → Act_2` remains a function between distinct types.

## Why an event kind cannot be `startup`

`LF.GeneralTrigger` has three constructors — `startup`, `logicalAction` and `inputPort`. Only the last
two can ever be *scheduled*: startup fires once, at the beginning, and nothing enqueues it.
`GeneralEventKind` therefore has two constructors rather than reusing `GeneralTrigger`, which makes an
unschedulable pending event unrepresentable instead of leaving a case for a rule to handle wrongly.

The cost is a conversion at the trigger-matching site in G2a-iii, which is the right place for it: that
is where a fired event has to be matched against a reaction's trigger list, and a trigger list is a
disjunction.

## Why one event queue rather than one per reactor

A single `GeneralEventQueue` ordered by tag is what the target actually has — LF's event queue is
global, and the tag, not the reactor, decides what happens next. Splitting it per reactor would make
"the earliest event overall" a computation over many queues and would let two reactors disagree about
the current tag.

## What is deliberately absent

The **selection** of the earliest pending event. Its source-side counterpart is G1's `selectMinimum`,
which lives in `Relico/DTR/GeneralActorSelection.lean` — a scheduler module, not a runtime module. The
target-side analogue belongs with G2a-iii's rules for the same reason, and adding a fourth module to
this obligation would silently move the job count the work plan predicts.
-/

namespace Tag

/--
The tag order is decidable.

Both components are `Nat`, so this needs no content beyond unfolding the definition and letting instance
resolution assemble the disjunction. Stated because G2a-iii's scheduler has to *compute* the earliest
pending tag, and the existing consumers of `PrecedesOrEqual` only ever prove a specific
inequality.
-/
instance instDecidablePrecedesOrEqual
    (left right :
      LF.Tag) :
    Decidable
      (PrecedesOrEqual
        left
        right) := by

  unfold PrecedesOrEqual

  infer_instance

/--
The tag order is transitive.

Four branches over the two hypotheses, three landing in the strict-time disjunct and one preserving the
tie. Every time comparison closes with an explicit `Nat` transitivity lemma rather than with `omega`, and
that is forced rather than stylistic: `Tag.time` has type `LogicalTime`, `omega` does not see through that
abbreviation, and a `LogicalTime`-typed hypothesis is therefore invisible to it. `Tag.microstep` is a bare
`Nat` and *is* visible, so the two fields of one structure behave differently inside one proof. G1's
source-side counterpart uses `omega` freely because `ReadyActor.logicalTime` is declared `Nat`, not
`LogicalTime` — its proof shape does not transfer here unchanged. Recorded as **F72**.

Needed so that "the computed minimum is least" is a fact about the order rather than about the particular
list a scheduler walked.
-/
theorem precedesOrEqual_trans
    {left middle right :
      LF.Tag}
    (hLeft :
      PrecedesOrEqual
        left
        middle)
    (hRight :
      PrecedesOrEqual
        middle
        right) :
    PrecedesOrEqual
      left
      right := by

  unfold PrecedesOrEqual at hLeft hRight ⊢

  rcases hLeft with
    hTimeLeft |
    ⟨hTimeEqLeft, hStepLeft⟩

  · rcases hRight with
      hTimeRight |
      ⟨hTimeEqRight, _⟩

    · exact Or.inl
        (Nat.lt_trans hTimeLeft hTimeRight)

    · exact Or.inl
        (Nat.lt_of_lt_of_le hTimeLeft
          (Nat.le_of_eq hTimeEqRight))

  · rcases hRight with
      hTimeRight |
      ⟨hTimeEqRight, hStepRight⟩

    · exact Or.inl
        (Nat.lt_of_le_of_lt
          (Nat.le_of_eq hTimeEqLeft)
          hTimeRight)

    · exact Or.inr
        ⟨hTimeEqLeft.trans hTimeEqRight,
          Nat.le_trans hStepLeft hStepRight⟩

/--
The tag order is total: any two tags are comparable in one direction or the other.

Needed because a scheduler that picks a minimum has to know one exists. Note that this is totality of a
**preorder**, not antisymmetry: two events at the same tag tie, and that is the ordinary case rather than
a corner one, because every zero-delay send produces events sharing a time. Ties are resolved downstream
by queue position, which is the stability convention decision `0041` fixed for exactly this situation.

The split avoids ever asking `omega` about a time comparison, for F72's reason: two `Nat.lt_or_ge` cases
establish the strict orders, `Nat.le_antisymm` recovers the tie from the two non-strict leftovers, and
`omega` is used only on the `microstep` goal, where the field is a bare `Nat` and so visible to it. G1's
`by_cases` on time equality is deliberately *not* copied — it produces a `LogicalTime`-typed hypothesis
that `omega` silently ignores.
-/
theorem precedesOrEqual_total
    (left right :
      LF.Tag) :
    PrecedesOrEqual
        left
        right ∨
      PrecedesOrEqual
        right
        left := by

  unfold PrecedesOrEqual

  rcases Nat.lt_or_ge left.time right.time with
    hTimeLess |
    hTimeAtLeast

  · exact Or.inl (Or.inl hTimeLess)

  · rcases Nat.lt_or_ge right.time left.time with
      hTimeGreater |
      hTimeAtMost

    · exact Or.inr (Or.inl hTimeGreater)

    · have hTimeEq :
          left.time = right.time :=
        Nat.le_antisymm hTimeAtMost hTimeAtLeast

      by_cases hStep :
          left.microstep ≤ right.microstep

      · exact Or.inl
          (Or.inr ⟨hTimeEq, hStep⟩)

      · refine Or.inr
          (Or.inr ⟨hTimeEq.symm, ?_⟩)
        omega

end Tag

/--
The kind of a schedulable target event.

Two constructors, not three: `LF.GeneralTrigger.startup` is a trigger but never a *pending* event, so it
is excluded here rather than left as a case a rule could mishandle.
-/
inductive GeneralEventKind where

  | logicalAction
      (name :
        ActionName) :
      GeneralEventKind

  | inputPort
      (name :
        PortName) :
      GeneralEventKind

deriving Repr, DecidableEq, BEq, Inhabited

/--
One pending target event: what will happen, to which reactor, carrying what, and when.

`target` is an `ActorName` because `LF.GeneralReactorInstance.name` is an `ActorName` — the target keeps
the source's actor naming, which is what lets G2b index both sides of the correspondence with one key
type instead of a translation between two.
-/
structure GeneralPendingEvent where
  target :
    ActorName

  kind :
    GeneralEventKind

  tag :
    Tag

  payload :
    List LF.GeneralValue := []

deriving Repr, DecidableEq, BEq, Inhabited

/--
The global event queue, in insertion order.

Order is retained rather than sorted, because insertion order is the tie-break for events sharing a tag
and a sort would discard it.
-/
abbrev GeneralEventQueue :=
  List LF.GeneralPendingEvent

/--
One reactor's runtime state: its state-variable valuation, plus the statements it has left to run.

The mirror of `DTR.GeneralActorRuntime`, and for the same reason: the continuation is added beside the
existing content rather than as a new field on a type built code already elaborates against.

**`frames` mirrors `DTR.GeneralActorRuntime.frames`, and the mirroring is forced rather than tidy.**
Stage H's source runtime gained a stack of enclosing continuations so that stepping into a branch can
remember what follows it. Adding it on one side only breaks the correspondence in a way that is easy to
miss and was caught by the compiler: `Correctness.generalActorIdle_of_reactorIdle` transfers idleness
*from* the target *to* the source, and a source `idle` that also asks for an empty stack cannot be
concluded from a target that has no stack to ask about. Either both runtimes carry the stack or the
transfer stops being provable, so both carry it.

Not defaultable, for the reason given on the source field: every step rule rewrites a reactor as a full
record literal, and a default would let a rule silently discard the stack with no test failing.
-/
structure GeneralReactorRuntime where
  valuation :
    Store VarName LF.GeneralValue

  activeBody :
    LF.GeneralBody := []

  frames :
    List LF.GeneralBody

deriving Repr, DecidableEq, BEq, Inhabited

/--
A global target runtime state: the current tag, one runtime state per reactor, and the pending queue.

The field that differs from `DTR.GeneralConfiguration` is the first one. The source carries a
`LogicalTime`; the target carries a `Tag`, which is a logical time **and** a microstep. That extra
component is the whole content of P24: a zero-delay send advances it, the source has nothing that
corresponds, and a correctness statement that reads the tag as if it were a time is false.
-/
structure GeneralRuntimeState where
  currentTag :
    Tag

  reactors :
    Store ActorName LF.GeneralReactorRuntime

  pending :
    LF.GeneralEventQueue := []

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralReactorRuntime

/--
Whether this reactor has no statements left to run, at any level.

The mirror of `DTR.GeneralActorRuntime.idle`, conjunct for conjunct, and the symmetry is what lets
idleness transfer in both directions across the correspondence. A reactor whose active body has run out
but whose frame stack still holds an enclosing continuation owes the statements after the branch it
stepped into, so it is not finished.

For every program compiled from the currently accepted fragment `frames` is `[]`, so the second conjunct
is `true` wherever the pre-stage-H development goes.
-/
def idle
    (reactor : GeneralReactorRuntime) :
    Bool :=
  reactor.activeBody.isEmpty &&
    reactor.frames.isEmpty

@[simp]
theorem idle_of_nil
    (valuation :
      Store VarName LF.GeneralValue) :
    idle
        {
          valuation := valuation
          activeBody := []
          frames := []
        } =
      true := by
  rfl

@[simp]
theorem idle_of_cons
    (valuation :
      Store VarName LF.GeneralValue)
    (statement :
      LF.GeneralStmt)
    (remaining :
      LF.GeneralBody)
    (frames :
      List LF.GeneralBody) :
    idle
        {
          valuation := valuation
          activeBody :=
            statement :: remaining
          frames := frames
        } =
      false := by
  rfl

/--
A reactor with a pending frame is not idle, whatever its active body.

The mirror of `DTR.GeneralActorRuntime.idle_of_frames_cons`, and needed for the same reason: the two
ways a reactor is busy are independent, and a proof that knew only the first would treat a reactor that
has just finished a branch as ready for a new event.
-/
@[simp]
theorem idle_of_frames_cons
    (valuation :
      Store VarName LF.GeneralValue)
    (activeBody :
      LF.GeneralBody)
    (frame :
      LF.GeneralBody)
    (frames :
      List LF.GeneralBody) :
    idle
        {
          valuation := valuation
          activeBody := activeBody
          frames := frame :: frames
        } =
      false := by
  simp [
    idle
  ]

end GeneralReactorRuntime

namespace GeneralRuntimeState

/--
The observable logical time of a target runtime state.

The tag's time component, with the microstep dropped. This is the projection Lemma 1 relates to
`DTR.GeneralConfiguration.now`, and dropping the microstep here is not a convenience: it is the
statement that the microstep is **not** observable, which is what makes P24's repaired Theorem 1 true
where the paper's is false.
-/
def now
    (state : GeneralRuntimeState) :
    LogicalTime :=
  state.currentTag.time

@[simp]
theorem now_eq
    (state : GeneralRuntimeState) :
    now state =
      state.currentTag.time := by
  rfl

end GeneralRuntimeState

/--
Observable labels of one target step.

The same three shapes as the source's `DTR.GeneralLabel`, which is what makes a label translation
possible at all, but with the τ set P24 measured rather than the one the paper's Table II implies:

* `tau` — a statement step **or** a microstep-only tag advance. Folding the second into τ is P24's
  repair. The paper's TIME PROGRESS is a single observable rule; measured against the target it splits
  in two, and only the branch that increases logical time is observable.
* `timeAdvance` — logical time strictly increasing. The observable half of that split.
* `consume` — an event firing at the current tag, carrying the target reactor and the event kind.

Which rule emits which label is G2a-iii's business.
-/
inductive GeneralLabel where

  | tau :
      GeneralLabel

  | timeAdvance
      (before after :
        LogicalTime) :
      GeneralLabel

  | consume
      (target :
        ActorName)
      (kind :
        LF.GeneralEventKind) :
      GeneralLabel

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralLabel

/--
Whether this label is internal.

`Prop`-valued for the reason recorded on `DTR.GeneralLabel.isTau`: `Common.TauSteps` and
`Common.WeakStep` in `Relico/Common/WeakTransition.lean` both take `isTau : Label → Prop`, and
`Relico/Tests/WeakTransitionFoundation.lean`'s `exampleIsTau` is the built shape.

The target's τ set is the one P24 measured, and this is where that shows: a microstep-only tag advance
must be classified internal here, and G2a-iii's rules must be split so that one exists to classify.
-/
def isTau :
    GeneralLabel →
    Prop

  | tau =>
      True

  | timeAdvance _ _ =>
      False

  | consume _ _ =>
      False

@[simp]
theorem isTau_tau :
    isTau tau :=
  True.intro

@[simp]
theorem not_isTau_timeAdvance
    (before after : LogicalTime) :
    ¬ isTau (timeAdvance before after) := by
  simp [isTau]

@[simp]
theorem not_isTau_consume
    (target : ActorName)
    (kind : LF.GeneralEventKind) :
    ¬ isTau (consume target kind) := by
  simp [isTau]

/--
Project a label onto the observable alphabet.

The target-side counterpart of `DTR.GeneralLabel.project`, and the reason the two are declared with the
same shape rather than one being derived from the other: G2d's trace agreement compares
`Common.observableProjection` applied to a source trace against the same function applied to a target
trace, so the two projections must be independently statable.
-/
def project :
    GeneralLabel →
    Option GeneralLabel

  | tau =>
      none

  | timeAdvance before after =>
      some (timeAdvance before after)

  | consume target kind =>
      some (consume target kind)

@[simp]
theorem project_tau :
    project tau = none := by
  rfl

@[simp]
theorem project_timeAdvance
    (before after : LogicalTime) :
    project (timeAdvance before after) =
      some (timeAdvance before after) := by
  rfl

@[simp]
theorem project_consume
    (target : ActorName)
    (kind : LF.GeneralEventKind) :
    project (consume target kind) =
      some (consume target kind) := by
  rfl

end GeneralLabel

end LF
end Relico
