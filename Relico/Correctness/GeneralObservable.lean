/-
! # The general family's observable alphabet and trace agreement

The shared observation the two general-family label types agree on, and the instantiation of the generic
weak-bisimulation trace agreement at it.

## Why a new type is needed at all

`Correctness.weakBisimulation_traceAgreement_forward` and `..._backward` are generic in both label types
and both τ predicates, and ask only that *projections* agree pairwise. But they need **one** `Observable`
type, and the two families' own `project` functions land in different ones:
`DTR.GeneralLabel.project : DTR.GeneralLabel → Option DTR.GeneralLabel` and
`LF.GeneralLabel.project : LF.GeneralLabel → Option LF.GeneralLabel`. Those two cannot be reconciled by
choosing one of them, because `DTR.GeneralLabel.consume` carries a `DTR.GeneralMessage` while
`LF.GeneralLabel.consume` carries an `LF.GeneralEventKind`, and **F78 forbids a message-to-kind function**.
So the alphabet has to be a third type that both erase into, and defining it is a claim about what the
development treats as observed rather than a mechanical step.

## What is observed, and why exactly this much

* A **consume** observes only the **receiver's identity**. Neither the payload nor the event kind survives.
* A **time advance** observes **both endpoints of the logical-time step**, unchanged.
* An internal step observes nothing.

This is the *smallest* shared observation, and each erasure is forced rather than chosen for convenience:

**The kind cannot be observed.** `Correctness.GeneralConsumeMatch`'s own docstring records that the event
kind is deliberately unconstrained by the correspondence, because relating a `MsgName` to an
`LF.GeneralEventKind` is a property of the *compiled program* — which reaction of which reactor the
translation emitted — and not of the runtime states. An alphabet that observed the kind would demand from
the trace layer exactly the identification F78 refuses.

**The payload cannot be observed either, and this one is more subtle: it is not that it could not be
related, but that relating it would make the alphabet translation-dependent.** `GeneralConsumeMatch` does
pin `event.payload = message.payload.map Translation.compileGeneralValue`, so a payload-carrying alphabet
*could* be made to agree — but only by mentioning `Translation.compileGeneralValue` in the definition of
what is observed. Observation would then depend on the compiler, and a trace statement built on it would be
weaker than it looks: it would hold *because* the translation was applied, not as an independent check on
it. Erasing the payload keeps the alphabet a property of the two semantics alone.

**The receiver survives because the correspondence already pins it.** `GeneralConsumeMatch`'s first
conjunct is `event.target = name`. So receiver identity is not an extra obligation this module introduces —
it is the part of a consume the relation was always going to have to agree about.

**Time survives whole because both label types carry it identically.** Both `timeAdvance` constructors take
`(before after : LogicalTime)`, and `GeneralStateCorrespondence.logicalTime` equates the two clocks, so
nothing has to be erased for the two sides to agree.

## What this module does not do

It does not touch either label type, either `project` function, `GeneralConsumeMatch`,
`GeneralStateCorrespondence`, or any instant-block theorem. It adds no premise to anything already proved.
The trace theorems below take the per-step transfer condition as a **premise**, in the shape the generic
theorem fixes, because that condition still carries the α′ residue for `.consume` — the same residue
`generalConsume_forward_weak_of_fireRepresentative` carries and that this development has not discharged.
Faking it here would claim the frozen question was settled.
-/
import Relico.Correctness.GeneralInstantBlockBackward
import Relico.Correctness.WeakBisimulationTrace

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
One observation of a general-family execution.

Two constructors, because the two label types have two visible shapes between them and the internal one
observes nothing. `consume` keeps the receiver and drops everything else; `timeAdvance` keeps both
endpoints of the step.

Deriving `DecidableEq` and `BEq` because the trace layer compares observation lists, and `Repr` because a
regression pin over a trace is far easier to read than a nested projection expression.

The alphabet mentions **no** payload type, **no** message type, **no** event kind and **no** translation
function. That is the property that makes it an independent check: a trace agreement stated over this type
compares what the two semantics do, not what the compiler arranged.
-/
inductive GeneralObservable where

  | consume
      (receiver :
        ActorName) :
      GeneralObservable

  | timeAdvance
      (before after :
        LogicalTime) :
      GeneralObservable

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralObservable

/--
Observe a source label.

The internal label observes nothing, which is what makes this function agree with
`DTR.GeneralLabel.isTau` (`observe_eq_none_iff_isTau` below). A consume drops its message and keeps the
receiver the label already names.
-/
def ofSourceLabel :
    DTR.GeneralLabel →
    Option GeneralObservable

  | .tau =>
      none

  | .timeAdvance before after =>
      some
        (timeAdvance
          before
          after)

  | .consume receiver _ =>
      some
        (consume receiver)

/--
Observe a target label.

The same three cases as `ofSourceLabel`, and the drop is the event kind rather than the message. `target`
is the reactor the event names, which the compiled program keys by the source actor's own name — so no
renaming is applied here and none is needed.
-/
def ofTargetLabel :
    LF.GeneralLabel →
    Option GeneralObservable

  | .tau =>
      none

  | .timeAdvance before after =>
      some
        (timeAdvance
          before
          after)

  | .consume target _ =>
      some
        (consume target)

@[simp]
theorem ofSourceLabel_tau :
    ofSourceLabel
        DTR.GeneralLabel.tau =
      none := by
  rfl

@[simp]
theorem ofSourceLabel_timeAdvance
    (before after : LogicalTime) :
    ofSourceLabel
        (DTR.GeneralLabel.timeAdvance
          before
          after) =
      some
        (timeAdvance
          before
          after) := by
  rfl

@[simp]
theorem ofSourceLabel_consume
    (receiver : ActorName)
    (message : DTR.GeneralMessage) :
    ofSourceLabel
        (DTR.GeneralLabel.consume
          receiver
          message) =
      some
        (consume receiver) := by
  rfl

@[simp]
theorem ofTargetLabel_tau :
    ofTargetLabel
        LF.GeneralLabel.tau =
      none := by
  rfl

@[simp]
theorem ofTargetLabel_timeAdvance
    (before after : LogicalTime) :
    ofTargetLabel
        (LF.GeneralLabel.timeAdvance
          before
          after) =
      some
        (timeAdvance
          before
          after) := by
  rfl

@[simp]
theorem ofTargetLabel_consume
    (target : ActorName)
    (kind : LF.GeneralEventKind) :
    ofTargetLabel
        (LF.GeneralLabel.consume
          target
          kind) =
      some
        (consume target) := by
  rfl

/--
A source label observes nothing exactly when it is internal.

The soundness condition on an observable alphabet, and the reason it is worth stating rather than assuming:
an alphabet that dropped a *visible* label would make trace agreement vacuously easier, and the generic
trace theorems cannot detect that — they never see `isTau`, only the projections. This theorem is what rules
it out for the source side, and `ofTargetLabel_eq_none_iff_isTau` does the same for the target.

Both directions, because both are used: left-to-right rules out a silently-dropped visible label, and
right-to-left confirms that a τ step contributes nothing to a trace.
-/
theorem ofSourceLabel_eq_none_iff_isTau
    (label : DTR.GeneralLabel) :
    ofSourceLabel label = none ↔
      DTR.GeneralLabel.isTau label := by

  cases label with

  | tau =>
      simp [
        DTR.GeneralLabel.isTau
      ]

  | timeAdvance before after =>
      simp [
        DTR.GeneralLabel.isTau
      ]

  | consume receiver message =>
      simp [
        DTR.GeneralLabel.isTau
      ]

/--
A target label observes nothing exactly when it is internal.

The target's twin of `ofSourceLabel_eq_none_iff_isTau`, and it carries P24's measured τ set: a
microstep-only tag advance is `LF.GeneralLabel.tau` on this side, so it observes nothing — which is the
whole point of the split, since the source takes no step at all there.
-/
theorem ofTargetLabel_eq_none_iff_isTau
    (label : LF.GeneralLabel) :
    ofTargetLabel label = none ↔
      LF.GeneralLabel.isTau label := by

  cases label with

  | tau =>
      simp [
        LF.GeneralLabel.isTau
      ]

  | timeAdvance before after =>
      simp [
        LF.GeneralLabel.isTau
      ]

  | consume target kind =>
      simp [
        LF.GeneralLabel.isTau
      ]

end GeneralObservable

/-!
## The two agreements

Both are instantiations of the generic theorems at `GeneralObservable`, with the general family's step
relations and τ predicates. Neither adds a premise beyond the one the generic theorem asks for, and neither
touches a definition.

**The per-step transfer condition is a premise, and that is not an evasion.** For `.timeAdvance` it is
already proved (`generalTimeAdvance_forward_weak` and `..._backward_weak`); for `.consume` it carries the α′
residue that `generalConsume_forward_weak_of_fireRepresentative` and
`generalConsume_backward_weak_of_takeRepresentative` carry, and that this development has deliberately not
discharged. A caller who can supply representatives discharges the premise by case-splitting the visible
label and applying the two existing cores. Discharging it *here* would mean asserting the frozen question
was settled.

The premise's projection obligation is the interesting part: it demands
`ofSourceLabel label = ofTargetLabel targetLabel`, which after the erasures above means the two sides agree
on the **receiver** of a consume and on **both endpoints** of a time advance. Both are facts the
correspondence already delivers — `GeneralConsumeMatch`'s first conjunct and
`GeneralStateCorrespondence.logicalTime` respectively — so the alphabet asks for nothing new.
-/

/--
**Forward trace agreement for the general family.**

Every source execution is answered by a target execution observing the same sequence, with the two end
states still related. The `related` relation is a parameter rather than fixed to
`GeneralStateCorrespondence`, for the reason the generic theorem's own docstring gives: a caller may hold a
strengthened relation (one carrying store-key uniqueness, say, as both instant-block wrappers do), and
fixing the relation here would force them to weaken it first and then re-establish it.

The two label lists come out the same length — the transfer condition answers each source weak step with
exactly one target weak step — while the *observable* traces may be shorter on both sides, since a pair
projecting to `none` twice contributes nothing. That gap is what makes this trace **agreement** rather than
trace equality, and it is what lets the target's extra microstep traffic (P24) be invisible.
-/
theorem generalTraceAgreement_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (related :
      DTR.GeneralRuntimeConfiguration →
      LF.GeneralRuntimeState →
      Prop)
    (hForward :
      ∀ (config : DTR.GeneralRuntimeConfiguration)
        (state : LF.GeneralRuntimeState)
        (label : DTR.GeneralLabel)
        (config' : DTR.GeneralRuntimeConfiguration),
        related config state →
        Common.WeakStep
          (DTR.GeneralStep model)
          DTR.GeneralLabel.isTau
          config
          label
          config' →
        ∃ (targetLabel : LF.GeneralLabel)
          (state' : LF.GeneralRuntimeState),
          Common.WeakStep
              (LF.GeneralStepModulo program)
              LF.GeneralLabel.isTau
              state
              targetLabel
              state' ∧
            related config' state' ∧
            GeneralObservable.ofSourceLabel label =
              GeneralObservable.ofTargetLabel targetLabel)
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {labels : List DTR.GeneralLabel}
    (hRelated :
      related config state)
    (hSteps :
      Common.WeakSteps
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        labels
        config') :
    ∃ (targetLabels : List LF.GeneralLabel)
      (state' : LF.GeneralRuntimeState),
      Common.WeakSteps
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          targetLabels
          state' ∧
        related config' state' ∧
        Common.observableProjection
            GeneralObservable.ofSourceLabel
            labels =
          Common.observableProjection
            GeneralObservable.ofTargetLabel
            targetLabels :=
  weakBisimulation_traceAgreement_forward
    GeneralObservable.ofSourceLabel
    GeneralObservable.ofTargetLabel
    related
    hForward
    hRelated
    hSteps

/--
**Backward trace agreement for the general family.**

The mirror, and the theorem that makes the pair a bisimulation rather than a simulation. Proved by
`weakBisimulation_traceAgreement_backward`, which is itself the forward theorem at the swapped systems —
so the two are one argument, and neither assumes the other's half.

Note which system sits on the target side here: `LF.GeneralStepModulo`, the light within-tag quotient, not
the raw target step relation. That is decision 0042's placement showing through at the trace level, and it
is the same system both instant-block wrappers answer in.
-/
theorem generalTraceAgreement_backward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (related :
      DTR.GeneralRuntimeConfiguration →
      LF.GeneralRuntimeState →
      Prop)
    (hBackward :
      ∀ (config : DTR.GeneralRuntimeConfiguration)
        (state : LF.GeneralRuntimeState)
        (label : LF.GeneralLabel)
        (state' : LF.GeneralRuntimeState),
        related config state →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          label
          state' →
        ∃ (sourceLabel : DTR.GeneralLabel)
          (config' : DTR.GeneralRuntimeConfiguration),
          Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              config
              sourceLabel
              config' ∧
            related config' state' ∧
            GeneralObservable.ofTargetLabel label =
              GeneralObservable.ofSourceLabel sourceLabel)
    {config : DTR.GeneralRuntimeConfiguration}
    {state state' : LF.GeneralRuntimeState}
    {labels : List LF.GeneralLabel}
    (hRelated :
      related config state)
    (hSteps :
      Common.WeakSteps
        (LF.GeneralStepModulo program)
        LF.GeneralLabel.isTau
        state
        labels
        state') :
    ∃ (sourceLabels : List DTR.GeneralLabel)
      (config' : DTR.GeneralRuntimeConfiguration),
      Common.WeakSteps
          (DTR.GeneralStep model)
          DTR.GeneralLabel.isTau
          config
          sourceLabels
          config' ∧
        related config' state' ∧
        Common.observableProjection
            GeneralObservable.ofTargetLabel
            labels =
          Common.observableProjection
            GeneralObservable.ofSourceLabel
            sourceLabels :=
  weakBisimulation_traceAgreement_backward
    GeneralObservable.ofSourceLabel
    GeneralObservable.ofTargetLabel
    related
    hBackward
    hRelated
    hSteps

end Correctness
end Relico
