/-
! # The general family's label-level weak bisimulation interface

The named object C8 owes, so that the claim *"the General family admits a weak bisimulation structure"* has a
declaration behind it rather than a pair of theorems a reader has to assemble.

## This is NOT the 13-field phase-indexed structure, and the difference is not cosmetic

The four sibling families each carry a `*PhaseWeakBisimulation` with **thirteen** fields — five forward, eight
backward — whose names read `forwardConsumeAfterTimeMatch`, `forwardConsumeReadyMatch`,
`backwardMicrostepSameTimeMatch`, and so on. Those are not forward/backward × *label*. They are
forward/backward × **phase**: their target state is an inductive carrying mid-dispatch phases
(`LF.DetailedMultiStoreState`'s `stable` / `afterTime` / `dispatchReady`, each holding a dispatch proof
*inside the state*), and eight of the thirteen fields exist to cover those phases.

**The general family has no phase state.** `LF.GeneralRuntimeState` is a flat structure — a tag, a reactor
store, a pending queue — and there is no general counterpart of the siblings' `*ForwardPhaseCompatible`.
So the thirteen-field shape is not merely inconvenient here, it is uninstantiable: eight of its fields would
name phases that do not exist. Copying it would require adding phase-indexed state to the general semantics,
which is a change to the semantics and not to a correctness interface.

What this family has instead is a **label** structure. `DTR.GeneralLabel` has three constructors and
`LF.GeneralLabel` has three, so the honest field set is one per label per direction: six.

## What this structure captures

Weak **label** correspondence, over the light within-tag quotient. Each field says: a step at one label on one
side is answered by a weak step at the corresponding label on the other, with the relation re-established.
Internal τ activity is hidden inside the weak transitions, which is what makes this a *weak* correspondence
rather than a refinement, and it is why there is no field per internal step shape.

## Some fields carry explicit residues, and those are genuine semantic obligations

**This structure is not premise-free, and does not claim to be.** Three of its six fields are inhabited by
theorems that themselves carry a residue, and each residue is a measured non-derivability rather than an
unfinished proof:

* **`forwardConsumeMatch`** — the α-representative package of
  `Correctness.generalConsume_forward_weak_of_fireRepresentative`. Which α-equivalent representative the
  target's `fire` premises hold at is the frozen α′ question.
* **`backwardConsumeMatch`** — `hName`, the per-step actor agreement of
  `Correctness.generalConsume_backward_weakStep_of_takeRepresentative`. Not derivable: source actor selection
  is a *function* of the source configuration alone, and `readyActors` / `earliestDueArrival` never mention the
  target program, its queue, or its fire order (F76).
* **`backwardTauMatch`** — `hTauAnswer`. The target's τ set has five constructors against the source's three,
  `microstepAdvance` has no source counterpart at all, and `LF.GeneralStepModulo.weakStep_of_raw` has no sound
  converse. So there is no backward τ closure, by decision, and the answer is a premise.

The other three fields — `forwardTauMatch`, `forwardTimeAdvanceMatch`, `backwardTimeAdvanceMatch` — are
**unconditional**: `generalTauSteps_forward`, `generalTimeAdvance_forward_weak` and
`generalTimeAdvance_backward_weak` inhabit them outright.

So the shape is three unconditional fields and three carrying named obligations. Stating that plainly is the
point: a structure that hid the three would be a stronger-looking claim about a weaker fact.

## Consumed, not merely declared

`GeneralLabelWeakBisimulation.forwardStep` and `.backwardStep` dispatch an arbitrary weak step of either
system onto the appropriate field, mirroring how the three sibling *interfaces* are consumed. That is what
keeps this from being declaration-only surface. Like those three, the structure is a **hypothesis** of its own
consumers rather than something constructed unconditionally — an unconditional witness is impossible while any
field carries a residue, and pretending otherwise is exactly what the residue documentation above exists to
prevent.
-/
import Relico.Correctness.GeneralTraceTransfer

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
The general family's label-level weak bisimulation interface.

Six fields: one per label per direction. **Not** the thirteen-field phase-indexed shape the sibling families
carry — see this module's header for why that shape is uninstantiable here.

Parametrised by the model and the compiled program rather than by a phase index, because the general family's
runtime states are flat. The relation is `Correctness.GeneralTraceRelated`, i.e. the state correspondence
bundled with both store-key invariants, because the τ crossings consume both at every step and a bare
correspondence cannot run them.

**Three of the six fields carry residues.** `forwardConsumeMatch`, `backwardConsumeMatch` and
`backwardTauMatch` are inhabited by theorems that take, respectively, the α-representative package, `hName`,
and `hTauAnswer`. Each is a measured non-derivability, not an unfinished proof, and the module header records
the measurement for each. **This structure is not premise-free.**
-/
structure GeneralLabelWeakBisimulation
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram) :
    Prop where

  /--
  A source internal step is answered by a target internal weak step.

  Unconditional. `Correctness.generalTauSteps_forward` inhabits it, and covers all three source τ statement
  forms at once because a τ-labelled weak step *is* a τ closure.
  -/
  forwardTauMatch :
    ∀ (config config' : DTR.GeneralRuntimeConfiguration)
      (state : LF.GeneralRuntimeState)
      (label : DTR.GeneralLabel),
      GeneralTraceRelated
        model
        config
        state →
      DTR.GeneralLabel.isTau label →
      Common.WeakStep
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        label
        config' →
      ∃ state' : LF.GeneralRuntimeState,
        Common.WeakStep
            (LF.GeneralStepModulo program)
            LF.GeneralLabel.isTau
            state
            LF.GeneralLabel.tau
            state' ∧
          GeneralTraceRelated
            model
            config'
            state'

  /--
  A source consume is answered by a target consume of the paired event.

  **Carries the forward α′ residue.** Inhabited by
  `Correctness.generalConsume_forward_weak_of_fireRepresentative`, whose α-representative package is a premise
  there and stays one here. The answered event is existential and its `target` is tied to the source's
  receiver, which is all the observable alphabet needs; the event **kind** is deliberately unconstrained (F78).
  -/
  forwardConsumeMatch :
    ∀ (config config' : DTR.GeneralRuntimeConfiguration)
      (state : LF.GeneralRuntimeState)
      (receiver : ActorName)
      (message : DTR.GeneralMessage),
      GeneralTraceRelated
        model
        config
        state →
      Common.WeakStep
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        (DTR.GeneralLabel.consume
          receiver
          message)
        config' →
      ∃ (state' : LF.GeneralRuntimeState)
        (event : LF.GeneralPendingEvent),
        Common.WeakStep
            (LF.GeneralStepModulo program)
            LF.GeneralLabel.isTau
            state
            (LF.GeneralLabel.consume
              event.target
              event.kind)
            state' ∧
          event.target = receiver ∧
          GeneralTraceRelated
            model
            config'
            state'

  /--
  A source time advance is answered by a target time advance with the same endpoints.

  Unconditional. `Correctness.generalTimeAdvance_forward_weak` inhabits it. Both endpoints are preserved
  exactly, which is what lets the observable alphabet keep time whole rather than erasing it.
  -/
  forwardTimeAdvanceMatch :
    ∀ (config config' : DTR.GeneralRuntimeConfiguration)
      (state : LF.GeneralRuntimeState)
      (before after : LogicalTime),
      GeneralTraceRelated
        model
        config
        state →
      Common.WeakStep
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        (DTR.GeneralLabel.timeAdvance
          before
          after)
        config' →
      ∃ state' : LF.GeneralRuntimeState,
        Common.WeakStep
            (LF.GeneralStepModulo program)
            LF.GeneralLabel.isTau
            state
            (LF.GeneralLabel.timeAdvance
              before
              after)
            state' ∧
          GeneralTraceRelated
            model
            config'
            state'

  /--
  A target internal step is answered by a source internal weak step.

  **Carries the `hTauAnswer` residue.** There is no backward τ closure and none is to be built: the target's τ
  set has five constructors against the source's three, `microstepAdvance` has no source counterpart so must be
  answered by *zero* source steps, and the quotient's converse is deliberately absent.

  The answered source label is required to be internal. Without that the field would permit a target τ step to
  be answered by a *visible* source label, which would break the observable agreement this structure exists to
  support.
  -/
  backwardTauMatch :
    ∀ (config : DTR.GeneralRuntimeConfiguration)
      (state state' : LF.GeneralRuntimeState)
      (label : LF.GeneralLabel),
      GeneralTraceRelated
        model
        config
        state →
      LF.GeneralLabel.isTau label →
      Common.WeakStep
        (LF.GeneralStepModulo program)
        LF.GeneralLabel.isTau
        state
        label
        state' →
      ∃ (sourceLabel : DTR.GeneralLabel)
        (config' : DTR.GeneralRuntimeConfiguration),
        DTR.GeneralLabel.isTau sourceLabel ∧
          Common.WeakStep
            (DTR.GeneralStep model)
            DTR.GeneralLabel.isTau
            config
            sourceLabel
            config' ∧
          GeneralTraceRelated
            model
            config'
            state'

  /--
  A target consume is answered by a source consume at the same receiver.

  **Carries the `hName` residue** — the per-step actor agreement, which is not derivable from source-side data
  because `readyActors` and `earliestDueArrival` are functions of the source configuration alone.
  `Correctness.generalConsume_backward_weakStep_of_takeRepresentative` inhabits it and takes `hName` as a
  premise.

  The answered message is existential; only the receiver is pinned, which is exactly what the observable
  alphabet compares.
  -/
  backwardConsumeMatch :
    ∀ (config : DTR.GeneralRuntimeConfiguration)
      (state state' : LF.GeneralRuntimeState)
      (target : ActorName)
      (kind : LF.GeneralEventKind),
      GeneralTraceRelated
        model
        config
        state →
      Common.WeakStep
        (LF.GeneralStepModulo program)
        LF.GeneralLabel.isTau
        state
        (LF.GeneralLabel.consume
          target
          kind)
        state' →
      ∃ (message : DTR.GeneralMessage)
        (config' : DTR.GeneralRuntimeConfiguration),
        Common.WeakStep
            (DTR.GeneralStep model)
            DTR.GeneralLabel.isTau
            config
            (DTR.GeneralLabel.consume
              target
              message)
            config' ∧
          GeneralTraceRelated
            model
            config'
            state'

  /--
  A target time advance is answered by a source time advance with the same endpoints.

  Unconditional in content — `Correctness.generalTimeAdvance_backward_weak` inhabits it — though a caller must
  hold the *raw* target step to apply that theorem, since it is stated over `LF.GeneralStep` while this field
  quantifies over the quotient. Bridging that direction is the forbidden inversion, so the caller supplies the
  answer rather than this structure deriving it.
  -/
  backwardTimeAdvanceMatch :
    ∀ (config : DTR.GeneralRuntimeConfiguration)
      (state state' : LF.GeneralRuntimeState)
      (before after : LogicalTime),
      GeneralTraceRelated
        model
        config
        state →
      Common.WeakStep
        (LF.GeneralStepModulo program)
        LF.GeneralLabel.isTau
        state
        (LF.GeneralLabel.timeAdvance
          before
          after)
        state' →
      ∃ config' : DTR.GeneralRuntimeConfiguration,
        Common.WeakStep
            (DTR.GeneralStep model)
            DTR.GeneralLabel.isTau
            config
            (DTR.GeneralLabel.timeAdvance
              before
              after)
            config' ∧
          GeneralTraceRelated
            model
            config'
            state'

/-!
## The consumers

`.forwardStep` and `.backwardStep`, mirroring how the three sibling *interfaces* are consumed: the structure is
a **hypothesis**, and each theorem dispatches an arbitrary weak step onto the field that answers it.

Both dispatch on the **label**, not on the step. That is what keeps them independent of either system's
internal step count — the target has five τ constructors and the source three, and neither theorem needs to
know. A new label on either side would appear here as a missing case rather than falling through a default.
-/

/--
The interface answers **any** source weak step.

Dispatch on the source label: `tau` to `forwardTauMatch`, `consume` to `forwardConsumeMatch`, `timeAdvance` to
`forwardTimeAdvanceMatch`. The answered target label is returned rather than fixed, because the three fields
answer at three different labels.

The observation equation is produced as well, so a caller gets the trace-level obligation discharged in the
same step. For `tau` it holds because both projections send their internal label to `none`; for the other two
because the answered label carries the same observable content — the receiver in the consume case, both
endpoints in the time case.
-/
theorem GeneralLabelWeakBisimulation.forwardStep
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hBisimulation :
      GeneralLabelWeakBisimulation
        model
        program)
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {label : DTR.GeneralLabel}
    (hRelated :
      GeneralTraceRelated
        model
        config
        state)
    (hStep :
      Common.WeakStep
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        label
        config') :
    ∃ (targetLabel : LF.GeneralLabel)
      (state' : LF.GeneralRuntimeState),
      Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          targetLabel
          state' ∧
        GeneralTraceRelated
          model
          config'
          state' ∧
        GeneralObservable.ofSourceLabel label =
          GeneralObservable.ofTargetLabel targetLabel := by

  cases label with

  | tau =>
      obtain ⟨state', hTargetStep, hNextRelated⟩ :=
        hBisimulation.forwardTauMatch
          config
          config'
          state
          DTR.GeneralLabel.tau
          hRelated
          DTR.GeneralLabel.isTau_tau
          hStep

      exact
        ⟨LF.GeneralLabel.tau,
         state',
         hTargetStep,
         hNextRelated,
         rfl⟩

  | timeAdvance before after =>
      obtain ⟨state', hTargetStep, hNextRelated⟩ :=
        hBisimulation.forwardTimeAdvanceMatch
          config
          config'
          state
          before
          after
          hRelated
          hStep

      exact
        ⟨LF.GeneralLabel.timeAdvance
           before
           after,
         state',
         hTargetStep,
         hNextRelated,
         rfl⟩

  | consume receiver message =>
      obtain ⟨state', event, hTargetStep, hTarget, hNextRelated⟩ :=
        hBisimulation.forwardConsumeMatch
          config
          config'
          state
          receiver
          message
          hRelated
          hStep

      refine
        ⟨LF.GeneralLabel.consume
           event.target
           event.kind,
         state',
         hTargetStep,
         hNextRelated,
         ?_⟩

      rw [
        GeneralObservable.ofSourceLabel_consume,
        GeneralObservable.ofTargetLabel_consume,
        hTarget
      ]

/--
The interface answers **any** target weak step of the quotient system.

The mirror, and together with `forwardStep` what makes the structure a bisimulation interface rather than a
simulation one. Dispatch is again on the label, so the target's larger τ constructor set is invisible here.

The `tau` case needs the field's `DTR.GeneralLabel.isTau sourceLabel` conjunct to close its observation
equation: the answered source label must itself be internal, or the two projections disagree. That is why the
field carries it.
-/
theorem GeneralLabelWeakBisimulation.backwardStep
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hBisimulation :
      GeneralLabelWeakBisimulation
        model
        program)
    {config : DTR.GeneralRuntimeConfiguration}
    {state state' : LF.GeneralRuntimeState}
    {label : LF.GeneralLabel}
    (hRelated :
      GeneralTraceRelated
        model
        config
        state)
    (hStep :
      Common.WeakStep
        (LF.GeneralStepModulo program)
        LF.GeneralLabel.isTau
        state
        label
        state') :
    ∃ (sourceLabel : DTR.GeneralLabel)
      (config' : DTR.GeneralRuntimeConfiguration),
      Common.WeakStep
          (DTR.GeneralStep model)
          DTR.GeneralLabel.isTau
          config
          sourceLabel
          config' ∧
        GeneralTraceRelated
          model
          config'
          state' ∧
        GeneralObservable.ofTargetLabel label =
          GeneralObservable.ofSourceLabel sourceLabel := by

  cases label with

  | tau =>
      obtain ⟨sourceLabel, config', hSourceTau, hSourceStep, hNextRelated⟩ :=
        hBisimulation.backwardTauMatch
          config
          state
          state'
          LF.GeneralLabel.tau
          hRelated
          LF.GeneralLabel.isTau_tau
          hStep

      refine
        ⟨sourceLabel,
         config',
         hSourceStep,
         hNextRelated,
         ?_⟩

      rw [
        (GeneralObservable.ofSourceLabel_eq_none_iff_isTau
          sourceLabel).mpr
          hSourceTau
      ]

      rfl

  | timeAdvance before after =>
      obtain ⟨config', hSourceStep, hNextRelated⟩ :=
        hBisimulation.backwardTimeAdvanceMatch
          config
          state
          state'
          before
          after
          hRelated
          hStep

      exact
        ⟨DTR.GeneralLabel.timeAdvance
           before
           after,
         config',
         hSourceStep,
         hNextRelated,
         rfl⟩

  | consume target kind =>
      obtain ⟨message, config', hSourceStep, hNextRelated⟩ :=
        hBisimulation.backwardConsumeMatch
          config
          state
          state'
          target
          kind
          hRelated
          hStep

      exact
        ⟨DTR.GeneralLabel.consume
           target
           message,
         config',
         hSourceStep,
         hNextRelated,
         rfl⟩

/-!
## Trace agreement from the interface

The payoff, and the reason the structure is worth having rather than the two transfer conditions alone: with
the interface in hand, **both** trace rows follow with no further premises. A caller states the bisimulation
claim once and gets the observable-trace consequence in both directions.
-/

/--
Forward observable-trace agreement, from the interface alone.

`GeneralLabelWeakBisimulation.forwardStep` is exactly `generalTraceAgreement_forward`'s transfer premise, so
this is that theorem at this structure. No residue appears in the statement: they are inside the interface,
which is the point of naming it.
-/
theorem GeneralLabelWeakBisimulation.traceAgreement_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hBisimulation :
      GeneralLabelWeakBisimulation
        model
        program)
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {labels : List DTR.GeneralLabel}
    (hRelated :
      GeneralTraceRelated
        model
        config
        state)
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
        GeneralTraceRelated
          model
          config'
          state' ∧
        Common.observableProjection
            GeneralObservable.ofSourceLabel
            labels =
          Common.observableProjection
            GeneralObservable.ofTargetLabel
            targetLabels :=
  generalTraceAgreement_forward
    (GeneralTraceRelated model)
    (fun _ _ _ _ hRelatedStep hStepOne =>
      hBisimulation.forwardStep
        hRelatedStep
        hStepOne)
    hRelated
    hSteps

/--
Backward observable-trace agreement, from the interface alone.

The mirror. Together with `traceAgreement_forward` this is the bisimulation consequence the paper cites, and
neither statement mentions a residue.
-/
theorem GeneralLabelWeakBisimulation.traceAgreement_backward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hBisimulation :
      GeneralLabelWeakBisimulation
        model
        program)
    {config : DTR.GeneralRuntimeConfiguration}
    {state state' : LF.GeneralRuntimeState}
    {labels : List LF.GeneralLabel}
    (hRelated :
      GeneralTraceRelated
        model
        config
        state)
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
        GeneralTraceRelated
          model
          config'
          state' ∧
        Common.observableProjection
            GeneralObservable.ofTargetLabel
            labels =
          Common.observableProjection
            GeneralObservable.ofSourceLabel
            sourceLabels :=
  generalTraceAgreement_backward
    (GeneralTraceRelated model)
    (fun _ _ _ _ hRelatedStep hStepOne =>
      hBisimulation.backwardStep
        hRelatedStep
        hStepOne)
    hRelated
    hSteps

end Correctness
end Relico
