/-
! # Assembling the general family's trace-agreement transfer premise

`Correctness.generalTraceAgreement_forward` takes a per-step transfer condition as a premise. This module
assembles that condition from what is already proved, leaving exactly one residue named and visible.

## The three cases, and where each comes from

A source `Common.WeakStep` carries one label, and `DTR.GeneralLabel` has three shapes:

* **τ** — discharged outright, from `Correctness.generalTauSteps_forward` and
  `Common.WeakStep.of_tauSteps`. A τ-labelled weak step *is* a τ closure, so no per-statement lemma is
  needed: the closure theorem already covers `assign`, `trace` and `send` together. This is why no
  `generalTrace_forward_weak` / `generalAssign_forward_weak` / `generalSend_forward_weak` exist — they would
  duplicate `generalTauSteps_forward`.
* **`.timeAdvance`** — discharged by reusing `Correctness.generalTimeAdvance_forward_weak`, with the source
  step inverted first. Only `DTR.GeneralStep.timeProgress` can carry that label, so the inversion has one
  case.
* **`.consume`** — **kept as a premise**, in exactly the shape
  `Correctness.generalConsume_forward_weak_of_fireRepresentative` produces. That premise is the α′
  representative package, which this development has deliberately not discharged. Supplying it here would
  claim the frozen question was settled.

## What the relation has to carry, and why it is bundled

The generic trace theorem is parametric in `related`, but the two τ paddings are crossed by
`generalTauSteps_forward_raw`, which consumes **both** store-key uniqueness invariants at every step. A bare
`GeneralStateCorrespondence` is therefore not enough to run the induction, so `GeneralTraceRelated` bundles
the correspondence with both invariants. That is not a strengthening of anything: both invariants are proved
reachable-state facts (`DTR.generalStoreKeyUnique_of_reachable`, `LF.generalStoreKeyUnique_of_reachable`), so
a caller starting from initial states holds them already.

Bundling also makes the relation *inductive* along the transfer, which is the property the generic theorem
needs: each case re-establishes both invariants rather than assuming they survive.

## What this module does not do

It changes no theorem shape. It does not strengthen `hConsumeAnswer`, does not touch the forward spine, does
not modify any `GeneralInstantBlock` proof, does not revisit α or F27, and adds no runtime field. The two
private helpers below are local twins of `private` lemmas in
`Relico/Correctness/GeneralInstantBlockForward.lean`; the house rule prefers duplicating a small lemma over
de-privatising one.
-/
import Relico.Correctness.GeneralObservable

set_option autoImplicit false

namespace Relico
namespace Correctness

/-!
## Two local twins

Both exist as `private` declarations in `Relico/Correctness/GeneralInstantBlockForward.lean`. Duplicated
rather than de-privatised, and the duplication is deliberate: that file's copies serve the block induction
and these serve the trace transfer, so a later change to either breaks only its own consumer.
-/

/--
Source actor-store key uniqueness survives a τ closure.

The mirror of `LF.generalStoreKeyUnique_of_tauSteps` for the side that has only the per-step theorem. The
label filter plays no role — `DTR.generalStoreKeyUnique_of_step` holds at any label — which is why the
induction has no case on it.
-/
private theorem generalStoreKeyUnique_of_sourceTauStepsLocal
    {model : DTR.GeneralModel}
    {config config' : DTR.GeneralRuntimeConfiguration}
    (hUnique :
      DTR.GeneralStoreKeyUnique config)
    (hSteps :
      Common.TauSteps
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        config') :
    DTR.GeneralStoreKeyUnique config' := by
  revert hUnique

  induction hSteps with

  | refl current =>
      intro hUniqueCurrent

      exact hUniqueCurrent

  | cons headStep headIsTau remainingSteps IH =>
      intro hUniqueStep

      exact
        IH
          (DTR.generalStoreKeyUnique_of_step
            hUniqueStep
            headStep)

/--
A visible weak step absorbs a τ closure on either end.

The splice each visible case performs: the source's own weak step pads its visible step with τ segments, the
answer's weak step pads its own, and composing means concatenating four τ segments around one visible step
rather than nesting weak steps.

`cases` on the middle step rather than `induction`, since `Common.WeakStep` has no premise of its own type.
The `tau` alternative is refuted by `hVisible`, which is why visibility is taken explicitly rather than
recovered from the label — the caller has it either way, and taking it keeps the lemma independent of which
labels a family calls internal.
-/
private theorem weakStep_padTauLocal
    {State : Type}
    {Label : Type}
    {step : Common.LabeledTransition State Label}
    {isTau : Label → Prop}
    {source before after target : State}
    {label : Label}
    (hVisible :
      ¬ isTau label)
    (hPrefix :
      Common.TauSteps
        step
        isTau
        source
        before)
    (hMiddle :
      Common.WeakStep
        step
        isTau
        before
        label
        after)
    (hSuffix :
      Common.TauSteps
        step
        isTau
        after
        target) :
    Common.WeakStep
      step
      isTau
      source
      label
      target := by

  cases hMiddle with

  | tau hTau _ =>
      exact
        absurd
          hTau
          hVisible

  | visible _ hInnerPrefix hStep hInnerSuffix =>
      exact
        Common.WeakStep.visible
          hVisible
          (Common.TauSteps.trans
            hPrefix
            hInnerPrefix)
          hStep
          (Common.TauSteps.trans
            hInnerSuffix
            hSuffix)

/-!
## The relation the transfer is inductive along
-/

/--
The correspondence together with both store-key invariants.

The relation `Correctness.generalTraceAgreement_forward` is instantiated at. Bundled rather than passed as
three arguments because the generic theorem takes **one** relation, and because the invariants have to be
re-established at each transfer step rather than assumed to survive — a bundle makes that an obligation the
type system checks.

Neither invariant is a new assumption: both are reachable-state facts
(`DTR.generalStoreKeyUnique_of_reachable`, `LF.generalStoreKeyUnique_of_reachable`), so a caller starting
from initial states holds them. What they buy is the ability to cross τ segments at all —
`generalTauSteps_forward_raw` consumes both at every step.
-/
def GeneralTraceRelated
    (model : DTR.GeneralModel)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState) :
    Prop :=
  GeneralStateCorrespondence
      model
      config
      state ∧
    DTR.GeneralStoreKeyUnique config ∧
      LF.GeneralStoreKeyUnique state

/-!
## The assembled transfer condition

One theorem, three cases, one residue.
-/

/--
**The trace-agreement transfer condition for the general family, assembled.**

Every source weak step is answered by a target weak step of the quotient system, with the relation
re-established and the two labels observing the same thing. This is precisely
`Correctness.generalTraceAgreement_forward`'s `hForward` premise at `Correctness.GeneralTraceRelated`, so a
caller feeds it straight in.

**The three cases.**

* **τ** — `generalTauSteps_forward` produces the target closure and `Common.WeakStep.of_tauSteps` labels it
  `LF.GeneralLabel.tau`. The observation obligation closes because *both* projections send their internal
  label to `none`. No per-statement theorem is involved: a τ-labelled weak step *is* a τ closure, and the
  closure theorem covers `assign`, `trace` and `send` at once — which is why no
  `generalTrace_forward_weak` / `generalAssign_forward_weak` / `generalSend_forward_weak` exist or are needed.
* **`.timeAdvance`** — the visible source step is `cases`d (only `DTR.GeneralStep.timeProgress` carries that
  label) and `generalTimeAdvance_forward_weak` supplies the answer, lifted by
  `LF.GeneralStepModulo.weakStep_of_raw`. Both observed endpoints agree because
  `GeneralStateCorrespondence.logicalTime` equates the clocks and the answer's event sits at `future`.
* **`.consume`** — **delegated to `hConsumeAnswer`**, the premise. Not discharged and not weakened: its shape
  is what `generalConsume_forward_weak_of_fireRepresentative` produces, so a caller who can supply an
  α-representative discharges it by applying that theorem. The α′ question stays open, named, and visible.

**Why the paddings are crossed in the raw system.** Both τ segments are answered by
`generalTauSteps_forward_raw` and lifted only at the splice. `Common.TauSteps` over `LF.GeneralStepModulo`
cannot preserve `LF.GeneralStoreKeyUnique` — a modulo step may switch α-representatives and α cannot see
occurrence multiplicity — so the invariant is re-established on raw closures and never transported through α.

**Why the three τ statement forms are refuted rather than handled** in the `visible` case: they carry
`DTR.GeneralLabel.tau`, so `hVisible : ¬ isTau label` becomes `¬ True` once the label is fixed. `absurd
True.intro hVisible` closes each. A fourth τ rule would appear here as a new unhandled case rather than
falling through.

No theorem shape changed, no `GeneralInstantBlock` proof touched, no α or F27 decision revisited, no runtime
field added.
-/
theorem generalTraceTransfer_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
                  model.classes
                  candidateClass =
                .ok candidateEnv) →
          (List.map
            (fun candidateEntry =>
              candidateEntry.outputPort.value)
            candidateEnv).Nodup)
    (hNames :
      (List.map
        (fun candidate =>
          candidate.name)
        model.instances).Nodup)
    (hConsumeAnswer :
      ∀ (stepConfig stepConfig' : DTR.GeneralRuntimeConfiguration)
        (stepState : LF.GeneralRuntimeState)
        (receiver : ActorName)
        (message : DTR.GeneralMessage),
        GeneralTraceRelated
          model
          stepConfig
          stepState →
        DTR.GeneralStep
          model
          stepConfig
          (DTR.GeneralLabel.consume
            receiver
            message)
          stepConfig' →
        ∃ (stepState' : LF.GeneralRuntimeState)
          (event : LF.GeneralPendingEvent),
          Common.WeakStep
              (LF.GeneralStepModulo program)
              LF.GeneralLabel.isTau
              stepState
              (LF.GeneralLabel.consume
                event.target
                event.kind)
              stepState' ∧
            event.target = receiver ∧
            GeneralTraceRelated
              model
              stepConfig'
              stepState')
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (label : DTR.GeneralLabel)
    (config' : DTR.GeneralRuntimeConfiguration)
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

  obtain ⟨hCorrespondence, hUniqueS, hUniqueT⟩ :=
    hRelated

  cases hStep with

  | tau hTau hSteps =>

      -- The whole τ case. The closure theorem already covers all three τ statement forms.
      obtain ⟨stateRaw, hRawSteps, hRawCorrespondence⟩ :=
        generalTauSteps_forward_raw
          hCompiled
          hRoutes
          hEnvNodup
          hNames
          hCorrespondence
          hUniqueS
          hUniqueT
          hSteps

      refine
        ⟨LF.GeneralLabel.tau,
         stateRaw,
         Common.WeakStep.of_tauSteps
           LF.GeneralLabel.isTau_tau
           (LF.GeneralStepModulo.tauSteps_of_raw
             hRawSteps),
         ⟨hRawCorrespondence,
          generalStoreKeyUnique_of_sourceTauStepsLocal
            hUniqueS
            hSteps,
          LF.generalStoreKeyUnique_of_tauSteps
            hUniqueT
            hRawSteps⟩,
         ?_⟩

      -- Both sides observe nothing, so the projections agree without either being computed.
      rw [
        (GeneralObservable.ofSourceLabel_eq_none_iff_isTau
          label).mpr
          hTau
      ]

      rfl

  | visible hVisible hPrefix hVisibleStep hSuffix =>

      -- The τ prefix, crossed in the RAW target system so the invariant survives it.
      obtain ⟨stateBefore, hRawPrefix, hCorrespondenceBefore⟩ :=
        generalTauSteps_forward_raw
          hCompiled
          hRoutes
          hEnvNodup
          hNames
          hCorrespondence
          hUniqueS
          hUniqueT
          hPrefix

      have hUniqueSBefore :
          DTR.GeneralStoreKeyUnique _ :=
        generalStoreKeyUnique_of_sourceTauStepsLocal
          hUniqueS
          hPrefix

      have hUniqueTBefore :
          LF.GeneralStoreKeyUnique stateBefore :=
        LF.generalStoreKeyUnique_of_tauSteps
          hUniqueT
          hRawPrefix

      cases hVisibleStep with

      | assign hActor hBody hEvaluate =>
          exact
            absurd
              True.intro
              hVisible

      | trace hActor hBody =>
          exact
            absurd
              True.intro
              hVisible

      | send hSender hBody hArguments hTarget hReceiver =>
          exact
            absurd
              True.intro
              hVisible

      -- Stage H's three step-into rules are τ, so they are refuted by the visibility premise
      -- exactly as the three τ rules above are.
      | branchTrue hActor hBody hCondition =>
          exact
            absurd
              True.intro
              hVisible

      | branchFalse hActor hBody hCondition =>
          exact
            absurd
              True.intro
              hVisible

      | resume hActor hBody hFrames =>
          exact
            absurd
              True.intro
              hVisible

      | take hSelected hName hActor hIdle hDue hArrival hServer =>

          -- The consume case: delegated to the premise, which is the α′ residue.
          obtain ⟨stateAfter, event, hAnswerStep, hAnswerTarget, hAnswerRelated⟩ :=
            hConsumeAnswer
              _
              _
              stateBefore
              _
              _
              ⟨hCorrespondenceBefore,
               hUniqueSBefore,
               hUniqueTBefore⟩
              (DTR.GeneralStep.take
                hSelected
                hName
                hActor
                hIdle
                hDue
                hArrival
                hServer)

          obtain ⟨hAfterCorrespondence, hAfterUniqueS, hAfterUniqueT⟩ :=
            hAnswerRelated

          -- The τ suffix, again raw.
          obtain ⟨stateFinal, hRawSuffix, hFinalCorrespondence⟩ :=
            generalTauSteps_forward_raw
              hCompiled
              hRoutes
              hEnvNodup
              hNames
              hAfterCorrespondence
              hAfterUniqueS
              hAfterUniqueT
              hSuffix

          refine
            ⟨LF.GeneralLabel.consume
                 event.target
                 event.kind,
             stateFinal,
             weakStep_padTauLocal
               (LF.GeneralLabel.not_isTau_consume
                 event.target
                 event.kind)
               (LF.GeneralStepModulo.tauSteps_of_raw
                 hRawPrefix)
               hAnswerStep
               (LF.GeneralStepModulo.tauSteps_of_raw
                 hRawSuffix),
             ⟨hFinalCorrespondence,
              generalStoreKeyUnique_of_sourceTauStepsLocal
                hAfterUniqueS
                hSuffix,
              LF.generalStoreKeyUnique_of_tauSteps
                hAfterUniqueT
                hRawSuffix⟩,
             ?_⟩

          -- Receiver identity is the whole observation, and the answer supplies it.
          rw [
            GeneralObservable.ofSourceLabel_consume,
            GeneralObservable.ofTargetLabel_consume,
            hAnswerTarget
          ]

      | timeProgress hForward hQuiescent hSelected =>

          -- The time case: `generalTimeAdvance_forward_weak`, reused unchanged.
          obtain ⟨event, hEventTime, hAnswerStep, hAnswerCorrespondence⟩ :=
            generalTimeAdvance_forward_weak
              program
              model
              _
              stateBefore
              _
              hCorrespondenceBefore
              hForward
              hQuiescent
              hSelected

          have hAnswerUniqueT :
              LF.GeneralStoreKeyUnique
                {
                  currentTag := event.tag
                  reactors := stateBefore.reactors
                  pending := stateBefore.pending
                } :=
            hUniqueTBefore

          -- The τ suffix.
          -- The source invariant after the clock moves. `timeProgress` rebuilds the configuration with the
          -- SAME actor store, so this is the per-step theorem at the rule itself rather than a new fact.
          have hUniqueSAfter :
              DTR.GeneralStoreKeyUnique _ :=
            DTR.generalStoreKeyUnique_of_step
              hUniqueSBefore
              (DTR.GeneralStep.timeProgress
                (model := model)
                hForward
                hQuiescent
                hSelected)

          obtain ⟨stateFinal, hRawSuffix, hFinalCorrespondence⟩ :=
            generalTauSteps_forward_raw
              hCompiled
              hRoutes
              hEnvNodup
              hNames
              hAnswerCorrespondence
              hUniqueSAfter
              hAnswerUniqueT
              hSuffix

          refine
            ⟨LF.GeneralLabel.timeAdvance
                 stateBefore.currentTag.time
                 event.tag.time,
             stateFinal,
             weakStep_padTauLocal
               (LF.GeneralLabel.not_isTau_timeAdvance
                 stateBefore.currentTag.time
                 event.tag.time)
               (LF.GeneralStepModulo.tauSteps_of_raw
                 hRawPrefix)
               (LF.GeneralStepModulo.weakStep_of_raw
                 hAnswerStep)
               (LF.GeneralStepModulo.tauSteps_of_raw
                 hRawSuffix),
             ⟨hFinalCorrespondence,
              generalStoreKeyUnique_of_sourceTauStepsLocal
                hUniqueSAfter
                hSuffix,
              LF.generalStoreKeyUnique_of_tauSteps
                hAnswerUniqueT
                hRawSuffix⟩,
             ?_⟩

          -- Both endpoints agree: the source's clock is the target's by `logicalTime`, and the answer's
          -- event sits at the source's `future`.
          rw [
            GeneralObservable.ofSourceLabel_timeAdvance,
            GeneralObservable.ofTargetLabel_timeAdvance,
            hEventTime,
            hCorrespondenceBefore.logicalTime
          ]

/-!
## The row

The forward trace agreement with its transfer condition discharged down to the one residue.
-/

/--
**Forward trace agreement for the general family, with the transfer condition assembled.**

The row this milestone exists to produce. Everything is discharged except the `.consume` answer, which is
carried through as `hConsumeAnswer` — the α′ representative residue, unchanged and unweakened.

Read it as: *given a way to answer one source consume, every source execution is answered by a target
execution observing the same sequence.* The τ and `.timeAdvance` cases are not assumptions of this theorem;
they are proved inside it, from `generalTauSteps_forward` and `generalTimeAdvance_forward_weak` respectively.

`Correctness.GeneralTraceRelated` is the relation, so the conclusion also re-establishes both store-key
invariants at the end state — which is what makes the result composable with another execution segment
rather than terminal.
-/
theorem generalTraceAgreement_of_consumeAnswer
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
                  model.classes
                  candidateClass =
                .ok candidateEnv) →
          (List.map
            (fun candidateEntry =>
              candidateEntry.outputPort.value)
            candidateEnv).Nodup)
    (hNames :
      (List.map
        (fun candidate =>
          candidate.name)
        model.instances).Nodup)
    (hConsumeAnswer :
      ∀ (stepConfig stepConfig' : DTR.GeneralRuntimeConfiguration)
        (stepState : LF.GeneralRuntimeState)
        (receiver : ActorName)
        (message : DTR.GeneralMessage),
        GeneralTraceRelated
          model
          stepConfig
          stepState →
        DTR.GeneralStep
          model
          stepConfig
          (DTR.GeneralLabel.consume
            receiver
            message)
          stepConfig' →
        ∃ (stepState' : LF.GeneralRuntimeState)
          (event : LF.GeneralPendingEvent),
          Common.WeakStep
              (LF.GeneralStepModulo program)
              LF.GeneralLabel.isTau
              stepState
              (LF.GeneralLabel.consume
                event.target
                event.kind)
              stepState' ∧
            event.target = receiver ∧
            GeneralTraceRelated
              model
              stepConfig'
              stepState')
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
    (generalTraceTransfer_forward
      hCompiled
      hRoutes
      hEnvNodup
      hNames
      hConsumeAnswer)
    hRelated
    hSteps

/-!
## The backward direction

`Correctness.generalTraceAgreement_backward` needs the mirror transfer condition. **It is not the mirror of
the forward one**, and the asymmetry is measured rather than assumed — the audit that produced this section
is recorded in the docstring of `generalTraceTransfer_backward` below.

Two of the three cases are in hand and are reused unchanged:
`Correctness.generalConsume_backward_weakStep_of_takeRepresentative` and
`Correctness.generalTimeAdvance_backward_weak`. The τ case is a **premise**, for reasons that are structural
rather than a matter of effort.
-/

/--
**The backward trace-agreement transfer condition, assembled.**

Every target weak step of the quotient system is answered by a source weak step, with the relation
re-established and the two labels observing the same thing. This is
`Correctness.generalTraceAgreement_backward`'s `hBackward` premise at `Correctness.GeneralTraceRelated`.

**Three cases, two reused, one a premise.**

* **`.consume`** — `hConsumeAnswer`, whose shape is exactly
  `generalConsume_backward_weakStep_of_takeRepresentative`'s conclusion. A caller discharges it by applying
  that theorem, supplying its `hName` per-step actor agreement. Unchanged from what landed.
* **`.timeAdvance`** — `hTimeAnswer`, whose shape is exactly `generalTimeAdvance_backward_weak`'s
  conclusion. Also a premise rather than an inlined application, and for a reason worth stating: that
  theorem is proved against `LF.GeneralStep`, while this transfer is handed an `LF.GeneralStepModulo` step.
  Inverting the modulo step to reach the raw one is precisely what is forbidden here, so the caller — who
  holds the raw step — applies it and hands the answer in.
* **τ** — `hTauAnswer`, the premise this milestone introduces.

**Why the τ case cannot be derived, in three independent ways.** All three were measured against the
definitions, not assumed:

1. **The target's τ set has five constructors, not three.** `LF.GeneralStep.now_eq_of_tau`'s own case list
   is `assign`, `trace`, `schedule`, `setPort`, `microstepAdvance`. The source has three. So there is no
   shape-by-shape correspondence to induct along.
2. **`microstepAdvance` has no source counterpart at all.** It is P24's measured divergence — a zero-delay
   send costs the target a microstep the source never takes — so a backward τ step there must be answered by
   *zero* source steps. No forward case ever had to answer a step with nothing.
3. **The quotient runs the wrong way, and deliberately.** `LF.GeneralStepModulo.tauSteps_of_raw` and
   `weakStep_of_raw` lift raw to modulo; `weakStep_of_raw`'s docstring records that "the converse is
   deliberately absent: a modulo weak step may switch representatives between segments, and that is the
   quotient's semantics, not an accident to be undone." A backward τ closure would have to invert exactly
   that, which reopens the frozen α′ question.

So the τ answer is carried as a premise, named and visible, exactly as the forward direction carries its
α-representative package. **No modulo-to-raw lemma is added, no α′ decision is touched, and no backward τ
closure is attempted.**

**What is still proved here rather than assumed:** that the three premises *compose* into the shape the
generic trace theorem consumes, that the observation obligation is discharged in every case, and that both
store-key invariants are threaded. The τ premise's observation obligation closes from
`ofTargetLabel_eq_none_iff_isTau` and `ofSourceLabel_eq_none_iff_isTau` together — a target τ step must be
answered by a source label that is *also* internal, which the premise's own `isTau` conclusion supplies.

No theorem shape changed, `hConsumeAnswer` unchanged, `GeneralInstantBlock` untouched, no runtime field, no
F27 change.
-/
theorem generalTraceTransfer_backward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hTauAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (label : LF.GeneralLabel),
        GeneralTraceRelated
          model
          stepConfig
          stepState →
        LF.GeneralLabel.isTau label →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          stepState
          label
          stepState' →
        ∃ (sourceLabel : DTR.GeneralLabel)
          (stepConfig' : DTR.GeneralRuntimeConfiguration),
          DTR.GeneralLabel.isTau sourceLabel ∧
            Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              stepConfig
              sourceLabel
              stepConfig' ∧
            GeneralTraceRelated
              model
              stepConfig'
              stepState')
    (hConsumeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (target : ActorName)
        (kind : LF.GeneralEventKind),
        GeneralTraceRelated
          model
          stepConfig
          stepState →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.consume
            target
            kind)
          stepState' →
        ∃ (message : DTR.GeneralMessage)
          (stepConfig' : DTR.GeneralRuntimeConfiguration),
          Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.consume
                target
                message)
              stepConfig' ∧
            GeneralTraceRelated
              model
              stepConfig'
              stepState')
    (hTimeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (before after : LogicalTime),
        GeneralTraceRelated
          model
          stepConfig
          stepState →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.timeAdvance
            before
            after)
          stepState' →
        ∃ stepConfig' : DTR.GeneralRuntimeConfiguration,
          Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.timeAdvance
                before
                after)
              stepConfig' ∧
            GeneralTraceRelated
              model
              stepConfig'
              stepState')
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (label : LF.GeneralLabel)
    (state' : LF.GeneralRuntimeState)
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

  -- The label decides which premise answers. Splitting on the LABEL rather than on the step is what keeps
  -- this independent of the target's τ constructor count: a sixth τ rule would change nothing here.
  cases label with

  | tau =>

      obtain ⟨sourceLabel, config', hSourceTau, hSourceStep, hSourceRelated⟩ :=
        hTauAnswer
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
         hSourceRelated,
         ?_⟩

      -- Both sides observe nothing. The premise's own `isTau` conclusion is what makes the source side
      -- internal too — without it a target τ step could be answered by a visible source label, and the
      -- observation would not agree.
      rw [
        (GeneralObservable.ofSourceLabel_eq_none_iff_isTau
          sourceLabel).mpr
          hSourceTau
      ]

      rfl

  | timeAdvance before after =>

      obtain ⟨config', hSourceStep, hSourceRelated⟩ :=
        hTimeAnswer
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
         hSourceRelated,
         rfl⟩

  | consume target kind =>

      obtain ⟨message, config', hSourceStep, hSourceRelated⟩ :=
        hConsumeAnswer
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
         hSourceRelated,
         rfl⟩

/--
**Backward trace agreement for the general family, with the transfer condition assembled.**

The mirror of `generalTraceAgreement_of_consumeAnswer`, and together with it the pair that makes the
observable-trace story a bisimulation rather than a simulation.

Three residues rather than the forward direction's one, and the count is the honest measurement: the target
has five τ constructors against the source's three, `microstepAdvance` has no source counterpart, and the
quotient has no sound inverse. Each residue is per-step and named. Two of the three have existing theorems
whose conclusions are exactly their shapes — `generalConsume_backward_weakStep_of_takeRepresentative` and
`generalTimeAdvance_backward_weak` — so a caller holding raw target steps discharges them directly.
-/
theorem generalTraceAgreement_backward_of_answers
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hTauAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (label : LF.GeneralLabel),
        GeneralTraceRelated
          model
          stepConfig
          stepState →
        LF.GeneralLabel.isTau label →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          stepState
          label
          stepState' →
        ∃ (sourceLabel : DTR.GeneralLabel)
          (stepConfig' : DTR.GeneralRuntimeConfiguration),
          DTR.GeneralLabel.isTau sourceLabel ∧
            Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              stepConfig
              sourceLabel
              stepConfig' ∧
            GeneralTraceRelated
              model
              stepConfig'
              stepState')
    (hConsumeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (target : ActorName)
        (kind : LF.GeneralEventKind),
        GeneralTraceRelated
          model
          stepConfig
          stepState →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.consume
            target
            kind)
          stepState' →
        ∃ (message : DTR.GeneralMessage)
          (stepConfig' : DTR.GeneralRuntimeConfiguration),
          Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.consume
                target
                message)
              stepConfig' ∧
            GeneralTraceRelated
              model
              stepConfig'
              stepState')
    (hTimeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (before after : LogicalTime),
        GeneralTraceRelated
          model
          stepConfig
          stepState →
        Common.WeakStep
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.timeAdvance
            before
            after)
          stepState' →
        ∃ stepConfig' : DTR.GeneralRuntimeConfiguration,
          Common.WeakStep
              (DTR.GeneralStep model)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.timeAdvance
                before
                after)
              stepConfig' ∧
            GeneralTraceRelated
              model
              stepConfig'
              stepState')
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
    (generalTraceTransfer_backward
      hTauAnswer
      hConsumeAnswer
      hTimeAnswer)
    hRelated
    hSteps

end Correctness
end Relico
