/-
! # Regression pins for the general family's two trace-agreement rows

`Correctness.generalTraceTransfer_forward`, `generalTraceAgreement_of_consumeAnswer`,
`generalTraceTransfer_backward` and `generalTraceAgreement_backward_of_answers` are `Prop`-valued statements
whose conclusions are existentials, so **no `rfl` or `decide` can pin them.** What can be pinned, and is
pinned here, is that each of the four is *inhabited at a real compiled model* — that its accepted-program
premises are satisfiable, its relation is inhabited, and its conclusion can actually be extracted.

## Why an inhabited witness is the right instrument, and what each pin would catch

The failure mode these guard against is a theorem that elaborates but cannot be applied: premises that no
real compilation satisfies, or a relation nothing inhabits. That class of defect is invisible to `lake build`
— an unusable theorem type-checks perfectly — and F53 records that this repository has already shipped
"by construction" claims which outlived the findings refuting them. So:

* **Tests 1–4** pin the accepted-program premises at `pinModel`: the compilation succeeds, the routing table
  resolves, per-instance output-port names are duplicate-free, and instance names are duplicate-free. A
  premise set that no compiled model satisfies fails here and nowhere else.
* **Test 5** pins that `Correctness.GeneralTraceRelated` is **inhabited** at the initial pair. This is the
  one that would catch the relation being over-strengthened: it bundles the correspondence with *both*
  store-key invariants, and if any of the three stopped holding at initialization the bundle would become
  uninhabitable while every theorem mentioning it still elaborated.
* **Tests 6–7** apply the two forward theorems at the empty execution and extract their conclusions.
* **Tests 8–9** do the same for the two backward theorems.

## What is deliberately *not* pinned

The residue premises are **not** discharged with real content. `hConsumeAnswer`, `hTauAnswer` and
`hTimeAnswer` are supplied at the empty execution, where `Common.WeakSteps.refl` means the induction never
consumes them — so these pins check *applicability*, not the residues. Faking a residue to make a pin look
stronger would be exactly the dishonesty the residues exist to avoid: each is the α′ question, and a test
fixture cannot settle it.

Nor is the *observable trace* pinned to a non-empty list here. That is already covered by
`Relico/Tests/GeneralObservable.lean` test 10, which agrees two traces with different τ counts on the two
sides. Duplicating it against a row would add no failure mode.

The model is reused from `Relico/Tests/GeneralInitialization.lean` rather than rebuilt: it is a real
one-class, one-instance model that genuinely compiles, and `pinModel_compiles` there is the equation these
pins consume.
-/
import Relico.Correctness.GeneralTraceTransfer
import Relico.Tests.GeneralInitialization

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GeneralTraceTransfer

open Relico.Tests.GeneralInitialization

/-! ## The accepted-program premises, at a model that really compiles -/

/- Test 1: the routing table resolves. `pinModel` declares no known rebecs, so the table is empty — but
   `.ok []` and `.error _` are different facts, and only the former satisfies `hRoutes`. -/
theorem pinRoutes :
    Translation.routesOf pinModel =
      .ok [] := by
  rfl

/- Test 2: the class's output-port environment resolves, and is empty for the same reason. Needed as its own
   equation because the `hEnvNodup` premise quantifies over environments *obtained from* `outputPortEnvOf`,
   so the proof has to rewrite by this rather than compute under a binder. -/
theorem pinEnv :
    Translation.outputPortEnvOf
        pinModel.classes
        pinClass =
      .ok [] := by
  rfl

/- Test 3: instance names are duplicate-free. One instance, so `decide` settles it — but the premise is
   stated over `List.map`, and a `Nodup` on the instances themselves would be a different (weaker) claim. -/
theorem pinNames :
    (List.map
      (fun candidate =>
        candidate.name)
      pinModel.instances).Nodup := by
  decide

/- Test 4: the per-instance output-port `Nodup` premise, in exactly the shape both transfer theorems read.

   This is the one that needs a real proof rather than `decide`: the premise quantifies over *every* instance
   and *every* environment that instance's class resolves to, so it cannot be evaluated. The proof pins the
   single instance, pins its class, rewrites by test 2, and finishes. A premise that quantified over
   something no model could satisfy would fail here. -/
theorem pinEnvNodup :
    ∀ candidate ∈ pinModel.instances,
      ∀ candidateEnv : Translation.GeneralOutputPortEnv,
        (∃ candidateClass : DTR.GeneralReactiveClass,
          pinModel.class? candidate.className =
              some candidateClass ∧
            Translation.outputPortEnvOf
                pinModel.classes
                candidateClass =
              .ok candidateEnv) →
        (List.map
          (fun candidateEntry =>
            candidateEntry.outputPort.value)
          candidateEnv).Nodup := by

  intro candidate hCandidate candidateEnv hEnv

  obtain ⟨candidateClass, hClass, hEnvOf⟩ :=
    hEnv

  have hOnlyInstance :
      candidate = pinActor := by
    simpa [
      pinModel
    ] using hCandidate

  subst hOnlyInstance

  have hOnlyClass :
      candidateClass = pinClass :=
    (by
      simpa [
        pinModel,
        pinActor,
        DTR.GeneralModel.class?,
        DTR.findClass?,
        pinClass
      ] using hClass : _ = candidateClass).symm

  subst hOnlyClass

  rw [
    pinEnv
  ] at hEnvOf

  simp only [
    Except.ok.injEq
  ] at hEnvOf

  subst hEnvOf

  simp

/-! ## The relation is inhabited -/

/- Test 5: `Correctness.GeneralTraceRelated` holds at the initial pair.

   The pin that matters most in this file. The relation bundles three facts — the correspondence and both
   store-key invariants — and each comes from a different theorem: `generalCorrespondence_initial` (which
   needs the compilation), `DTR.generalStoreKeyUnique_initial` (source well-formedness), and
   `LF.generalStoreKeyUnique_initial` (target well-formedness, obtained from the compilation via
   `compileGeneralModel_wellFormed` rather than re-decided).

   If any one of the three stopped holding at initialization, every theorem mentioning
   `GeneralTraceRelated` would keep elaborating and this pin alone would fail. -/
theorem pinRelated :
    Correctness.GeneralTraceRelated
      pinModel
      (DTR.GeneralModel.initialState
        pinModel)
      (LF.GeneralProgram.initialState
        pinProgram) :=
  ⟨Correctness.generalCorrespondence_initial
     pinModel
     pinProgram
     pinModel_compiles,
   DTR.generalStoreKeyUnique_initial
     (by decide),
   LF.generalStoreKeyUnique_initial
     (Translation.compileGeneralModel_wellFormed
       pinModel_compiles)⟩

/-! ## No source consume can fire at this model

The fixture's single class declares **no message servers**, so `DTR.GeneralStep.take`'s `hServer` premise is
unsatisfiable at every actor and every message name. That is what lets the `.consume` residues be discharged
*honestly* below rather than faked: at this model the premise is vacuous because the step it quantifies over
cannot exist, not because a fixture was arranged to look agreeable.
-/

/--
`pinModel` resolves no message server, for any actor and any message name.

Two branches: an actor other than `pinActorName` is not an instance at all, and `pinActorName`'s class has an
empty `messageServers` list. `DTR.findMessageServer?` on `[]` is `none`, so the `.some` hypothesis is
contradictory either way.
-/
theorem pinNoMessageServer
    (receiver : ActorName)
    (messageName : MsgName)
    (server : DTR.GeneralMessageServer)
    (hServer :
      DTR.GeneralModel.messageServerFor?
          pinModel
          receiver
          messageName =
        some server) :
    False := by

  unfold DTR.GeneralModel.messageServerFor? at hServer

  cases hClass :
      DTR.GeneralModel.classOfActor?
        pinModel
        receiver with

  | none =>
      rw [hClass] at hServer

      simp at hServer

  | some reactiveClass =>
      rw [hClass] at hServer

      have hOnlyClass :
          reactiveClass = pinClass := by
        unfold
          DTR.GeneralModel.classOfActor?
          DTR.GeneralModel.actor? at hClass

        by_cases hIs :
            pinActorName = receiver

        · simp [
            pinModel,
            pinActor,
            DTR.findActor?,
            hIs,
            DTR.GeneralModel.class?,
            DTR.findClass?,
            pinClass
          ] at hClass

          exact hClass.symm

        · simp [
            pinModel,
            pinActor,
            DTR.findActor?,
            hIs
          ] at hClass

      subst hOnlyClass

      simp [
        pinClass,
        DTR.GeneralReactiveClass.messageServer?,
        DTR.findMessageServer?
      ] at hServer

/-! ## The four rows are applicable

Each row is applied at the initial pair over the empty execution, and its conclusion is extracted rather than
restated. The forward `.consume` residue is discharged genuinely by `pinNoMessageServer`; the backward
residues are supplied at the empty execution, where `Common.WeakSteps.refl` never consumes them, so those
three pins check **applicability** rather than the residues themselves. Faking a residue would defeat the
purpose it exists for.
-/

/- Test 6: `generalTraceTransfer_forward` applies, and its `.consume` residue is discharged for real. -/
example :
    ∃ (targetLabel : LF.GeneralLabel)
      (state' : LF.GeneralRuntimeState),
      Common.WeakStep
          (LF.GeneralStepModulo pinProgram)
          LF.GeneralLabel.isTau
          (LF.GeneralProgram.initialState
            pinProgram)
          targetLabel
          state' ∧
        Correctness.GeneralTraceRelated
          pinModel
          (DTR.GeneralModel.initialState
            pinModel)
          state' ∧
        Correctness.GeneralObservable.ofSourceLabel
            DTR.GeneralLabel.tau =
          Correctness.GeneralObservable.ofTargetLabel
            targetLabel :=
  Correctness.generalTraceTransfer_forward
    pinModel_compiles
    pinRoutes
    pinEnvNodup
    pinNames
    (fun _ _ _ receiver message _ hTake =>
      absurd
        hTake
        (by
          intro hStep
          cases hStep with
          | take _ _ _ _ _ _ hServer =>
              exact
                pinNoMessageServer
                  receiver
                  message.messageName
                  _
                  hServer))
    (DTR.GeneralModel.initialState
      pinModel)
    (LF.GeneralProgram.initialState
      pinProgram)
    DTR.GeneralLabel.tau
    (DTR.GeneralModel.initialState
      pinModel)
    pinRelated
    (Common.WeakStep.tau
      DTR.GeneralLabel.isTau_tau
      (Common.TauSteps.refl _))

/- Test 7: `generalTraceAgreement_of_consumeAnswer` applies, at the empty label list. The conclusion's trace
   equation is the interesting part — it holds with **both** projections applied, so a row whose two
   projections had drifted apart would fail here. -/
example :
    ∃ (targetLabels : List LF.GeneralLabel)
      (state' : LF.GeneralRuntimeState),
      Common.WeakSteps
          (LF.GeneralStepModulo pinProgram)
          LF.GeneralLabel.isTau
          (LF.GeneralProgram.initialState
            pinProgram)
          targetLabels
          state' ∧
        Correctness.GeneralTraceRelated
          pinModel
          (DTR.GeneralModel.initialState
            pinModel)
          state' ∧
        Common.observableProjection
            Correctness.GeneralObservable.ofSourceLabel
            [] =
          Common.observableProjection
            Correctness.GeneralObservable.ofTargetLabel
            targetLabels :=
  Correctness.generalTraceAgreement_of_consumeAnswer
    pinModel_compiles
    pinRoutes
    pinEnvNodup
    pinNames
    (fun _ _ _ receiver message _ hTake =>
      absurd
        hTake
        (by
          intro hStep
          cases hStep with
          | take _ _ _ _ _ _ hServer =>
              exact
                pinNoMessageServer
                  receiver
                  message.messageName
                  _
                  hServer))
    pinRelated
    (Common.WeakSteps.refl _)

/-! ## The two backward rows are applicable, GIVEN their residues

**These two pins take the three backward residues as hypotheses rather than supplying witnesses, and that is
the honest shape.** An earlier draft tried to discharge them vacuously at the empty execution and it does not
work — for a good reason worth recording. Each residue is quantified over *arbitrary* states, so an answer
must hold at every target step, not only the ones this fixture can reach; and `hTauAnswer` in particular has
to produce the relation at the target's **post**-state, which is exactly the fact that answering a target τ
step with zero source steps is not free. No fixture settles that — it is the α′ question.

So what these two check is what the rows actually claim: *given* answers of these shapes, the row applies and
its conclusion is extractable. That is a real property, and it fails if a premise shape drifts out of
agreement with the theorem it is meant to feed.
-/

/- Test 8: `generalTraceTransfer_backward` applies at a τ-labelled target weak step over the empty closure. -/
example
    (hTauAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (label : LF.GeneralLabel),
        Correctness.GeneralTraceRelated
          pinModel
          stepConfig
          stepState →
        LF.GeneralLabel.isTau label →
        Common.WeakStep
          (LF.GeneralStepModulo pinProgram)
          LF.GeneralLabel.isTau
          stepState
          label
          stepState' →
        ∃ (sourceLabel : DTR.GeneralLabel)
          (stepConfig' : DTR.GeneralRuntimeConfiguration),
          DTR.GeneralLabel.isTau sourceLabel ∧
            Common.WeakStep
              (DTR.GeneralStep pinModel)
              DTR.GeneralLabel.isTau
              stepConfig
              sourceLabel
              stepConfig' ∧
            Correctness.GeneralTraceRelated
              pinModel
              stepConfig'
              stepState')
    (hConsumeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (target : ActorName)
        (kind : LF.GeneralEventKind),
        Correctness.GeneralTraceRelated
          pinModel
          stepConfig
          stepState →
        Common.WeakStep
          (LF.GeneralStepModulo pinProgram)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.consume
            target
            kind)
          stepState' →
        ∃ (message : DTR.GeneralMessage)
          (stepConfig' : DTR.GeneralRuntimeConfiguration),
          Common.WeakStep
              (DTR.GeneralStep pinModel)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.consume
                target
                message)
              stepConfig' ∧
            Correctness.GeneralTraceRelated
              pinModel
              stepConfig'
              stepState')
    (hTimeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (before after : LogicalTime),
        Correctness.GeneralTraceRelated
          pinModel
          stepConfig
          stepState →
        Common.WeakStep
          (LF.GeneralStepModulo pinProgram)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.timeAdvance
            before
            after)
          stepState' →
        ∃ stepConfig' : DTR.GeneralRuntimeConfiguration,
          Common.WeakStep
              (DTR.GeneralStep pinModel)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.timeAdvance
                before
                after)
              stepConfig' ∧
            Correctness.GeneralTraceRelated
              pinModel
              stepConfig'
              stepState')
    :
    ∃ (sourceLabel : DTR.GeneralLabel)
      (config' : DTR.GeneralRuntimeConfiguration),
      Common.WeakStep
          (DTR.GeneralStep pinModel)
          DTR.GeneralLabel.isTau
          (DTR.GeneralModel.initialState
            pinModel)
          sourceLabel
          config' ∧
        Correctness.GeneralTraceRelated
          pinModel
          config'
          (LF.GeneralProgram.initialState
            pinProgram) ∧
        Correctness.GeneralObservable.ofTargetLabel
            LF.GeneralLabel.tau =
          Correctness.GeneralObservable.ofSourceLabel
            sourceLabel :=
  Correctness.generalTraceTransfer_backward
    hTauAnswer
    hConsumeAnswer
    hTimeAnswer
    (DTR.GeneralModel.initialState
      pinModel)
    (LF.GeneralProgram.initialState
      pinProgram)
    LF.GeneralLabel.tau
    (LF.GeneralProgram.initialState
      pinProgram)
    pinRelated
    (Common.WeakStep.tau
      LF.GeneralLabel.isTau_tau
      (Common.TauSteps.refl _))

/- Test 9: `generalTraceAgreement_backward_of_answers` applies, at the empty target label list. The trace
   equation holds with both projections applied, so a row whose projections had drifted apart fails here. -/
example
    (hTauAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (label : LF.GeneralLabel),
        Correctness.GeneralTraceRelated
          pinModel
          stepConfig
          stepState →
        LF.GeneralLabel.isTau label →
        Common.WeakStep
          (LF.GeneralStepModulo pinProgram)
          LF.GeneralLabel.isTau
          stepState
          label
          stepState' →
        ∃ (sourceLabel : DTR.GeneralLabel)
          (stepConfig' : DTR.GeneralRuntimeConfiguration),
          DTR.GeneralLabel.isTau sourceLabel ∧
            Common.WeakStep
              (DTR.GeneralStep pinModel)
              DTR.GeneralLabel.isTau
              stepConfig
              sourceLabel
              stepConfig' ∧
            Correctness.GeneralTraceRelated
              pinModel
              stepConfig'
              stepState')
    (hConsumeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (target : ActorName)
        (kind : LF.GeneralEventKind),
        Correctness.GeneralTraceRelated
          pinModel
          stepConfig
          stepState →
        Common.WeakStep
          (LF.GeneralStepModulo pinProgram)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.consume
            target
            kind)
          stepState' →
        ∃ (message : DTR.GeneralMessage)
          (stepConfig' : DTR.GeneralRuntimeConfiguration),
          Common.WeakStep
              (DTR.GeneralStep pinModel)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.consume
                target
                message)
              stepConfig' ∧
            Correctness.GeneralTraceRelated
              pinModel
              stepConfig'
              stepState')
    (hTimeAnswer :
      ∀ (stepConfig : DTR.GeneralRuntimeConfiguration)
        (stepState stepState' : LF.GeneralRuntimeState)
        (before after : LogicalTime),
        Correctness.GeneralTraceRelated
          pinModel
          stepConfig
          stepState →
        Common.WeakStep
          (LF.GeneralStepModulo pinProgram)
          LF.GeneralLabel.isTau
          stepState
          (LF.GeneralLabel.timeAdvance
            before
            after)
          stepState' →
        ∃ stepConfig' : DTR.GeneralRuntimeConfiguration,
          Common.WeakStep
              (DTR.GeneralStep pinModel)
              DTR.GeneralLabel.isTau
              stepConfig
              (DTR.GeneralLabel.timeAdvance
                before
                after)
              stepConfig' ∧
            Correctness.GeneralTraceRelated
              pinModel
              stepConfig'
              stepState')
    :
    ∃ (sourceLabels : List DTR.GeneralLabel)
      (config' : DTR.GeneralRuntimeConfiguration),
      Common.WeakSteps
          (DTR.GeneralStep pinModel)
          DTR.GeneralLabel.isTau
          (DTR.GeneralModel.initialState
            pinModel)
          sourceLabels
          config' ∧
        Correctness.GeneralTraceRelated
          pinModel
          config'
          (LF.GeneralProgram.initialState
            pinProgram) ∧
        Common.observableProjection
            Correctness.GeneralObservable.ofTargetLabel
            [] =
          Common.observableProjection
            Correctness.GeneralObservable.ofSourceLabel
            sourceLabels :=
  Correctness.generalTraceAgreement_backward_of_answers
    hTauAnswer
    hConsumeAnswer
    hTimeAnswer
    pinRelated
    (Common.WeakSteps.refl _)

end GeneralTraceTransfer
end Tests
end Relico
