/-
! # Pins for the general family's label weak bisimulation interface

`Correctness.GeneralLabelWeakBisimulation` is a `Prop` structure with six universally-quantified fields, so no
`rfl` or `decide` can pin it. What these pins establish is the two properties that could silently break:

* **the interface is inhabitable** — its six field types are not accidentally contradictory, and each is
  satisfiable in the shape an existing theorem produces;
* **its four consumers apply** — `.forwardStep`, `.backwardStep`, `.traceAgreement_forward` and
  `.traceAgreement_backward` can actually be used against it.

The second matters more than it looks. Three sibling families carry a `*PhaseWeakBisimulation` whose
`.forwardStep` / `.backwardStep` take the structure as a hypothesis and are **never applied anywhere in the
tree**. That is the F75 pattern, and these pins are what keep this family out of it.

## What is deliberately not pinned

The interface is **not** inhabited with real content, and cannot be: three of its six fields carry residues
(the forward α-representative package, `hName`, `hTauAnswer`), each a measured non-derivability. The pins below
take the interface as a **hypothesis** exactly as its own consumers do. Constructing a fake witness to make a
pin look stronger would assert the frozen α′ question was settled — which is the one thing the residue
documentation exists to prevent.
-/
import Relico.Correctness.GeneralLabelWeakBisimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GeneralLabelWeakBisimulation

open Relico.Correctness

/- Test 1: the structure and all six fields exist and are addressable by name. A field rename or removal
   breaks this immediately, which is what makes it worth stating rather than assuming. -/
example : True := by
  have _ := @Correctness.GeneralLabelWeakBisimulation
  have _ := @Correctness.GeneralLabelWeakBisimulation.forwardTauMatch
  have _ := @Correctness.GeneralLabelWeakBisimulation.forwardConsumeMatch
  have _ := @Correctness.GeneralLabelWeakBisimulation.forwardTimeAdvanceMatch
  have _ := @Correctness.GeneralLabelWeakBisimulation.backwardTauMatch
  have _ := @Correctness.GeneralLabelWeakBisimulation.backwardConsumeMatch
  have _ := @Correctness.GeneralLabelWeakBisimulation.backwardTimeAdvanceMatch
  trivial

/- Test 2: `.forwardStep` applies to an arbitrary source weak step, given the interface.

   This is the pin the three sibling interfaces do not have: their dispatch theorems exist but are never
   applied. Here the application is exercised, so a drift between a field's shape and what the dispatch expects
   fails at build time. -/
example
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hBisimulation :
      Correctness.GeneralLabelWeakBisimulation
        model
        program)
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {label : DTR.GeneralLabel}
    (hRelated :
      Correctness.GeneralTraceRelated
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
        Correctness.GeneralTraceRelated
          model
          config'
          state' ∧
        Correctness.GeneralObservable.ofSourceLabel label =
          Correctness.GeneralObservable.ofTargetLabel targetLabel :=
  hBisimulation.forwardStep
    hRelated
    hStep

/- Test 3: `.backwardStep` applies to an arbitrary target weak step of the quotient system. -/
example
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hBisimulation :
      Correctness.GeneralLabelWeakBisimulation
        model
        program)
    {config : DTR.GeneralRuntimeConfiguration}
    {state state' : LF.GeneralRuntimeState}
    {label : LF.GeneralLabel}
    (hRelated :
      Correctness.GeneralTraceRelated
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
        Correctness.GeneralTraceRelated
          model
          config'
          state' ∧
        Correctness.GeneralObservable.ofTargetLabel label =
          Correctness.GeneralObservable.ofSourceLabel sourceLabel :=
  hBisimulation.backwardStep
    hRelated
    hStep

/- Test 4: both trace-agreement consequences follow from the interface alone, over the EMPTY execution.

   The empty label list is used because the interest is in applicability, not in the trace content — the
   non-empty trace agreement is already pinned in `Relico/Tests/GeneralObservable.lean` test 10, with different
   τ counts on the two sides. What this adds is that **neither consequence needs a premise beyond the
   interface**, which is the whole reason C8 was worth building rather than citing the two transfer conditions
   directly. -/
example
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hBisimulation :
      Correctness.GeneralLabelWeakBisimulation
        model
        program)
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hRelated :
      Correctness.GeneralTraceRelated
        model
        config
        state) :
    (∃ (targetLabels : List LF.GeneralLabel)
       (state' : LF.GeneralRuntimeState),
       Common.WeakSteps
           (LF.GeneralStepModulo program)
           LF.GeneralLabel.isTau
           state
           targetLabels
           state' ∧
         Correctness.GeneralTraceRelated
           model
           config
           state' ∧
         Common.observableProjection
             Correctness.GeneralObservable.ofSourceLabel
             [] =
           Common.observableProjection
             Correctness.GeneralObservable.ofTargetLabel
             targetLabels) ∧
      (∃ (sourceLabels : List DTR.GeneralLabel)
         (config' : DTR.GeneralRuntimeConfiguration),
         Common.WeakSteps
             (DTR.GeneralStep model)
             DTR.GeneralLabel.isTau
             config
             sourceLabels
             config' ∧
           Correctness.GeneralTraceRelated
             model
             config'
             state ∧
           Common.observableProjection
               Correctness.GeneralObservable.ofTargetLabel
               [] =
             Common.observableProjection
               Correctness.GeneralObservable.ofSourceLabel
               sourceLabels) :=
  ⟨hBisimulation.traceAgreement_forward
     hRelated
     (Common.WeakSteps.refl _),
   hBisimulation.traceAgreement_backward
     hRelated
     (Common.WeakSteps.refl _)⟩

/- Test 5: the interface is INHABITABLE — its six field types are jointly satisfiable.

   Built by supplying each field from a hypothesis of that field's own shape, which is what a caller holding
   the three residues would do. This is the pin that would catch a field whose type is accidentally
   contradictory, or whose shape no theorem can produce: such a field would make the structure uninhabitable
   while every theorem mentioning it still elaborated. -/
example
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (forwardTau :
      ∀ (config config' : DTR.GeneralRuntimeConfiguration)
        (state : LF.GeneralRuntimeState)
        (label : DTR.GeneralLabel),
        Correctness.GeneralTraceRelated model config state →
        DTR.GeneralLabel.isTau label →
        Common.WeakStep (DTR.GeneralStep model) DTR.GeneralLabel.isTau
          config label config' →
        ∃ state' : LF.GeneralRuntimeState,
          Common.WeakStep (LF.GeneralStepModulo program) LF.GeneralLabel.isTau
              state LF.GeneralLabel.tau state' ∧
            Correctness.GeneralTraceRelated model config' state')
    (forwardConsume :
      ∀ (config config' : DTR.GeneralRuntimeConfiguration)
        (state : LF.GeneralRuntimeState)
        (receiver : ActorName)
        (message : DTR.GeneralMessage),
        Correctness.GeneralTraceRelated model config state →
        Common.WeakStep (DTR.GeneralStep model) DTR.GeneralLabel.isTau
          config (DTR.GeneralLabel.consume receiver message) config' →
        ∃ (state' : LF.GeneralRuntimeState) (event : LF.GeneralPendingEvent),
          Common.WeakStep (LF.GeneralStepModulo program) LF.GeneralLabel.isTau
              state (LF.GeneralLabel.consume event.target event.kind) state' ∧
            event.target = receiver ∧
            Correctness.GeneralTraceRelated model config' state')
    (forwardTime :
      ∀ (config config' : DTR.GeneralRuntimeConfiguration)
        (state : LF.GeneralRuntimeState)
        (before after : LogicalTime),
        Correctness.GeneralTraceRelated model config state →
        Common.WeakStep (DTR.GeneralStep model) DTR.GeneralLabel.isTau
          config (DTR.GeneralLabel.timeAdvance before after) config' →
        ∃ state' : LF.GeneralRuntimeState,
          Common.WeakStep (LF.GeneralStepModulo program) LF.GeneralLabel.isTau
              state (LF.GeneralLabel.timeAdvance before after) state' ∧
            Correctness.GeneralTraceRelated model config' state')
    (backwardTau :
      ∀ (config : DTR.GeneralRuntimeConfiguration)
        (state state' : LF.GeneralRuntimeState)
        (label : LF.GeneralLabel),
        Correctness.GeneralTraceRelated model config state →
        LF.GeneralLabel.isTau label →
        Common.WeakStep (LF.GeneralStepModulo program) LF.GeneralLabel.isTau
          state label state' →
        ∃ (sourceLabel : DTR.GeneralLabel)
          (config' : DTR.GeneralRuntimeConfiguration),
          DTR.GeneralLabel.isTau sourceLabel ∧
            Common.WeakStep (DTR.GeneralStep model) DTR.GeneralLabel.isTau
              config sourceLabel config' ∧
            Correctness.GeneralTraceRelated model config' state')
    (backwardConsume :
      ∀ (config : DTR.GeneralRuntimeConfiguration)
        (state state' : LF.GeneralRuntimeState)
        (target : ActorName)
        (kind : LF.GeneralEventKind),
        Correctness.GeneralTraceRelated model config state →
        Common.WeakStep (LF.GeneralStepModulo program) LF.GeneralLabel.isTau
          state (LF.GeneralLabel.consume target kind) state' →
        ∃ (message : DTR.GeneralMessage)
          (config' : DTR.GeneralRuntimeConfiguration),
          Common.WeakStep (DTR.GeneralStep model) DTR.GeneralLabel.isTau
              config (DTR.GeneralLabel.consume target message) config' ∧
            Correctness.GeneralTraceRelated model config' state')
    (backwardTime :
      ∀ (config : DTR.GeneralRuntimeConfiguration)
        (state state' : LF.GeneralRuntimeState)
        (before after : LogicalTime),
        Correctness.GeneralTraceRelated model config state →
        Common.WeakStep (LF.GeneralStepModulo program) LF.GeneralLabel.isTau
          state (LF.GeneralLabel.timeAdvance before after) state' →
        ∃ config' : DTR.GeneralRuntimeConfiguration,
          Common.WeakStep (DTR.GeneralStep model) DTR.GeneralLabel.isTau
              config (DTR.GeneralLabel.timeAdvance before after) config' ∧
            Correctness.GeneralTraceRelated model config' state') :
    Correctness.GeneralLabelWeakBisimulation
      model
      program :=
  {
    forwardTauMatch := forwardTau
    forwardConsumeMatch := forwardConsume
    forwardTimeAdvanceMatch := forwardTime
    backwardTauMatch := backwardTau
    backwardConsumeMatch := backwardConsume
    backwardTimeAdvanceMatch := backwardTime
  }

end GeneralLabelWeakBisimulation
end Tests
end Relico
