import Relico.Common.WeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

universe u v w x y

/-!
## Finite observable traces agree across a weak bisimulation

Stage G row 9 (`G2d`), and the discharge of `docs/trusted-boundary.md` aims 8 and 9:

> 8. every permitted source execution has a corresponding target execution;
> 9. every target execution corresponds to a permitted source execution.

Both are proved here **once, over an abstract labelled transition system**, so no family pays for them
again. No statement below mentions DTR, Lingua Franca, reactors, tags, priorities or the translator, and the
only import is `Relico.Common.WeakExecution` — with `Relico.Common.WeakTransition` through it.

**Why this is not a re-proof of something the repository already has.** `F65` corrected the design's §4 by
recording that the multi-store family already carries a finite-execution development discharging these two
aims — `Correctness/GlobalMultiStorePayloadFiniteExecutionCorrespondence.lean`, `finite_forward` and
`finite_backward`. That development is real, and this module does not supersede it. It differs in two ways
that are visible in the statements rather than in the prose:

* Its `Steps` relation carries **no label list**, so it relates executions by their endpoints only. There
  is nothing in it to project, and therefore no trace agreement — the design calls it *a strict lock-step
  shape*. The theorems below relate executions **and** their observable traces.
* Its per-step correspondence is packaged as a **mirrored inductive** (`ForwardStepsCompatible`), because
  its one-step correspondence carries side conditions that vary along the execution. The weak transfer
  conditions here are uniform in the state, so a `∀`-quantified hypothesis suffices and no new inductive
  is introduced.

**Two implications, not one `Iff`.** The design's §4 settles this: the landed multi-store precedent states
aims 8 and 9 as a `_forward` / `_backward` pair, *"not one iff, but two implications each conditioned on
the other side's base correspondence"*, on the ground that *"a single symmetric statement would hide which
side's well-formedness is being assumed"*. §7 item 6 names the result `weakBisimulation_traceAgreement`;
that is the family name, and the pair below is what it denotes. Each theorem asks for exactly the one
transfer condition its own direction consumes, so a caller holding only one of them is not made to invent
the other.

**No weak-bisimulation structure is defined.** There is no generic one in the repository — the four
`*PhaseWeakBisimulation` declarations are all family-specific — and bundling the two transfer conditions
into one would force every caller to supply both. That is the same reason item 1a refused to invent a
program-rebuilding function: a definition earns its place from callers, not from tidiness.

**Scope, stated rather than discovered.** These are **finite** executions, `Common.WeakSteps`. Infinite
runs would need a coinductive treatment, which the paper does not give either and which nothing in this
repository needs. The design records that limit as a scope statement and not an owed theorem.

**What this does not do is discharge the aims for the general family — see F83.** The theorems are stated
over an arbitrary pair of systems and consume a transfer condition holding at **every** weak step. The
general family currently proves its transfer conditions for the `.timeAdvance` case only
(`generalTimeAdvance_forward_weak`, `generalTimeAdvance_backward_weak`); the `.consume` case is `#129`,
blocked on F76's repair decision. So the generic result lands now and the general-family instantiation
waits, which is a scheduling fact rather than a gap in either statement.
-/

/--
Two traces whose heads project to the same observable and whose tails already agree, agree.

The one arithmetic step of the induction below, factored out for a reason that is mechanical rather than
stylistic: inside an `induction` alternative the constructor's **implicit** fields are inaccessible, so a
proof written in place could not name the head label or the remaining labels in order to instantiate
`Common.observableProjection_cons_none` and `_cons_some`. Here every binder has a name, and the call site
supplies only the two projections — the two hypotheses between them pin all four label and list implicits.

Kept in this module rather than beside the three `@[simp]` lemmas it uses. Those three are single-system
facts about one projection; this one relates **two** projections over two different label types, which is a
trace-agreement notion, and it has exactly one consumer — immediately below. Promoting it to `Common/` would
widen the foundation for a single caller, which is the shape **F75** records as a defect.
-/
theorem observableProjection_cons_congr
    {SourceLabel : Type w}
    {TargetLabel : Type x}
    {Observable : Type y}
    (sourceProject :
      SourceLabel →
      Option Observable)
    (targetProject :
      TargetLabel →
      Option Observable)
    {sourceLabel : SourceLabel}
    {targetLabel : TargetLabel}
    {sourceRemaining : List SourceLabel}
    {targetRemaining : List TargetLabel}
    (hLabel :
      sourceProject sourceLabel =
        targetProject targetLabel)
    (hRemaining :
      Common.observableProjection
          sourceProject
          sourceRemaining =
        Common.observableProjection
          targetProject
          targetRemaining) :
    Common.observableProjection
        sourceProject
        (sourceLabel :: sourceRemaining) =
      Common.observableProjection
        targetProject
        (targetLabel :: targetRemaining) := by

  cases hSourceValue : sourceProject sourceLabel with

  | none =>
      have hTargetValue :
          targetProject targetLabel =
            none := by
        rw [← hLabel]
        exact hSourceValue

      rw [Common.observableProjection_cons_none
            sourceProject
            sourceLabel
            sourceRemaining
            hSourceValue,
          Common.observableProjection_cons_none
            targetProject
            targetLabel
            targetRemaining
            hTargetValue]

      exact hRemaining

  | some observable =>
      have hTargetValue :
          targetProject targetLabel =
            some observable := by
        rw [← hLabel]
        exact hSourceValue

      rw [Common.observableProjection_cons_some
            sourceProject
            sourceLabel
            observable
            sourceRemaining
            hSourceValue,
          Common.observableProjection_cons_some
            targetProject
            targetLabel
            observable
            targetRemaining
            hTargetValue,
          hRemaining]

/--
**Aim 8.** Every finite source execution has a corresponding target execution carrying the same observable
trace.

The hypothesis `hForward` is the forward transfer condition of a weak bisimulation, stated at the **weak**
step level rather than the single-step level. That is deliberate and it is what makes this corollary free:
the general family already proves its transfer condition in exactly this shape, for the labels it covers —
`generalTimeAdvance_forward_weak` — so instantiating this theorem requires no τ reasoning at the use site.
Every τ prefix and suffix is already absorbed inside `Common.WeakStep`; all that is left here is list
bookkeeping, which is why the proof is one induction with two short branches.

`related` is passed as a bare relation and the transfer condition as a `∀`-quantified hypothesis, rather
than bundled into a `WeakBisimulation` structure. There is no generic such structure in this repository —
the four `*PhaseWeakBisimulation` declarations are all family-specific — and bundling would force a caller
that holds only the forward direction to supply the backward one as well. The pairing with
`weakBisimulation_traceAgreement_backward` is what makes the two directions a bisimulation; neither theorem
needs to assume the other's half.

Note what is **not** assumed: that the two label types are the same, that the two τ predicates agree, or
that corresponding labels are equal. Only their *projections* have to agree, one pair at a time. The two
label lists do come out the same length, because the transfer condition answers each source weak step with
exactly one target weak step; what may differ in length is the observable trace, since a pair that projects
to `none` on both sides contributes nothing to either. That gap between the label list and the observable
trace is what makes this trace *agreement* rather than trace equality, and it is what lets a target system
with a different internal step structure still be judged correct.
-/
theorem weakBisimulation_traceAgreement_forward
    {SourceState : Type u}
    {TargetState : Type v}
    {SourceLabel : Type w}
    {TargetLabel : Type x}
    {Observable : Type y}
    {sourceStep :
      Common.LabeledTransition SourceState SourceLabel}
    {targetStep :
      Common.LabeledTransition TargetState TargetLabel}
    {sourceIsTau : SourceLabel → Prop}
    {targetIsTau : TargetLabel → Prop}
    (sourceProject :
      SourceLabel →
      Option Observable)
    (targetProject :
      TargetLabel →
      Option Observable)
    (related :
      SourceState →
      TargetState →
      Prop)
    (hForward :
      ∀ (source : SourceState)
        (target : TargetState)
        (label : SourceLabel)
        (nextSource : SourceState),
        related source target →
        Common.WeakStep
          sourceStep
          sourceIsTau
          source
          label
          nextSource →
        ∃ (targetLabel : TargetLabel)
          (nextTarget : TargetState),
          Common.WeakStep
              targetStep
              targetIsTau
              target
              targetLabel
              nextTarget ∧
            related nextSource nextTarget ∧
            sourceProject label =
              targetProject targetLabel)
    {source : SourceState}
    {target : TargetState}
    {labels : List SourceLabel}
    {nextSource : SourceState}
    (hRelated :
      related source target)
    (hSteps :
      Common.WeakSteps
        sourceStep
        sourceIsTau
        source
        labels
        nextSource) :
    ∃ (targetLabels : List TargetLabel)
      (nextTarget : TargetState),
      Common.WeakSteps
          targetStep
          targetIsTau
          target
          targetLabels
          nextTarget ∧
        related nextSource nextTarget ∧
        Common.observableProjection
            sourceProject
            labels =
          Common.observableProjection
            targetProject
            targetLabels := by

  -- `target` and the correspondence between it and `source` must travel through the induction, because
  -- each step lands at a *new* target state that only the transfer condition can name. Reverting them
  -- rather than writing `generalizing` keeps the motive explicit and matches what the multi-store
  -- precedent (`finite_forward`) spells out by hand as a `motive` carrying the correspondence as an
  -- antecedent.
  revert target

  induction hSteps with

  | refl state =>
      intro target hRelated

      exact
        ⟨[],
          target,
          Common.WeakSteps.refl target,
          hRelated,
          by simp⟩

  | cons headStep remainingSteps inductionHypothesis =>
      intro target hRelated

      -- A `cons` alternative binds EXPLICIT fields only, so `before`, `middle`, `after`, `label` and
      -- `remainingLabels` are all inaccessible here. The transfer condition therefore has to be applied
      -- with placeholders and let unification recover the indices from `hRelated` and `headStep`; an
      -- instantiated application cannot be written at all. The same constraint shaped item 3's rewrite.
      obtain
          ⟨targetLabel,
            targetMiddle,
            hTargetHead,
            hMiddleRelated,
            hLabelProjection⟩ :=
        hForward
          _
          target
          _
          _
          hRelated
          headStep

      -- No target argument here, and that is a measured constraint rather than a shorthand. `revert`
      -- preserves binder info, and `target` is implicit in this statement, so the reverted goal is
      -- `∀ {target}, related source target → …` and the induction hypothesis takes its target
      -- implicitly too. Passing `targetMiddle` positionally lands it in the `related` slot and fails
      -- with an application type mismatch; `hMiddleRelated` pins the same value by unification.
      obtain
          ⟨targetLabels,
            targetAfter,
            hTargetTail,
            hAfterRelated,
            hTailProjection⟩ :=
        inductionHypothesis
          hMiddleRelated

      exact
        ⟨targetLabel :: targetLabels,
          targetAfter,
          Common.WeakSteps.cons
            hTargetHead
            hTargetTail,
          hAfterRelated,
          observableProjection_cons_congr
            sourceProject
            targetProject
            hLabelProjection
            hTailProjection⟩

/--
**Aim 9.** Every finite target execution corresponds to a source execution carrying the same observable
trace.

Proved by instantiating `weakBisimulation_traceAgreement_forward` at the swapped systems, with `related`
flipped. That is sound precisely *because* the generic statement assumes nothing asymmetric about the two
sides: no shared label type, no shared τ predicate, no direction-specific well-formedness. The asymmetry in
this repository lives in the families' transfer conditions, not here, which is exactly why the design asks
for the two directions to be stated separately — *"a single symmetric statement would hide which side's
well-formedness is being assumed"* — while permitting one to be derived from the other at this level of
abstraction.

The instantiation is written positionally with fully annotated lambdas. The flip changes the *order* of the
transfer condition's first two arguments (the forward statement leads with its own source, which is this
statement's target), so the bridging lambda is not `hBackward` itself even though its body is. The result is
destructured and rebuilt component by component rather than passed to a single `exact`, so that each `related`
beta-reduction is checked against one goal component instead of against an `Exists` predicate as a function.

**This does not close aims 8 and 9 for the general family — see F83.** Both theorems consume a transfer
condition holding at *every* weak step. The general family proves the `.timeAdvance` case only; its
`.consume` case is task `#129`, blocked on the F76 selection divergence, whose repair is not a Lean
question. What lands here is the generic half, once and for all families.
-/
theorem weakBisimulation_traceAgreement_backward
    {SourceState : Type u}
    {TargetState : Type v}
    {SourceLabel : Type w}
    {TargetLabel : Type x}
    {Observable : Type y}
    {sourceStep :
      Common.LabeledTransition SourceState SourceLabel}
    {targetStep :
      Common.LabeledTransition TargetState TargetLabel}
    {sourceIsTau : SourceLabel → Prop}
    {targetIsTau : TargetLabel → Prop}
    (sourceProject :
      SourceLabel →
      Option Observable)
    (targetProject :
      TargetLabel →
      Option Observable)
    (related :
      SourceState →
      TargetState →
      Prop)
    (hBackward :
      ∀ (source : SourceState)
        (target : TargetState)
        (label : TargetLabel)
        (nextTarget : TargetState),
        related source target →
        Common.WeakStep
          targetStep
          targetIsTau
          target
          label
          nextTarget →
        ∃ (sourceLabel : SourceLabel)
          (nextSource : SourceState),
          Common.WeakStep
              sourceStep
              sourceIsTau
              source
              sourceLabel
              nextSource ∧
            related nextSource nextTarget ∧
            targetProject label =
              sourceProject sourceLabel)
    {source : SourceState}
    {target : TargetState}
    {labels : List TargetLabel}
    {nextTarget : TargetState}
    (hRelated :
      related source target)
    (hSteps :
      Common.WeakSteps
        targetStep
        targetIsTau
        target
        labels
        nextTarget) :
    ∃ (sourceLabels : List SourceLabel)
      (nextSource : SourceState),
      Common.WeakSteps
          sourceStep
          sourceIsTau
          source
          sourceLabels
          nextSource ∧
        related nextSource nextTarget ∧
        Common.observableProjection
            targetProject
            labels =
          Common.observableProjection
            sourceProject
            sourceLabels := by

  obtain
      ⟨resultLabels,
        resultSource,
        hResultSteps,
        hResultRelated,
        hResultProjection⟩ :=
    weakBisimulation_traceAgreement_forward
      targetProject
      sourceProject
      (fun
          (targetState : TargetState)
          (sourceState : SourceState) =>
        related sourceState targetState)
      (fun
          (targetState : TargetState)
          (sourceState : SourceState)
          (label : TargetLabel)
          (nextTargetState : TargetState) =>
        hBackward
          sourceState
          targetState
          label
          nextTargetState)
      hRelated
      hSteps

  exact
    ⟨resultLabels,
      resultSource,
      hResultSteps,
      hResultRelated,
      hResultProjection⟩

end Correctness
end Relico
