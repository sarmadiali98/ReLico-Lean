# C8: a General-specific label weak bisimulation interface

Status: **APPROVED 2026-09-02**

Decision: give the general family `Correctness.GeneralLabelWeakBisimulation`, a **six-field, label-level,
conditional** weak bisimulation interface, so that the claim *"the general family admits a weak bisimulation
structure"* is backed by a named declaration. Add `.forwardStep`, `.backwardStep`,
`.traceAgreement_forward` and `.traceAgreement_backward` so the structure is consumed rather than merely
declared.

Decision: **do not** copy the sibling families' thirteen-field `*PhaseWeakBisimulation` shape. It is
uninstantiable here.

Decision: this **overrides the anti-bundling ruling only for the weak bisimulation interface**. The
anti-bundling ruling continues to hold for the end-to-end trace composition.

## Context

`docs/decisions/0043-forward-instant-block-weak-step.md` rejected an end-to-end bisimulation bundle on three
grounds: it adds no theorem content, `Relico/Correctness/WeakBisimulationTrace.lean` records that bundling
*"would force a caller that holds only the forward direction to supply the backward one as well"*, and a
general-family bundle would carry four independent residues in one signature.

A six-field structure carrying three residues is, structurally, the same kind of object. So this decision is a
genuine conflict with 0043 and is recorded as one rather than being presented as a natural continuation.

What changed is the requirement, not the reasoning. The paper must be able to **state and defend** that the
general family admits a weak bisimulation structure. A pair of transfer conditions supports that claim but does
not *name* it: a reader has to assemble them, and a referee has no single declaration to point at. The
acceptance ledger's C8 row says the same thing in the project's own vocabulary, quoting F83 — C8 *"cannot exist
before `#129` closes"* — and adding: **"Without this, Stage G's headline claim is generic-only."** `#129`
closed with C7, so C8 became reachable for the first time.

The general family was also the **only one of five** without such a structure. The other four each carry one.

## Why the thirteen-field phase shape was rejected

Measured, not assumed. All four sibling structures have exactly thirteen fields with identical names — verified
by extracting the field lists and diffing them pairwise, zero differences. Five forward, eight backward.

Those fields are not forward/backward × *label*. They are forward/backward × **phase**. The siblings' target
state is an inductive carrying mid-dispatch phases:

```
inductive DetailedMultiStoreState (messageReactions) where
  | stable        : LF.StoreState → …
  | afterTime     (before) (selectedAction) (selectedReaction) (after) (hDispatch) → …
  | dispatchReady (before) (selectedAction) (selectedReaction) (after) (hDispatch) → …
```

(`Relico/LF/DetailedMultiStoreSemantics.lean:149`.) Names like `forwardConsumeAfterTimeMatch`,
`forwardConsumeReadyMatch` and `backwardMicrostepSameTimeMatch` are cases of that indexing, each carrying a
dispatch proof *inside the state*.

**`LF.GeneralRuntimeState` has no phases.** It is flat — a tag, a reactor store, a pending queue — and there is
no general counterpart of the siblings' `*ForwardPhaseCompatible` (grep returns one for each of the other four
and none for this family). So eight of the thirteen fields would name phases that do not exist. Copying the
shape would require adding phase-indexed state to the general semantics: a change to the **semantics**, not to
a correctness interface, and outside every standing constraint.

## Why six label-level fields were chosen

`DTR.GeneralLabel` and `LF.GeneralLabel` each have three constructors, so one field per label per direction is
six, and the structure is exhaustive by construction: a new label on either side appears as a missing case in
`.forwardStep` / `.backwardStep` rather than falling through a default.

| field | inhabited by | residue |
|---|---|---|
| `forwardTauMatch` | `generalTauSteps_forward` | none |
| `forwardConsumeMatch` | `generalConsume_forward_weak_of_fireRepresentative` | α-representative package |
| `forwardTimeAdvanceMatch` | `generalTimeAdvance_forward_weak` | none |
| `backwardTauMatch` | — (premise-only) | `hTauAnswer` |
| `backwardConsumeMatch` | `generalConsume_backward_weakStep_of_takeRepresentative` | `hName` |
| `backwardTimeAdvanceMatch` | `generalTimeAdvance_backward_weak` | none |

Two shape details are load-bearing rather than stylistic. `backwardTauMatch` answers with a
`Common.WeakStep` and not a `Common.TauSteps`, so a target `microstepAdvance` — which has no source
counterpart — can be answered by *zero* source steps. And it requires the answering source label to be
internal; without that a target τ step could be answered by a *visible* source label and the observable
agreement would silently break.

Both dispatch theorems split on the **label**, not the step, which is why the target's five τ constructors
against the source's three are invisible to them.

## Why the residues remain explicit premises

Three fields carry residues, and each is a **measured non-derivability** rather than an unfinished proof:

- **`forwardConsumeMatch`** — the α-representative package. Which α-equivalent representative the target's
  `fire` premises hold at is the frozen α′ question (decision 0042's setting).
- **`backwardConsumeMatch`** — `hName`, the per-step actor agreement. `DTR.GeneralActorSelection.selectedActor`
  is a *function* of the source configuration alone, and `readyActors` / `earliestDueArrival` never mention the
  target program, its queue or its fire order (F76). `selectedActor_unique` sharpens the obstruction by proving
  the source schedule forced.
- **`backwardTauMatch`** — `hTauAnswer`. Five target τ constructors against three source ones;
  `microstepAdvance` has no source counterpart; and `LF.GeneralStepModulo.weakStep_of_raw`'s docstring records
  that the converse is *deliberately* absent, because a modulo weak step may switch representatives between
  segments.

Hiding these inside a definition would make the structure look stronger than the fact it records. The
docstring therefore states outright that it is **not premise-free**, and an unconditional witness is
impossible while any field carries a residue — so, like three of the four siblings, the structure is consumed
as a hypothesis rather than constructed.

The non-vacuity is nevertheless demonstrated rather than asserted:
`Correctness.generalSourceReadiness_of_targetEvent` shows the backward package is not empty, and a pin in
`Relico/Tests/GeneralLabelWeakBisimulation.lean` constructs the structure from six hypotheses of the field
shapes, so the six field types are jointly satisfiable.

## What C8 buys, stated honestly

Its six fields are inhabited by theorems that already existed, so as *theorem content* it adds nothing. What
it adds is:

1. **a single citable name** for the family's weak bisimulation claim;
2. **trace agreement as a consequence** — `.traceAgreement_forward` and `.traceAgreement_backward` derive both
   observable-trace rows from the interface **with no further premises**, and no residue appears in either
   statement. This is the part that makes the structure worth more than citing the two transfer conditions;
3. **an exhaustiveness check**, one field per label per direction;
4. **parity with the four siblings**, which the ledger names as the difference between a general claim and a
   generic-only one.

It also avoids a defect the siblings have. Three of the four sibling interfaces are never inhabited *and*
their `.forwardStep` / `.backwardStep` theorems are never applied anywhere in the tree — the F75 pattern of a
declaration with no caller. This family's dispatch theorems and both trace consequences are exercised by pins.

## Scope

- Applies to the weak bisimulation **interface** only. **Anti-bundling still stands for the end-to-end trace
  composition**: that would add no theorem content and combine four residues in one signature, and 0043's
  reasoning is unchanged.
- No generic cross-family bundle. The structure is general-family specific, as all four siblings are
  family-specific.
- `hConsumeAnswer` unchanged; `GeneralInstantBlock` theorem shapes unchanged; decision 0043's Option A intact;
  α and F27 decisions untouched; no runtime fields; no modulo→raw lemma.
- Name: `GeneralLabelWeakBisimulation`. `GeneralWeakBisimulation` was avoided because
  `Relico/Correctness/GeneralWeakBisimulation.lean` already exists as a module and holds the consume cores;
  a structure of that name would collide confusingly. "Phase" is deliberately absent from the name because
  there are no phases.

## Rejected alternatives

- **(a) Copy the thirteen-field phase shape.** Uninstantiable: eight fields name phases the family does not
  have. Would require changing the general semantics.
- **(b) Do not build C8; state the "generic-only" caveat in the paper instead.** Legitimate and costs nothing,
  but leaves the paper unable to make the claim it needs, and leaves the general family the only one of five
  without a named structure.
- **(c) Build it with the residues hidden inside the definition**, so the structure reads as premise-free.
  Rejected: it would misrepresent the fact recorded. The residues are the honest boundary of the result.
- **(d) Wait for the residues to be discharged first.** Rejected: two of the three are *provably* not
  derivable from the available data, so this is not a matter of sequencing.

## Consequences

- `docs/STAGE_G_FINDINGS.md`'s *C7 contribution* section item 3 is rewritten to cite the structure, with the
  label-versus-phase measurement recorded and the earlier citation noted as superseded rather than silently
  replaced.
- The paper should cite `GeneralLabelWeakBisimulation` and its two `traceAgreement_*` consequences, and must
  still disclose the three residues and decision 0042's partial quotient.
- No Lean work is planned for C7 or C8.
