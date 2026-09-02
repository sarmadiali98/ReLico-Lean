# General-family correctness claim

What the general family's verified translation asserts, and how a reader re-derives each assertion
without trusting this document.

## How to read this file

Every row cites an **instrument**: a Lean declaration, a gate marker, a shell command, or a commit
SHA. The instrument is the claim's evidence, and it is checkable now; this file is not a status
report and carries no status words, no dates and no progress notes. A row whose instrument does not
exist is a defect in the row, not a task; delete it rather than annotate it.

**There are no measured totals here.** Counts are measurements and measurements rot: the gate scripts
assert their own totals internally (`EXPECTED_PRINTER_ASSERTIONS` in
`frontend/check-general-lean.sh`), so the gate is the authority and this file cites the gate rather
than repeating what it prints. A figure copied into prose is a second source of truth that nothing
checks.

**Residues are part of the claim.** Where a row's theorem carries an undischarged premise, the
`Residues / scope` column names it. Reading a row without that column overstates it.

Nothing here restates the reasoning behind a claim. `docs/STAGE_G_FINDINGS.md`'s *"The C7
contribution"* section carries the argument; the decision records carry the choices; this file carries
only the mapping from claim to instrument.

## What the project undertakes to prove

`docs/trusted-boundary.md:28-38` is authoritative for the aims. The general family's rows below are
grouped under the three it owns, quoted there as aims 7, 8 and 9: designer-specified priorities are
preserved; every permitted source execution has a corresponding target execution; every target
execution corresponds to a permitted source execution.

## Aim 7: designer-specified priorities are preserved

| # | Claim | Instrument | Kind | Residues / scope |
|---|---|---|---|---|
| 1 | The translator never emits a reaction carrying an LF priority; the offence is impossible, not merely refused | `Relico.Translation.compileGeneralModel_reactionPrioritiesAbsent` · `0bf807c` | decl · sha | none |
| 2 | The pre-guard assembly already satisfies the clause, so the claim is independent of the guard's verdict | `Relico.Translation.assembleGeneralProgram_reactionPrioritiesAbsent` · `0bf807c` | decl · sha | none |
| 3 | A populated reaction priority is a well-formedness violation with its own refusal | `Relico.LF.GeneralProgram.reactionPrioritiesAbsent` | decl | guard-relative |
| 4 | Priority order is observable in a real `lfc` run, not only in emitted text | `GENERAL_LF_PRIORITY_WITNESS_OK` | marker | requires `lfc` 0.11.0 |

Row 1's proof is deliberately the composition of the per-reaction equations and **not** an extraction
from the guard's decision; row 2 exists so that substituting the weaker proof stays visible. F84 and
its appended discharge note record why.

## Aim 8: every permitted source execution has a corresponding target execution

| # | Claim | Instrument | Kind | Residues / scope |
|---|---|---|---|---|
| 5 | The state relation pairing source configurations with target states | `Relico.Correctness.GeneralStateCorrespondence` · `a7b42c9` | decl · sha | n/a |
| 6 | Every source internal (τ) segment is answered by a target internal segment | `Relico.Correctness.generalTauSteps_forward` · `f4f1255` | decl · sha | none beyond accepted-program facts |
| 7 | A source instant block is answered by a target execution of the quotient system, with a per-reactor match | `Relico.Correctness.generalInstantBlock_forward` · `047a5ef` | decl · sha | per-consume α-representative package |
| 8 | The same, against the source block predicate | `Relico.Correctness.generalInstantBlock_forward_of_source` · `047a5ef` | decl · sha | as row 7; endpoint conditions not carried into the conclusion |
| 9 | Source quiescence and idleness transport to the target | `Relico.Correctness.generalPendingFuture_of_quiescent`, `Relico.Correctness.generalReactorIdle_of_actorIdle` · `0226689` | decl · sha | none |
| 10 | Forward observable-trace agreement | `Relico.Correctness.GeneralLabelWeakBisimulation.traceAgreement_forward` · `728cc21` | decl · sha | inherited from the interface (row 15) |

## Aim 9: every target execution corresponds to a permitted source execution

| # | Claim | Instrument | Kind | Residues / scope |
|---|---|---|---|---|
| 11 | A target fire is answered by a source consume at a supplied take representative | `Relico.Correctness.generalConsume_backward_weak_of_takeRepresentative` · `50283e5` | decl · sha | per-step actor agreement (`hName`) |
| 12 | A target instant block is answered by a source execution satisfying the **whole** source block predicate | `Relico.Correctness.generalInstantBlock_backward_of_target` · `a9c5609` | decl · sha | `hName` per occurrence; target representative package |
| 13 | The source is never stuck while the target has instant work, and the actor it selects has target work | `Relico.Correctness.generalSourceReadiness_of_targetEvent` · `f485129` | decl · sha | none |
| 14 | Backward observable-trace agreement | `Relico.Correctness.GeneralLabelWeakBisimulation.traceAgreement_backward` · `728cc21` | decl · sha | inherited from the interface (row 15) |

Row 12 concludes more than its forward counterpart (row 8). That asymmetry is intentional and is
recorded in `docs/decisions/0043-forward-instant-block-weak-step.md`.

## The named weak bisimulation object

| # | Claim | Instrument | Kind | Residues / scope |
|---|---|---|---|---|
| 15 | The general family admits a weak bisimulation structure | `Relico.Correctness.GeneralLabelWeakBisimulation` · `728cc21` | decl · sha | **3 of 6 fields carry residues**; not premise-free |
| 16 | Any source weak step is answered, and any target weak step is answered | `.forwardStep`, `.backwardStep` · `728cc21` | decl · sha | as row 15 |

Row 15 is **label-level**, six fields, one per label per direction. It is not the thirteen-field
phase-indexed shape the sibling families carry: `Relico.LF.GeneralRuntimeState` has no phase state, so
eight of those fields are uninstantiable here. `docs/decisions/0044-c8-general-label-weak-bisimulation.md`
records the measurement.

The three residues, named because a row read without them overstates the claim: the forward
`.consume` α-representative package; the backward `.consume` per-step actor agreement `hName`; the
backward τ answer `hTauAnswer`. Each is a measured non-derivability, not an unfinished proof.

## The setting the claims are stated over

| # | Claim | Instrument | Kind | Residues / scope |
|---|---|---|---|---|
| 17 | Correspondence is stated up to a **partial** within-tag quotient, free permutation among distinct reactors at one tag, order-preserving within one reactor | `Relico.LF.generalStateAlphaEquiv`, `Relico.LF.GeneralStepModulo` · `f026114` · `docs/decisions/0042-within-tag-partial-quotient.md` · `b13af48` | decl · sha | this is **not** the paper's Definition 1 verbatim |
| 18 | The observable alphabet: a consume observes the receiver only; a time advance observes both endpoints | `Relico.Correctness.GeneralObservable` · `d84638c` | decl · sha | payload and event kind are erased, by F78 and by compiler-independence |
| 19 | The alphabet drops exactly the internal labels and no visible one | `Relico.Correctness.GeneralObservable.ofSourceLabel_eq_none_iff_isTau`, `.ofTargetLabel_eq_none_iff_isTau` · `d84638c` | decl · sha | none |
| 20 | The accepted source fragment | `docs/supported-fragment-general.md` · `7c64932` | doc · sha | n/a |

## Mechanised-artefact integrity

| # | Claim | Instrument | Kind | Residues / scope |
|---|---|---|---|---|
| 21 | Everything compiles | `PATH="$HOME/.elan/bin:$PATH" lake build` | command | exit 0 |
| 22 | No `sorry`, and no project-specific axiom | `#print axioms <declaration>` on any row above | command | expect only `propext`, `Classical.choice`, `Quot.sound` |
| 23 | The Lean and printer gate passes, at the assertion total the script itself pins | `bash frontend/check-general-lean.sh` → `GENERAL_LEAN_GATE_OK`, `GENERAL_LF_PRINTER_TESTS_OK`; total pinned by `EXPECTED_PRINTER_ASSERTIONS` in that script | command · marker | the script is the authority for its own totals |
| 24 | The real Lingua Franca compiler accepts the emitted programs | `LFC=<path> bash frontend/check-general-lf-target.sh` → `GENERAL_LF_TARGET_OK` | command · marker | requires `lfc` 0.11.0 |
| 25 | The benchmark registry is internally consistent | `bash tools/relico_bench.sh --validate-registry` → `REGISTRY_VALID=yes` | command · marker | none |

## What is deliberately not claimed

Each of these is a recorded decision, not an omission.

- **No forward instant-block spine.** The forward result is a weak-step theorem; internal τ
  decomposition stays hidden inside weak transitions. `docs/decisions/0043-forward-instant-block-weak-step.md`.
- **No matching of an arbitrary admissible source order.** The source's `take` admits any equally-early
  message of a bag, and nothing derives that the target's single forced order is among them. F27,
  classification C.
- **Not the paper's `Theorem 1` verbatim.** The claims hold over the partial quotient of row 17. An
  unqualified "we mechanised Theorem 1" is deflatable in one sentence.
- **No premise-free bisimulation.** Row 15 is a conditional interface; three of its fields carry the
  residues named above.
- **No end-to-end bisimulation bundle.** The two trace rows are cited as a pair; bundling adds no
  theorem content. `docs/decisions/0043`, reaffirmed in `0044`.

## Where the reasoning lives

This file maps claims to instruments and nothing else. For why each claim has the shape it does:

- `docs/STAGE_G_FINDINGS.md`, *"The C7 contribution"*, the argument, the three residues with their
  measurements, the invariant layers.
- `docs/decisions/0042-within-tag-partial-quotient.md`, why the quotient is partial.
- `docs/decisions/0043-forward-instant-block-weak-step.md`, why forward is a weak-step theorem.
- `docs/decisions/0044-c8-general-label-weak-bisimulation.md`, why the structure is label-level.
- `docs/trusted-boundary.md`; the aims these rows are grouped under.
- `docs/supported-fragment-general.md`, what the translator accepts and refuses.
