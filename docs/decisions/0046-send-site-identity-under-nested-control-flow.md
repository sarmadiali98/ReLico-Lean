# Stage H: send-site identity under nested control flow

Status: **APPROVED 2026-09-03**

Decision: **Design I.** A send site is identified by its **path** through a possibly nested body,
`Translation.SendSite.index : List Nat` replacing `Nat`, and the operational semantics **steps into** a nested
body rather than splicing it into the continuation.

Decision: the DTR AST gains `GeneralStmt.ifThenElse` and **nothing else**. `DTR.GeneralStmt.send` is unchanged,
and `DTR.GeneralModel.wellFormed` keeps its five clauses.

Decision: **Design III is rejected**, and it is recorded here in full rather than summarised, because it is the
cheaper design and a later contributor is entitled to see what was weighed.

Decision: **this record authorizes architecture only, not implementation.** No Lean file changes on the strength
of it. It fixes where a send site's identity comes from once statement bodies stop being flat, so that the
implementation that follows has a settled answer to the one question whose wrong answer is invisible to every
gate.

## 1. Context

### The current model

`Translation.SendSite` is `{ body : GeneralBodyKey, index : Nat }`. The `index` is the statement's position in its
body's statement list, counted from zero **over all statements and not only over the sends**. The module
docstring states the principle behind that choice:

> a position is an address, it can be checked against the source by counting statements, whereas a count of
> preceding sends is a number that only the traversal that produced it can explain.

`GeneralBody` is `List DTR.GeneralStmt`, and `docs/STAGE_B_DESIGN.md` section 7 records that the flatness is
deliberate and that this is the stage which ends it: *"statement bodies stay `List GeneralStmt`, flat, and stage H
changes the type on purpose."*

### Why nested control flow breaks it

A statement inside an `if` branch has no position in the enclosing list, because the branch is a separate list.
There is no `Nat` to store.

This is not avoidable by restricting the fragment to branches without sends. Measured over the 25 candidate
benchmarks of the Rebeca corpus: **44 of 94 branch bodies contain a send**, 18 of them in `smarthome` alone. A
no-sends-in-branches rule would exclude most of the corpus this stage exists to admit.

### Why it is a correctness issue and not only an implementation issue

Three traversals walk a body in lockstep: `compileGeneralBody`, `externalSendsFromIndex` and
`selfSendsFromIndex`. `compileGeneralBody`'s docstring states the invariant and names the failure mode:

> both advance the index once per statement regardless of what the statement is, so a send's position here and
> its position there are the same number. If one of them ever skips, **ports are assigned to the wrong sends and
> every downstream check still passes**.

A misaligned site yields a well formed LF program in which a send is wired to the wrong port. `lfc` accepts it,
the printer gate accepts it, the benchmark registry validates, and the correctness theorems still hold, of the
wrong program. **This is the only failure mode in the project that is invisible to every existing gate**, which
is why the identity scheme is a decision record rather than an implementation detail.

### What depends on the current scheme

| invariant | depends on | site |
|---|---|---|
| monotonicity | `index <= send.site.index` for a walk from `index` | `site_index_ge_of_mem_externalSendsFromIndex` |
| site injectivity | proved **because** the index strictly increases | `externalSendsFromIndex_site_injective` |
| correspondence site conjunct | `source.drop k` paired with `index + k` | `GeneralContinuationCompiles`, consumed at `GeneralConnectionSourceUniqueness.lean:1219`, `:1231`, `:1416`, `:1428` |
| port name ordinals | a **total order** on one class's sites | `numberExternalSends`, `generalSiteSuffixFor` |
| three traversal lockstep | one index step per statement | the three functions above |

The third is the deep one. `GeneralContinuationCompiles` is a field of `GeneralActorCorresponds`, a field of
`GeneralStateCorrespondence`, the first conjunct of `GeneralTraceRelated`, so **every C7 theorem and all six C8
fields are stated over it**. It has 22 mention sites across 5 modules, and its own docstring records the
difficulty: `activeBody` *"is a *suffix* of a declared body whose"* `bodyKey` and index are existential.

### One bound on the blast radius

Generated port and action names do **not** contain the index. `generalSiteSuffixFor` emits the site's 1-based
ordinal among its `(known rebec, message)` pair, over `externalSendsOfClass`'s canonical order. Any design that
preserves canonical traversal order therefore preserves every emitted name, so `EXPECTED_PRINTER_ASSERTIONS` and
the `lfc` gate verdict do not move. The corresponding obligation: the redesign must still supply a total order on
one class's sites, even once the index stops being a `Nat`.

## 2. Options considered

A third option, **pre-flattening before site assignment**, was analysed and is not viable. Flatten for numbering
only, and `activeBody` at runtime is a suffix of one branch rather than of the flattened list, so the flat index
addresses nothing the runtime can reach; recovering it needs a tree-position-to-flat-index map, which is Design I
with an extra indirection. Eliminate nesting in the elaborator, and it fails outright: a data dependent branch
cannot become a straight line without guarded statements, itself a new construct with its own semantics. (This is
precisely why `for` **can** be lowered to `while` and `if` cannot be lowered to anything.)

### Design I: path-based identifiers, step-into semantics

- **AST**: `SendSite` is a `Translation` type the DTR AST never mentions, so the only AST change is `ifThenElse`
  itself. `GeneralStmt.send` untouched.
- **Translation**: both traversals accumulate a path instead of incrementing; lockstep is preserved in shape,
  each still advancing once per statement within a level. Canonical order becomes lexicographic, but
  `externalSendsOfClass` can remain a list numbered by list position, so `numberExternalSends` is unchanged.
- **Correspondence**: the hardest hit. `source.drop k` is meaningless on a tree, so the site conjunct is restated
  as a path plus residual, or as a zipper. The definition changes under a fixed name, so theorem **statements**
  survive and **proofs** do not.
- **Proof impact**: monotonicity has no analogue and is replaced by a prefix extension lemma; injectivity becomes
  structurally easier but its existing proof is discarded rather than adapted.
- **Design principles**: preserves source position as address, keeps the AST minimal, adds no `wellFormed`
  clause.
- **Advantages**: no recorded commitment is retired; every claim's text is unchanged; C8's shape survives
  untouched, since its six fields are indexed by **label** and `if` is a new internal **statement**, not a new
  label.
- **Disadvantages**: heaviest proof burden of the two; a continuation stack on `GeneralActorRuntime`, which every
  correctness module quantifies over; more internal step rules (enter, exit, branch decision).

### Design III: stable elaborator-assigned identifiers, in-place reduction

- **AST**: the only option that changes it. `GeneralStmt.send` gains a site field or a parallel identifier.
- **Translation**: simplest of the two. The statement carries its own identifier, no index threading, and **the
  three traversal lockstep invariant disappears entirely**, removing the silent misrouting failure mode at its
  root instead of re-proving around it.
- **Correspondence**: also simplest. The `activeBody`-is-a-suffix obstruction dissolves, because the running
  statement carries its own site.
- **Proof impact**: injectivity trivial by construction, monotonicity not needed. The largest saving available.
- **Design principles**: **violates** source position as address, since an elaborator-assigned identifier is
  exactly a number only its producing traversal can explain, and unlike a position cannot be checked against the
  source at all. Weakens AST minimality. Requires a **sixth `wellFormed` clause** for identifier uniqueness.
- **Advantages**: least proof work, least semantic machinery, eliminates a whole bug class.
- **Disadvantages**: `DecidableEq` on `GeneralStmt` then distinguishes two structurally identical sends, so two
  models differing only in identifiers are different models and every hand built test AST must supply them; and
  the sixth clause reopens what `docs/decisions/0045-divide-by-zero-restriction-only.md` declined one day
  earlier, with prediction **F-7** of `docs/STAGE_F_DESIGN.md` (*"`wellFormed` stays at five clauses"*) standing
  on that ruling.

### The trade, stated in one place

| principle | Design I | Design III |
|---|---|---|
| source positions as addresses | preserved | violated |
| minimal AST representation | preserved | weakened |
| no unnecessary `wellFormed` clause | preserved at five | requires a sixth |
| preserving existing correctness structure | statements survive, proofs re-done | statements survive, fewer proofs re-done |
| avoiding silent unsoundness | lockstep survives and must be re-proved for paths | lockstep eliminated, strongest on this axis |

The two designs trade the last row against the first three. That is the entire decision.

## 3. Decision

**Design I**, on three grounds:

1. **The source-position-as-address principle is preserved.** A send site remains checkable against source text
   by counting statements, now per level of nesting.
2. **No sixth `wellFormed` clause.** The predicate stays a five clause name resolution predicate, so `0045`
   stands and F-7 is not refuted.
3. **The send AST representation is unchanged.** `GeneralStmt.send` carries no translator facing data, and models
   that are structurally equal remain equal.

**This decision preserves existing architectural commitments; it does not minimise implementation effort.**
Design III is the cheaper design by every measure taken, and the choice is made against it deliberately. Stating
that plainly matters, because a later reader who rediscovers Design III's lower cost should find it already
weighed rather than apparently overlooked.

**Where this is judgement rather than measurement.** Design III's strongest argument is not economy: it deletes
the only failure mode no gate can see. A ruling that weighed bug class elimination above the address principle
would have been defensible. It would have had to be recorded as **retiring the address principle explicitly**,
and it would have reopened the sixth clause question. That is the trade this decision declines, not one it
overlooks.

## 4. Consequences

**Positive.**

- Site identity stays **source checkable**: a reader counts statements per level and arrives at the same address
  the translator used.
- The model philosophy is preserved: the DTR AST represents the fragment and nothing about the translation of it.
- The DTR AST stays minimal: one new constructor, `ifThenElse`, whose name `docs/STAGE_B_DESIGN.md` section 7
  already fixed.
- Every correctness claim's **text** is unchanged, and C8's six field shape needs no change.

**Negative.**

- **Path based reasoning** replaces arithmetic on a `Nat`. Monotonicity gives way to a prefix extension lemma,
  and lexicographic order must be supplied or avoided deliberately.
- **Continuation semantics** for nested bodies: a stack on `GeneralActorRuntime`, which every correctness module
  quantifies over, and more internal step rules.
- **Correspondence and routing proofs must be updated.** Measured: **62 theorems mention a site or an index in
  their statement**, 48 in `Translation` (`GeneralBasic` 27, `GeneralRouting` 21) and 14 in `Correctness`. Most
  are projection style and should follow the definitions mechanically; the genuinely new work is the prefix
  extension lemma, the restated injectivity proof, and the `GeneralContinuationCompiles` site conjunct with its
  four consumers.
- `Correctness.generalTauSteps_forward` grows a case and `GeneralLabelWeakBisimulation.forwardTauMatch`'s
  inhabitant is re-proved. The *"five target internal constructors against the source's three"* count moves in 8
  tracked places, four of them Lean docstrings.

## 5. Non-goals

- **No benchmark work starts here.** No benchmark file, registry entry, expected output or benchmark document.
  The binding rule stands: benchmarks require the selected set's features implemented, the pipeline handling them
  end to end, transformations documented, and results reproducible.
- **No implementation starts here.** This record fixes an architecture, not a schedule, and authorizes no Lean
  change.
- **No `for` support and no local declaration support.** Both were measured to unlock **zero** benchmarks,
  because every one of the 11 corpus files using them also needs a permanently excluded construct. Both are out
  of scope until that changes.
- **No reopening of closed stage G decisions.** `0042`'s partial quotient, `0043`'s Option A, `0044`'s label
  level interface, `0045`'s fragment restriction, `hConsumeAnswer`, the `GeneralInstantBlock` theorem shapes, and
  the three C7 residues are all untouched. `0044` is closed: its six field shape does not need to change under
  this decision, and that reading should be confirmed rather than assumed before it is relied on.

## 6. Next milestone after approval

1. **Design the nested body representation.** `GeneralStmt.ifThenElse : GeneralExpr -> GeneralBody ->
   GeneralBody -> GeneralStmt`, self nesting through the existing abbreviation, so `compileGeneralBody`'s `nil`
   and `cons` `rfl` equations survive; its docstring records that those `rfl` proofs are load bearing for the
   order preservation induction. Settle the step-into rule set in the same document.
2. **Implement `if`/`else` through the required correctness layers**, all ten of `CONTRIBUTING.md`'s feature
   completion rule: source syntax, source well-formedness, source semantics, target syntax, executable
   translation, target semantics, structural correctness, semantic correctness, a regression model, and
   documentation.
3. **Then, and only then, proceed to benchmark adaptation.** `if`/`else` is a prerequisite for 23 of the 25
   candidates, including all 20 published case studies that carry `.property` files.

`while` is deliberately **not** in this sequence. It unlocks 2 benchmarks, needs Java bridge work that `if` does
not (`WhileStatement` is not imported by the exporter at all), and raises a question `if` does not: a loop makes
an internal segment unbounded, while `generalTauSteps_forward` walks a finite chain. It deserves its own decision.

---

## 7. As implemented, 2026-09-04

**Appended after the fact. Sections 1 to 6 are the approved decision and are left exactly as approved**;
this section records where implementation confirmed the decision and where it falsified the decision's own
predictions. Nothing above is edited, for the reason `AGENTS.md` gives about historical records.

### Confirmed

- **Design I as decided.** `Translation.SendSite.index : List Nat`; one new constructor,
  `GeneralStmt.ifThenElse`, on each side; `DTR.GeneralStmt.send` unchanged;
  `DTR.GeneralModel.wellFormed` still five clauses.
- **The branch selector is structural and alternating**, ruled 2026-09-03: a path is
  `[…, statementPosition, branchSelector, …]` with `0` for the then-branch and `1` for the else-branch, so
  `1.0.2` reads *"statement 1, then-branch, statement 2"*. The two rejected encodings were a branch-tagged
  `PathStep` component, which moves the field off `List Nat`, and offsetting else-branch positions past the
  then-branch's length, which makes an address unreadable without counting the other branch.
- **Step-into, not splicing**, on both runtimes: `DTR.GeneralActorRuntime.frames` and
  `LF.GeneralReactorRuntime.frames`, both `List GeneralBody`, both **non-defaultable**, and both read by
  `idle`, which became `activeBody.isEmpty && frames.isEmpty`. The field docstrings record why splicing
  was rejected: spliced statements would occupy top-level positions while the routing table addresses them
  at `levelPath ++ [i, side, …]`.
- **Source checkability**, the property the whole decision was for, is pinned rather than argued:
  `Relico/Tests/GeneralConditional.lean` reads the address of a send inside a then-branch off a real body
  and fixes it at `[1, 0, 0]`, rendered `1.0.0`.

### Falsified by implementation

- **Section 6 predicted that `compileGeneralBody`'s `nil` and `cons` `rfl` equations survive. They did
  not.** Making the statement type nested moved several traversals to well-founded recursion, which does
  not reduce; the repair was to split every such traversal into a statement-level and a body-level
  function. `docs/STAGE_H_FINDINGS.md` **F89 part 1** records the measurement, the wrong first diagnosis,
  and the full list of functions that changed shape.
- **The negative consequence "monotonicity gives way to a prefix extension lemma" was right about the
  need and wrong about the instrument.** What landed is not a prefix order but
  `Translation.GeneralSendAtPath`, an inductive relation with one constructor per path step, plus
  `shiftHeadPath` and `bumpHeadPath` for the address arithmetic. The monotonicity lemma
  `site_index_ge_of_mem_externalSendsFromIndex` survived as a shape lemma — `index ≤ position` on a `Nat`,
  with a residue — and no lexicographic order was needed anywhere.
- **The nested chain conjunct was needed, and the first plan for discharging it was unsound.** The
  correspondence's site conjunct now quantifies over `GeneralSendAtPath` at
  `context.levelPath ++ shiftHeadPath index path`, which is what makes a branch's obligation the enclosing
  one instantiated a constructor deeper. An earlier plan discharged the initial establisher's obligation by
  *refuting* nested paths from `DTR.GeneralModel.statementResolves`; that plan cannot work, because
  `generalCorrespondence_initial` holds `program.wellFormed`, not `model.wellFormed`, and
  `Translation.compileGeneralModel` never checks the latter. The obligation is discharged positively
  instead, by `Translation.externalSendsFromIndex_knownRebec_of_path`.
- **The estimate "62 theorems mention a site or an index in their statement" understated the work in one
  direction and overstated it in another.** The `Translation` half was almost entirely mechanical, because
  nothing orders sites and no generated name reads the index; the genuinely new work was concentrated in
  four places the estimate did not separate out: site injectivity, the two site lemmas' residues, the
  nested path evidence, and the two branch transfer lemmas.

### Still owed by this decision

Nothing in the implementation layers. `DTR.GeneralModel.statementResolves` still **refuses**
`DTR.GeneralStmt.ifThenElse`, so the accepted fragment has not moved and
`docs/supported-fragment-general.md` is correctly unchanged: its two sentences about conditionals say they
are refused at the frontend and owed to stage H, and both remain true. Opening the fragment is a separate
decision, and two alarms are already written for that day —
`LF.GeneralStmtOrigin`'s conditional arm and
`Correctness.not_mem_ifThenElse_of_compiled_of_resolves` — each of which says so in its own docstring.
