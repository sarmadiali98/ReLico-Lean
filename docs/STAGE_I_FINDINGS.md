# Stage I findings: F90 onward

**Why this file exists.**
Stage I widens the *accepted* fragment rather than the translated one. Its first milestone, I0, admits
`if`/`else` end to end: the elaborator stops refusing the construct, and source well-formedness stops
refusing it too. Its findings start at **F90**, continuing the single `F` series that
[`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md) opened at F1–F20,
[`STAGE_D_FINDINGS.md`](STAGE_D_FINDINGS.md) carried to F21–F33,
[`STAGE_E_FINDINGS.md`](STAGE_E_FINDINGS.md) carried to F34–F58,
[`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md) carried from F59,
[`STAGE_G_FINDINGS.md`](STAGE_G_FINDINGS.md) carried to F88, and
[`STAGE_H_FINDINGS.md`](STAGE_H_FINDINGS.md) opened at **F89**.

Nothing before F90 is restated, renumbered or amended here.

**The provenance rule, unchanged since stage D.** Every entry carries one of four grades, and where a
single entry mixes them the sub-claims are graded separately rather than the whole taking the weakest
label: **measured** (a named run produced the result, identified well enough to repeat), **read** (a
reading of source at a cited declaration, including absence established by a described search),
**decided** (a choice between recorded alternatives, with the alternative stated), and **inferred**
(argued, not run, and either it names the experiment that would settle it or it does not belong here).

---

## F90: the refusal arm was the load-bearing part, and removing two of them cost more than adding the constructor did

**Grade: measured**, except where a sub-claim is marked otherwise.

Stage H added `DTR.GeneralStmt.ifThenElse` across all ten completion layers and deliberately left two
`false` arms behind, in `DTR.GeneralReactiveClass.statementTargetDeclared` and
`DTR.GeneralModel.statementResolves`, so that the accepted fragment did not move. Stage I0 turned those
two arms into recursions. That is a two-arm edit by line count, and it broke the build in a module
whose subject matter never mentions conditionals.

**What broke, measured.** One full `lake build` after the two arms changed: three errors, all in
`Relico/LF/GeneralKindOrigin.lean`, at job 546 of 548, with the rest of the library green. One was
mechanical: `sendsResolveToMessageServers` now ends in a recursion rather than in `List.all`, so a
consumer that finished with three nested `List.all_eq_true.mp` steps needed a bridge in place of the
innermost one. The other two were real, and each required the same two structural changes to a
theorem:

1. `DTR.GeneralModel.exists_messageServer_of_mem_selfSendsFromIndex`, whose conditional arm had been
   discharged by the source refusal.
2. `not_mem_ifThenElse_of_compiled_of_resolves`, which became **false as a statement**, taking with it
   the `ifThenElse` case of `generalStmtOrigin_of_mem_compiledBody`, which had been discharged by
   `absurd` on that lemma.

**The two changes, both times.** Move the level path from a parameter fixed before the colon into the
quantifier, because a branch is enumerated at `levelPath ++ [index, side]` and not at its parent's
path; and replace `induction body` with `cases body` plus a **self-recursive call**, because a branch
body is not a sublist of the body that holds it. Lean accepts both recursions **structurally**, as it
already accepted `Translation.exists_compileGeneralBody`'s, so neither owes a `termination_by`. That
`exists_compileGeneralBody` had already established the idiom in this repository is what made the two
rungs mechanical rather than exploratory.

**Two predictions in the source, graded separately.** Both broken arms carried a docstring naming
itself as an alarm: *"this arm failing to compile is the intended alarm"* on the first, and *"It is the
alarm, not the answer... Deleting the lemma is the first step of that work"* on the second. Both were
**accurate about the location** and both **understated the size**: the second alarm's "first step"
turned out to be deleting a 175-line proof and generalising a theorem with ten hypotheses. A third
prediction was simply **wrong**, and finding it wrong is a result: `statementTargetDeclared`'s docstring
said the no-branch property was *"what the traversals in `Translation.GeneralRouting` rely on"*. No such
reliance exists. Searched by name and confirmed by the build, whose only fallout was in
`GeneralKindOrigin`.

**The public interface did not have to move, and the earlier plan said it would.** The recorded plan
had `generalStmtOrigin_of_mem_compiledBody` generalised in place, its two public consumers taking new
arguments, and the converse of `generalStmtOrigin_of_mem_of_bodyOrigin` owed. All three were avoidable.
Generalising a *private* theorem to conclude `GeneralBodyOrigin`, then re-deriving the public statement
through the **existing forward** bridge, left the public statement byte-identical and both consumers
untouched. The converse was never needed. **Decided**, with the alternative stated: generalising in
place would have worked and would have changed two call sites for no gain.

**A second, quieter finding: the changed definition had no instrument.** `DTR.GeneralModel.wellFormed`
is a `Bool` that the frontend evaluates and that any `Relico/Tests/*` module could `decide`, and
**measured: none did**. So the recursion added to `statementResolves` was unprotected against exactly
the failure F89 part 1 records, a fall from structural to well-founded recursion, which keeps every
theorem true while silently ending reducibility. `Relico/Tests/GeneralConditional.lean` already held a
conditional model and asserted *in prose* that it was not well-formed; stage I0 replaced that paragraph
with `example : conditionalModel.wellFormed = true := by rfl`. One line, and it is now the only thing
in the development that would notice.

**Two things stage I0's acceptance did not establish, recorded so a green pair of gates is not
over-read. Both have since been closed by measurement, and each closure is recorded where the gap
stood.**

1. **Real `lfc` had never compiled a generated conditional. Closed by the witness milestone that
   followed, and the sequence is the point.** When stage I0's acceptance landed,
   `frontend/check-general-lf-target.sh` compiled the five programs the bridge mains built and not one
   of them contained an `if`: **measured**, `grep -c 'if ('` over the gate's whole log returned `0`. So a
   green `GENERAL_LF_TARGET_OK` said nothing about the construct stage H had taught the printer to emit,
   and that output was pinned by `rfl` in `Relico/Tests/GeneralConditional.lean` and by nothing else.
   The follow-on milestone added a sixth witness, `emit-conditional`: one class, one instance, one state
   variable, no ports and no connections, whose only distinguishing construct is a conditional with two
   non-empty branches. **Measured against `lfc 0.11.0`:** `LFC_ACCEPTED` moved from 5 to 6, the gate's
   log now matches `if (` once, and the emitted reaction body
   `if (on) { on = false; } else { on = true; }` was reported `lfc accepted it` and then
   `it ran and exited cleanly`. The lesson is not that the text turned out to be fine. It is that
   **nothing in a ten-layer proof, a green library and two green gates could tell us whether it was**,
   for as long as no witness carried the construct.
2. **The new fixture's exporter-equivalence was unverified. Closed at stage I's S-I6, by a measurement
   this gap's own prediction got wrong.** `branching.parser.json` was written by
   hand, in the canonical `sort_keys` form, and it is structurally conformant: **measured**, every key
   set it uses at every level already occurs among the ten pre-existing positives, and **measured**, all
   26 of its `line` fields point at the construct they name in `branching.rebeca`. What was *not*
   measured was that `RebecaGeneralJsonExporter.java` would emit it byte-identically. This gap then
   predicted the obstacle precisely and **predicted it wrongly**: it said the FMCAD
   Rebeca-compiler artifact zip was "not on this machine", and stage I's S-I6 census found that
   `~/.m2/repository` has held `rebecalang/compiler` 2.25 and 2.28, the Spring family and ANTLR all
   along — enough for the exporter to compile and run directly under `java -cp`, without the artifact
   and without the java-bridge gate's maven scaffold. The run measured: **the real exporter emits
   `branching.parser.json` byte-identically**, and it emits `locals.parser.json` byte-identically too,
   confirming the hand-written prediction of the very next stage. The lesson is the one F89 part 2
   already taught about pinned text, now aimed at a claim about the *machine*: a stated environmental
   blocker is a measurement with a date on it, not a fact, and the cheapest way to keep it honest is to
   re-run the search that produced it before repeating it.

### The transferable check

**When a constructor is added behind a refusal, write down what the refusal is load-bearing for, and
treat removing it as its own milestone with its own proof obligations.** A `false` arm is not a
placeholder. It is a hypothesis that the rest of the development is entitled to use, and code does use
it: two theorems here discharged whole cases from it, one of them by `absurd`, which is the strongest
possible dependence on a refusal because it will not survive the refusal's removal in any form.

Three specifics worth carrying forward:

1. **Grep for `absurd` and for arms whose proof is a contradiction from a well-formedness clause,
   before changing that clause.** They are the cases that cannot be repaired locally; every other kind
   of consumer can usually be patched with a bridge lemma.
2. **An alarm docstring should name its consumers and their size, not just itself.** Both alarms here
   pointed at the right line and neither said "a 175-line lemma and a ten-hypothesis theorem", which is
   the number that decides whether the removal is a turn's work or a milestone's.
3. **After changing a definition that a `Bool` guard reaches, check that some `rfl` or `decide` pin
   evaluates that guard.** If none does, add one in the same edit. The check costs one line and it is
   the only defence against F89 part 1, which no theorem and no type can see.

---

## F91: the guard that duplicated its own check, and the witness that found it

**Grade: measured**, every sub-claim, each by a named run or a named census.

Stage I added local variable declarations to the general fragment across six milestones, S-I1
through S-I6: the constructor on both sides, the translation, both step rules and the forward
transfer, elaborator and guard acceptance, the exporter widening with its fixture move, and two gate
witnesses. The design held: no runtime environment was added, no store was extended, no
correspondence conjunct was added, and `DTR.GeneralModel.wellFormed` kept its five clauses
throughout. A local is a third kind of name in a store that was never segmented by kind, which is
why the whole stage cost one constructor per side, one rule per side, one transfer lemma, and
threading — not new state.

That headline understates the stage, because the interesting events were all failures of
instruments, each caught by a different one. They are recorded here as one finding because they
share a shape: **the thing that found the defect was never the thing the defect lived in.**

### The headline: `reactionWellFormed` duplicated `bodyWellFormed` without the threading

The S-I6 bridge witness — a one-class model that declares a local, reads it, and assigns to it —
was refused by the translation's own LF guard on its first gate run, with `LFC_ACCEPTED` stuck at 4.
The cause was not the witness and not the exporter: `LF.reactionWellFormed` walked a reaction's body
with `List.all` over `stmtWellFormed reaction.parameters`, forming the same conjunction
`bodyWellFormed` forms — **but without the locals threading S-I5 had added to `bodyWellFormed`.** A
local declared in a reaction body was therefore invisible to every statement after it, and the
widened assignment check the S-I5 layer was written to admit refused the one model that used it.

Three properties of this defect are the finding. First, it **stood through two reviews**: the S-I5
implementation and the S-I5 landing both passed, because every other instrument evaluates either the
elaborator or `stmtWellFormed` directly, and `reactionWellFormed`'s `List.all` path is reached only
by `compileGeneralModel` running the guard over its own output. Second, the old docstring had
already named the duplication and dismissed it — "left as its `List.all` because it is not part of
this recursion and rewriting it would move a definition no clause of this change touches" — which is
the exact shape of a comment that is true on the day it is written and load-bearing wrong the day
someone changes what it shadows. Third, the repair was to **route through the traversal rather than
patch the path**: `reactionWellFormed` now calls `bodyWellFormed`, removing the duplication, and both
docstrings record the finding. **Measured after the repair:** `LFC_ACCEPTED 7`, the witness's
`int entry = 1;` in the gate log, lfc accepting and running it.

### The supporting failures, one per instrument

- **The red-by-design obligation worked as designed.** S-I1 landed with
  `exists_compileGeneralBody`'s `.localDecl` case unprovable while the translator refused — the
  stage H situation verbatim — and the arm was written in its repaired shape so the build error
  *named* the owed equation `compileGeneralStmt_localDecl`. S-I3 provided it and the tree went
  green. No statement was weakened, no `sorry` was written, and the refusal period lasted exactly
  one layer.
- **The full build is the only census, three times over.** S-I3's plan named one downstream
  candidate; the first green chain surfaced seven arms. S-I4a's module-target verification passed
  while two modules downstream needed arms. S-I4b's full build found three watch-list sites the
  grep census had only listed. Grep undercounts because proof bodies case on bare constructor
  patterns (`| assign target value =>`), not on annotated scrutinees; module builds undercount
  because everything downstream of an edited module is skipped when the edited module is red.
- **The Python suite found three pre-existing defects no Lean instrument could see.** Run directly
  (`python3 frontend/test_validate_general_v1.py` — unittest-based, so runnable where pytest is
  not), it failed 2 of 15 on the untouched committed tree: `branching.rebeca` used `record`, a
  Rebeca reserved word, as a message-server name, and sat in no provenance list; fixing those
  surfaced a third, that the fixtures README never named it. All three were stage I0 debts from the
  hand-written fixture, invisible to the Lean gate that happily accepted the document.
- **Two self-caught bugs, both recorded in the code that trapped them.** The first
  `locals.parser.json` had an off-by-one line drift its own line-checker caught before anything
  consumed it. The first replacement mutation in the Python suite was silently a no-op because
  `list.insert` returns `None` and an `and` chain short-circuits on it — a standalone reproduction
  proved the validator right and the test wrong, and the trap is now a comment in the test.
- **The maven cache closed F90's second gap by contradicting it.** F90 said the exporter could not
  run on this machine because the FMCAD artifact zip was absent. The S-I6 census found
  `~/.m2/repository` holding the rebecalang compiler jars, Spring and ANTLR all along; the exporter
  compiles and runs under `java -cp`, and the run confirmed `branching.parser.json` and
  `locals.parser.json` byte-identically. F90's closure note records the wrong prediction where it
  stood.

### The transferable check

**When a predicate is defined as "the same conjunction as" another traversal, and the two are kept
apart only by a comment that says the duplication is harmless, route one through the other at the
first change that touches either.** The comment is a claim about a world in which neither
definition changes; the first change to one of them converts the claim into a guard difference, and
guard differences are found only by the input that exercises the differing path — which for a
translation's output guard means a compiled model, i.e. a gate witness, i.e. the one instrument
whose whole purpose is to be the input nothing else provides.

Two specifics worth carrying forward:

1. **Every stage that widens a guard should end with a witness that runs the widened path through
   the whole pipeline**, not only through the layer that was edited. The S-I6 witness was scoped as
   "put `int x = 1;` through lfc" and found a defect in the Lean guard instead — instruments find
   defects where they are, not where the plan pointed.
2. **A stated environmental blocker is a measurement with a date, not a fact.** Re-run the search
   that produced it before repeating it in a finding; F90's one wrong sentence cost a stage of
   deferred verification that was never actually blocked.

