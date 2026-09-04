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
over-read. The first has since been closed by a follow-on witness; the second is still open.**

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
2. **The new fixture's exporter-equivalence is unverified.** `branching.parser.json` was written by
   hand, in the canonical `sort_keys` form, and it is structurally conformant: **measured**, every key
   set it uses at every level already occurs among the ten pre-existing positives, and **measured**, all
   26 of its `line` fields point at the construct they name in `branching.rebeca`. What is *not*
   measured is that `RebecaGeneralJsonExporter.java` would emit it byte-identically. A JDK 21 and Maven
   are present on this host, so the obstacle is not the toolchain: `frontend/java-bridge/check-general.sh`
   needs the FMCAD Rebeca-compiler artifact zip, which is not on this machine. One command settles it
   the day that artifact is available.

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
