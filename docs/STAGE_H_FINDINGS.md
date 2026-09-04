# Stage H findings: F89 onward

**Why this file exists.**
Stage H adds `if`/`else` to the accepted DTR fragment: one new source constructor, path-based send-site
identity under decision [`0046`](decisions/0046-send-site-identity-under-nested-control-flow.md), and
step-into continuation semantics on both sides of the translation. Its findings start at **F89**,
continuing the single `F` series that [`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md) opened at F1–F20,
[`STAGE_D_FINDINGS.md`](STAGE_D_FINDINGS.md) carried to F21–F33,
[`STAGE_E_FINDINGS.md`](STAGE_E_FINDINGS.md) carried to F34–F58,
[`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md) carried from F59, and
[`STAGE_G_FINDINGS.md`](STAGE_G_FINDINGS.md) carried to **F88**.

Nothing before F89 is restated, renumbered or amended here. F88 keeps its place at the end of
[`STAGE_G_FINDINGS.md`](STAGE_G_FINDINGS.md); the series continues across files, as it has since stage D.

**The provenance rule, unchanged since stage D.** Every entry carries one of four grades, and where a
single entry mixes them the sub-claims are graded separately rather than the whole taking the weakest
label: **measured** (a named run produced the result, identified well enough to repeat), **read** (a
reading of source at a cited declaration, including absence established by a described search),
**decided** (a choice between recorded alternatives, with the alternative stated), and **inferred**
(argued, not run, and either it names the experiment that would settle it or it does not belong here).

`docs/decisions/0046-send-site-identity-under-nested-control-flow.md` owns what stage H *does* and why.
This file owns only what stage H *found wrong*, or found true and surprising, while doing it.

---

## F89: two stage H changes preserved every theorem in the development while silently breaking a load-bearing property no theorem states

**Grade: measured**, both parts, each by a named run.

Stage H changed two things whose consequences no theorem could see. Adding
`DTR.GeneralStmt.ifThenElse` made the statement type a **nested** inductive, and changing
`Translation.SendSite.index` from `Nat` to `List Nat` changed how an address *prints*. Neither change
made any theorem false. Neither was caught by the type checker. One was caught by a regression pin two
modules away from the edit; the other was caught before it landed, and only because the pinned values it
would have moved were being read for an unrelated reason.

The two parts are filed as one finding because they share a shape, and the shape is the point: **a
property that no theorem states and no type expresses is a property the build cannot defend.** Both of
these are such properties. One is *definitional reducibility*; the other is *the text a value renders
to*.

### Part 1: a single function recursing into two nested bodies is compiled by well-founded recursion, and a well-founded definition does not reduce

`DTR.GeneralStmt` and `LF.GeneralStmt` each gained
`| ifThenElse : GeneralExpr → List GeneralStmt → List GeneralStmt → GeneralStmt`, which makes the type
nested: the constructor's arguments mention `List` of the type being defined. Several traversals were
then written the obvious way — a single function over a body, whose conditional arm recurses into the
head statement's two branch bodies *and* into the tail. `LF.setPortNamesOfBody`,
`Translation.externalSendsFromIndex` and `Translation.selfSendsFromIndex` were all written like that.

Lean **accepted** all three. It did not accept them structurally: it fell back to well-founded
recursion, silently, because that is what the equation compiler does when structural recursion fails.
And a well-founded definition does not reduce — its unfolding goes through `WellFounded.fix`, whose
recursor is blocked by an accessibility proof that is not a constructor application. So the *equations*
remain provable by `simp`, and every theorem in the development still holds, while `rfl` and `decide`
stop evaluating the function.

**What that broke, measured.** `LF.GeneralProgram.wellFormed`'s guard calls `setPortNamesOfBody`, and
`Relico/Tests/GeneralInitialization.lean` defines its pinned program by *matching on the result of the
compilation* and then pins `compileGeneralModel pinModel = .ok pinProgram` by `rfl`. With the
single-function traversals in place, `lake build` reported the library green and those two pins failed,
in a module that mentions neither conditionals nor `setPortNamesOfBody`. The first diagnosis was wrong:
the `levelPath` parameter's position was blamed — a parameter that varies in a recursive call may not sit
before the colon — and moving it into the matched position changed nothing, because the shape, not the
binder, was the cause.

**The measurement that settled it.** A probe defined the same computation twice over the same nested
inductive: once as a single function recursing into the branch bodies, once as the standard pair of a
statement-level function and a body-level one. `pairBody [] = 0` holds by `rfl`; `singleBody [] = 0`
does not. Same file, same toolchain, same data.

**The repair, applied everywhere.** Every traversal over a possibly nested body is now a statement-level
function paired with a body-level one: `LF.setPortNamesOfStmt` / `setPortNamesOfBody`,
`Translation.externalSendsFromStmt` / `externalSendsFromIndex`,
`Translation.selfSendsFromStmt` / `selfSendsFromIndex`, `LF.stmtWellFormed` / `bodyWellFormed`,
`LF.CppPrinter.renderGeneralStmt` / `renderGeneralBranchBody`,
`LF.CppPrinter.generalEffectNames` / `generalEffectNamesFrom`,
`DTR.decEqGeneralStmt` / `decEqGeneralBody`, and `LF.GeneralStmtOrigin` / `GeneralBodyOrigin`. Where the
pair form changed the *shape* of an equation a proof depended on — a `setPort` head now contributing
`[port] ++ …` rather than `port :: …` — the fix was a set of `@[simp]` per-constructor equation lemmas,
not a rewrite of the proofs.

**A second, smaller consequence of the same cause.** `Translation.compileGeneralBody`'s `nil` equation
was `by rfl` before stage H and is `by simp` after, and
`Relico/Correctness/GeneralCorrespondence.lean`'s and `Relico/LF/GeneralKindOrigin.lean`'s traversal
equations moved the same way. No value moved; only the proof that names it. Each such site says so in
place, because a reader who finds `simp` where `rfl` would obviously do is entitled to know that `rfl`
was tried.

### Part 2: `toString` on a `List Nat` site would have silently rewritten three pinned diagnostic strings

`Translation.SendSite.index` became `List Nat` under decision `0046`. `renderGeneralSendSite`, the
function every routing and translation refusal calls to name the offending send, rendered that field with
`toString`.

**Measured with the pinned toolchain:** `toString ([1] : List Nat)` is `"[1]"`. So every refusal that had
read *"message server `settle`, statement at index 0 counting from zero"* would have read *"…statement at
index [0] counting from zero"*, and `routedSendSiteIndices` in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean`, which maps `toString` over three sites, would have
gone from `"1|2|3"` to `"[1]|[2]|[3]"`.

**Why nothing would have failed at the point of the edit.** The type change is legal: `toString` is
defined for `List Nat`, so the code compiles. The three moved values are compared only in a bridge main,
and `lake build` does not compile the bridge mains — `lakefile.toml` declares one `lean_lib` and one
`lean_exe`, and `frontend/lean-bridge/*Main.lean` holds an inline `def main` that is compiled on demand
by `frontend/check-general-lean.sh`. So the library would have been green, the type checker satisfied,
and three values that appear in committed gate transcripts changed under a change nominally about
addressing.

**The repair.** `Translation.renderGeneralSitePath` renders a path as dot-separated components: `[1]` is
`1`, `[1, 0]` is `1.0`. Every level-0 site therefore renders **byte-identically** to what stage E
emitted, the two refusal texts and the digest keep their pinned values, and a nested send reads `1.0`
rather than as a list. `routedSendSiteIndices` was changed to call the renderer instead of `toString`,
which is a change to the *computation* so that the *expectation* could stay fixed — the direction
`AGENTS.md` requires.

### The transferable check

**After a change to a type's representation or to a definition's recursion shape, enumerate the
properties the old form had that no theorem states.** There are two classes worth naming, because both
recur and both are invisible to `lake build`:

1. **Definitional reducibility.** Ask, of every function whose recursion shape changed: does `rfl` still
   evaluate it, and does `decide` still evaluate anything that calls it? No theorem says *"this
   function reduces"*, so nothing fails at the edit site; what fails is a `rfl` pin in a distant module
   that evaluates a whole pipeline. The check is mechanical — for each changed definition, `example :
   f <smallest closed argument> = <expected> := by rfl` — and it costs one line per function.
2. **Rendered text.** Ask, of every field whose type changed: is it printed anywhere, and is any printed
   value pinned? `toString` is the trap, because it is total and instance-driven, so it silently follows
   the type. `grep` for `toString` on the changed type before trusting a green build, and prefer a
   named renderer over `toString` for anything a transcript records, so that the spelling is a decision
   with a docstring rather than an instance's default.

**And run the gates, not only the build.** Both parts of this finding are properties that `lake build`
is structurally unable to check: one lives in the reducibility of a definition the library never
evaluates, the other in a file the library never compiles. The instruments that see them are the `rfl`
and `decide` pins in `Relico/Tests/*` and the assertion set in `frontend/check-general-lean.sh`. A
development that only proved theorems would have shipped both defects with every proof intact.
