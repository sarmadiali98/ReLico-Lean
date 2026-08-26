# Stage G findings — F63 onward

**Why this file exists.**
Stage G makes designer-specified priority *preserved and observable* rather than merely emitted in a
defined order, which is what stage F delivered. Its findings start at **F63**, continuing the single
`F` series that [`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md) opened at F1–F20,
[`STAGE_D_FINDINGS.md`](STAGE_D_FINDINGS.md) carried to F21–F33,
[`STAGE_E_FINDINGS.md`](STAGE_E_FINDINGS.md) carried to F34–F58, and
[`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md) carried from F59.

This file exists rather than an extra section of [`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md) because
that file states its own scope in one sentence — *"This file owns only what stage F found wrong"* — and
F63 was not found by stage F. It was found while deriving stage G's scope from the repository, which is
also the reason it went unnoticed: it is a defect that accumulated across stages B through F without
being any single stage's output. Filing it under a heading that says "Stage F" would reproduce **F54**,
whose whole content is that an entry which exists but is invisible from where a reader looks costs a
duplicate investigation.

**The provenance rule, unchanged since stage D.** Every entry carries one of four grades, and where a
single entry mixes them the sub-claims are graded separately rather than the whole taking the weakest
label: **measured** (a named run produced the result, identified well enough to repeat), **read** (a
reading of source at a cited `path:line`, including absence established by a described search),
**decided** (a choice between recorded alternatives, with the alternative stated), and **inferred**
(argued, not run — and either it names the experiment that would settle it or it does not belong here).

`docs/STAGE_G_DESIGN.md` owns what stage G *does* and why. This file owns only what stage G *found
wrong*.

---

## F63 — the repository's headline claim is quantified over a fragment five stages out of date, and nothing declares the fragment it actually accepts

*Read.* Two parts, both repaired in the same commit that files this entry. They are one finding because
they share a single cause and a single repair site: there is no tracked statement of what the general
family accepts, so both the outer claim and the inner carve-out are unstatable.

### Part 1 — "the declared supported fragment" resolves to vertical slice v0

The project's top-level claim is quantified over a named fragment in three places:

- `README.md:3` — *"an executable Lean 4 translation from a supported fragment of Deterministic Timed
  Rebeca to a generated subset of Lingua Franca"*.
- `docs/trusted-boundary.md:28` — *"For every well-formed source model in the supported fragment, the
  project aims to prove that:"*, followed by the nine numbered obligations.
- `docs/trusted-boundary.md:62`, the *Intended claim* — *"The executable DTR-AST-to-LF-AST translation
  core implemented in ReLico-Lean is formally verified for the **declared** supported fragment."*

The only document that declares one is `docs/supported-fragment.md`, and it declares **vertical slice
v0**: one reactive class, one actor instance, one integer state variable, one constructor, one message
server, no message parameters, no payload values, `selfSend` as the only send form, and integer literals
plus one state-variable reference as the entire expression language (`:9-26`, `:41-49`).

Its *Initially excluded* list (`:82-97`) has sixteen entries, and the split is exactly even. **Eight have
since been delivered** — multiple classes and multiple actor instances (stage B), known rebecs and
external sends and ports and inter-reactor connections (stages C and E), message parameters and payloads
(stages D and E), actor priorities and message-server priorities (stage F, levels 1 and 2). **Eight
remain genuinely excluded** — conditionals, loops, arrays, inheritance, physical actions, environmental
inputs, broadcast, arbitrary LF programs — and reading the list as written, nothing else.

Half the list is stale, which is the strongest single argument that the document cannot be left as the
resolution of "the declared supported fragment": a reader has no way to tell which half they are in.

Grading this correctly matters, because the obvious verdict is wrong twice over. The document is **not
false about v0**; it is an accurate historical record of the first milestone, and its forward-looking
sentences were overtaken by the 2026-08-17 generalization pivot rather than being mistaken when
written. What is false is the *resolution*: a reader following "the declared supported fragment" from
the intended claim arrives at a declaration that excludes the priority work the claim is now largely
about. The defect is therefore in the pointer and the absence, not in the prose it points at — which is
why the repair is a dated scope marker plus a per-item delivery status, and **not** a rewrite of the v0
body.

The consequence is asymmetric and worth stating plainly, because it decides how urgent this is: the
outer claim is *understated* for what the tool accepts, and *misdescribed* for what is verified. No
proof is weaker than advertised. But the paper's scope section is the single most likely thing to be
drafted from a file named `supported-fragment.md`, and drafting it from this one would exclude stages
B through F from the paper's own statement of its subject.

### Part 2 — a binding decision to make theorem-eligibility legible was never carried out

`docs/STAGE_B_DESIGN.md:593-611` records the decision of 2026-08-18 — option **D**, guards as
theorem-level hypotheses — under the heading *"Consequences, which are now binding on stage B and on
every later stage"*. Two of those consequences are load-bearing for every stage since:

> *"Every stage-F/G correctness theorem carries them as explicit hypotheses. A theorem that needs
> determinism and does not name them is a bug in that theorem."*

> *"The three actor-tie and two message-server-tie fixtures identified in §7's table are therefore
> elaborable but not theorem-eligible. That distinction has to be legible, so §7's table graduates into
> the tracked docs alongside this file rather than living only here."*

The first was honoured: stage F's guard-relative theorems carry `ActorPrioritiesDistinct` and
`MessageServerPrioritiesDistinct` as explicit hypotheses, and `GeneralModel.wellFormed` still does not
mention priority. The second was not. Absence established by search: `grep -rniI
"theorem-eligible\|theorem eligible"` across `docs/`, `Relico/` and `frontend/` returns exactly one
line — `docs/STAGE_B_DESIGN.md:610`, the sentence that says the distinction has to be legible. The
table never graduated.

So five fixtures in the tracked corpus elaborate successfully and are excluded from every correctness
theorem, and no tracked document says which five. That is the same shape as **F47** (docstrings
crediting coverage to fixtures that cannot reach the code) and **F59** (ordering evidence credited to an
instrument that cannot produce it): a coverage boundary that is real, load-bearing, and invisible from
where a reader checks.

### Why this is one finding and not two

Part 1 is a missing *outer* boundary — what the tool accepts. Part 2 is a missing *inner* boundary —
which accepted models the theorems actually speak about. A reader needs both to interpret
`docs/trusted-boundary.md:28`'s "every well-formed source model in the supported fragment", and neither
exists in tracked form. The repair is one document, so the finding is one entry.

### Repair, and what is deliberately not repaired

Repaired here: a dated scope marker at the head of `docs/supported-fragment.md` recording that it
declares v0 and is retained as the historical declaration; a per-item delivery status on the
*Initially excluded* list separating the eight delivered from the eight still excluded; and the
namespace qualification at `docs/STAGE_C_DESIGN.md:794` (see below).

Deliberately **not** repaired here, and filed as stage G design work instead: writing the tracked
declaration of the general family's accepted fragment, and the theorem-eligibility table Part 2 owes.
Both are substantial documents whose content is partly decided by stage G's own scope — in particular
by which of `docs/trusted-boundary.md`'s nine obligations the general family can currently claim — and
writing them before that scope is approved would produce a third document that needs a marker later.
`docs/STAGE_G_DESIGN.md` states them as deliverables with the evidence already gathered here.

### A near-miss recorded because it nearly produced a false repair

While enumerating stage-G mentions, `docs/STAGE_C_DESIGN.md:794` — *"`GeneralStmt` has three
constructors"* — read as a direct contradiction of `docs/STAGE_F_DESIGN.md` §2.4, which says
*"`DTR.GeneralStmt` has exactly two constructors, `assign` and `send`"*. Measured: **both are true.**
`Relico/LF/GeneralSyntax.lean:349` defines an `LF.GeneralStmt` with exactly three constructors
(`assign`, `schedule`, `setPort`), and stage C is the stage that built the LF side, so `:794`'s
unqualified name means the LF type. `MultiStorePayloadStmt`'s "two" is also correct
(`assign`, `selfSend`).

The transferable point is the mirror image of `docs/STAGE_F_DESIGN.md` §7.4's triage lesson, and worth
separating from it. §7.4 failed by grading six lines without re-reading their paragraphs, so it called
two false claims cosmetic. This nearly failed the other way: a *true* claim looked false because it was
graded against the wrong referent, and the only thing that distinguishes the two cases is resolving the
namespace from the surrounding stage rather than from the name. Two types share the short name
`GeneralStmt` across `DTR` and `LF`, and the same is true of `GeneralSyntax.lean`, `GeneralExpr`,
`GeneralBody` and `GeneralWellFormed`. In tracked prose the namespace is not optional, and `:794` now
carries it along with both constructor lists.

---

## F64 — a reaction that never fires was recorded as a reaction with no source counterpart, and that was the stated reason for choosing the stage's central theorem

*Read.* The conclusion it was supporting is *decided*, and it survives on other grounds.

`docs/STAGE_G_DESIGN.md` §7, as landed in `dee5951`, rejected a strong step-by-step correspondence in
favour of the paper's weak bisimulation and gave two reasons. The first is correct: a step correspondence
with the whole-execution lift stated as owed is not the paper's architecture, and proves something
strictly weaker than `Theorem 1`. The second was this:

> *"the strong version is **false** of our generated programs: the emitted reactor contains a
> `drain_reaction` whose firings have no source counterpart, so a step correspondence admitting no
> internal steps has counterexamples in the repository already."*

**That is false — and the first attempt to say why was also false, which is the more useful half of this
entry.**

### The wrong refutation, recorded because it is the trap

`grep -rc "drain" Relico/ frontend/` returns matches in exactly four files, **all** under `frontend/`:
`check-general-lean.sh` (1), `fixtures/general/lean-reject/README.md` (1),
`fixtures/general/lean-reject/invalid-send-target-undeclared.json` (1), and
`lean-bridge/GeneralLfPrinterTestMain.lean` (10). **Zero occurrences anywhere under `Relico/`** — not in
`Relico/Translation/GeneralBasic.lean`, not in `Relico/LF/GeneralCppPrinter.lean`, not in the LF AST. The
conclusion drawn from that was *"`drain_reaction` is not translator output at all; it lives only in a
hand-built printer fixture"*, and it was written into this file before it was checked.

It is wrong. `fanInReceiverClass` in that test main is a **`DTR.GeneralReactiveClass`** — the file builds a
*source* model and feeds it through the real translation — and `drain` is one of its two message servers:
*"Its two servers are declared in the order `ping, drain` and prioritized in the order `drain, ping`"*. So
`drain_reaction` is emitted by `assembleGeneralMessageReactions` exactly like any other message reaction.
The string is absent from `Relico/` because the **name is data-derived**: it comes from the model, not from
a literal in the translator. String absence in an implementation is not artefact absence.

That is **F51**'s lesson pointed the other way. F51 recorded that absence of a string is not *invention*
when the method puts the witness outside the repository. Here absence of a string was read as absence of
the *emission*, while the witness was inside the repository the whole time, spelled by its input. A grep
bounded to `Relico/` answers "does the translator mention this name", which is a different question from
"does the translator emit this artefact", and for anything named after source data the two answers come
apart.

### The actual refutation

Two facts. The second is the general one and it is what the design now rests on.

`drain_reaction` **has a source counterpart**: the message server `drain` it is generated from. The
original claim's own words — *"whose firings have no source counterpart"* — are refuted by the declaration
that produces it. And in that model it never fires, because nothing sends `drain`; the same file records
*"Nothing sends `drain`, so its group is one action reaction and nothing else"*. **A never-firing reaction
is not an unmatched reaction**, and collapsing the two is the substance of the error: "no firings" was read
as "firings with nothing to match".

The general fact settles every model rather than one fixture.
`compileGeneralMessageServerReactionGroup` (`Relico/Translation/GeneralBasic.lean:1446` at this commit;
cited by name because line arithmetic does not detect a stale Lean cite, per the **F54** lesson) compiles a
message server's body **once** and passes the same `compiledBody` to *both*
`assembleGeneralMessageReactions` and `assembleGeneralPortReactions`. A port reaction therefore runs the
server's own body; it is not a forwarding stub that schedules the server's logical action. Together with
`assembleGeneralStartupReaction` for the constructor, **every reaction the general translator emits has a
source counterpart**, and the repository contains no counterexample to a lock-step correspondence at all.

**What this cost, and what it did not.** The conclusion — prove the paper's `Theorem 1`, weak
bisimilarity — is unchanged, because its first reason is sufficient on its own and is the reason the
decision-maker's instruction pointed at (*"read the paper first so we don't end up designing something
that would contradict that"*). What changes is a claim about **our own artefact** that a paper drafted
from these documents would have repeated, and three downstream statements that leaned on it: §7's τ
paragraph named `drain_reaction` firings as a τ member; §14 item 3 made an observable `drain_reaction`
firing *"the single prediction whose failure would cost the most"*, a prediction that cannot now fail
because the event does not exist; and §15 item 4 recorded the withdrawn reason as part of a settled
decision. All three are repaired in the commit that files this entry, and the real risk §14 item 3 was
groping at is restated there: **whether either τ set is non-empty is decided by the LTS granularity G2a
picks**, not by anything the translator emits.

**The mechanism.** `drain_reaction` was not invented, and neither was its emission — what was invented was
its *role*. Task **#97** moved it to the front of a reactor and ran the gate on the result, so it was
recent and familiar as *"the reaction whose position is interesting"*, and the reason its position is
interesting is that nothing sends it. "Nothing sends it" was then recalled as "nothing corresponds to it".
Those two properties sit one unmeasured inference apart, and that inference is the whole defect.

The check that separates them is asked of the **source** side, not the target: *does some source
declaration generate this reaction?* For every reaction family in `GeneralBasic.lean` the answer is yes —
message servers, send sites, the constructor — which is why the general measurement above is the durable
one and any fixture-level argument was never going to matter in either direction.

Correcting the wrong refutation adds a second and sharper rule, since it cost a second draft of this
entry: **for an artefact named after source data, a grep of the implementation cannot establish absence.**
`drain_reaction`'s name never appears in the translator that emits it, and never will. Whether something
is emitted is settled by reading the emitting function against its inputs, or by inspecting output — never
by searching the emitter for the output's name.

**Age.** Written and landed on 2026-08-23 and refuted the same day, before any Lean rested on it — the
one respect in which this is unlike **F53**, where three "by construction" claims outlived the findings
that refuted them. Both the original claim *and* this entry's first refutation were caught before being
committed, because §7's justification was re-checked before the first line of stage G's Lean was written,
on the standing rule that `docs/` is the paper's drafting source. The second catch came from a small habit
worth naming: *"servers"* is DTR vocabulary, and noticing that one word in a docstring is what exposed a
`DTR.` type where a hand-built LF program had been assumed.

---

## F65 — the design understated the project's own proof coverage: aims 8 and 9 are already proved for the multi-store family, twice

*Read.* Found in the same pass as **F64**, while gathering the exact API `selectedActor` must be built
against, and filed separately because the mechanism is the opposite one: F64 credited the repository with
an artefact it does not contain, and this credits it with **less proof than it has**.

`docs/trusted-boundary.md:28-38`'s aims 8 and 9 — *"every permitted source execution has a corresponding
target execution"* and *"every target execution corresponds to a permitted source execution"* — are
already discharged for the multi-store payload family, in two separate developments:

| Role | Module | Anchor declarations |
|---|---|---|
| Source finite executions | `Relico/DTR/GlobalMultiStorePayloadFiniteExecution.lean` | `Steps` |
| Target finite executions | `Relico/LF/GlobalMultiStorePayloadFiniteExecution.lean` | `Steps` |
| Execution correspondence | `Relico/Correctness/GlobalMultiStorePayloadFiniteExecutionCorrespondence.lean` | `ForwardStepsCompatible`, `BackwardStepsCompatible`, `finite_forward`, `finite_backward` |
| Priority-aware traces | `Relico/Correctness/GlobalMultiStorePayloadActorFiniteExecution.lean` (556 lines) | `SourceActorPriorityDispatchSteps`, `sourceActorPriorityDispatchSteps_forward`, `ActorDispatchEventTraceCorresponds`, `actorDispatchEventTraceCorresponds_length_eq` |

Two statements in `docs/STAGE_G_DESIGN.md` as landed in `dee5951` are wrong against that.

**§4 claimed the precedent is four modules.** *"The multi-store payload family already carries a full
actor-selection development. It is **four modules**, not one file"* — true of the *selection* development
and false as a description of the precedent, which the section is titled "The shape to mirror" and is
offering as exactly that. The four modules above are additional, and they are the ones bearing on §7's
subject rather than §6's.

**§7 item 6 implied the multi-store family has no finite-execution result.** It described the generic
`weakBisimulation_traceAgreement` as *"proved once over an abstract LTS, so it costs nothing per family
and can be reused by the multi-store family later"*. "Later" presupposes an absence. The family has two
such results already, and neither needs the generic theorem.

**Why the omission is not merely tidiness: it changes the argument.** With F64's justification withdrawn,
the live question was whether a lock-step correspondence is available to the general family, and these
modules answer it — *the existing shape is strict lock-step*.
`sourceActorPriorityDispatchSteps_forward` produces a target execution indexed by the **same `frames`
list** the source execution was indexed by, and `actorDispatchEventTraceCorresponds_length_eq` proves
`sourceEvents.length = targetEvents.length`: one target event per source event, no internal steps, no τ.
So lock-step is not refuted anywhere in this repository — it is *implemented*, and at its own granularity
it is a stronger statement than weak bisimilarity. Stage G still states the paper's weaker theorem, and
the honest reasons are now recorded in §4: `Theorem 1` is the claim this project is measured against, and
every `ActorDispatchFrame` carries the `ready` snapshot that is precisely §3's defect — a point that
structure's own docstring concedes in advance (*"The ready-actor snapshot is local to this transition. It
is deliberately not fixed globally across an arbitrary execution."*). Where the general family's τ sets
turn out empty, the two results coincide.

**Why this matters for the paper specifically.** F63's Part 1 found the project's headline claim
*understated* for what the tool accepts. This is the same direction one layer down: a contributions or
related-work section drafted from §7 item 6 would present whole-execution correspondence as new work for
stage G, when a narrower family already has it — either failing to cite the project's own result or
claiming novelty against it. Both readings are avoidable by naming the four modules, which §4 now does.

**The transferable check.** The claim "no such theorem exists yet" is an absence claim, and this file's
own provenance rule already says absence must be *"established by a described search"*. Neither §4's count
nor §7 item 6's "later" was; both were written from recollection of which modules stage G would touch,
which is a different set from which modules exist. Before a design document says a family lacks a result,
the search that would find it belongs in the entry.

---

## F66 — stage G's central deliverable was specified as one file, at a granularity that makes the paper's own relation vacuous, on a family that has no semantics to build it on

*Read.* Found before a single line of G2a Lean was written, in the pass whose only purpose was to confirm
the design's granularity choice against the precedent it named. The confirmation failed in seven separate
ways, and every one of them would have been discovered later and more expensively — five of them only after
a module had been written against the wrong plan. This is the counterpart to **F63**'s lesson at design
scale: the cheapest place to find a design defect is in the paragraph that says the design is settled.

### Part 1 — the general family has no operational semantics at all

`docs/STAGE_G_DESIGN.md` §7 specifies two transition relations,
`GeneralDtrStep sourceModel config action configAfter` and `GeneralLfStep program state action stateAfter`.
Neither can be stated, because nothing they are stated over exists.

| Ingredient §7 needs | General family | Every older family |
|---|---|---|
| Expression evaluator | **absent** | `Evaluation.lean`, `StoreEvaluation.lean`, `PayloadExpression.lean` |
| Statement semantics | **absent** | `DetailedMultiStorePayloadSemantics.lean` |
| Source step relation | **absent** | `DetailedMultiStorePayloadStep`, `ActorPriorityDispatchStep`, `Step`, `Steps` |
| Target runtime state | **absent** | `MachineSemantics.lean` (`MachineLabel`, `MachineStep`) |
| Weak/τ layer | **absent** | `DetailedMultiStorePayloadWeakSemantics.lean` (`SilentLabel`, `VisibleLabel`, `TauSteps`, `WeakStep`) |

Established by a described search, per this file's provenance rule. The general modules are exactly five
under `Relico/DTR/` — `GeneralActorSelection`, `GeneralPriority`, `GeneralState`, `GeneralSyntax`,
`GeneralWellFormed` — and exactly three under `Relico/LF/` — `GeneralCppPrinter`, `GeneralSyntax`,
`GeneralWellFormed`. A repository-wide grep for a declaration named `General…Step`, `…Trans`, `…Exec`,
`…Run`, `…Machine`, `…Label`, `…Action` or `…Event` returns one hit, and it is `LF.GeneralAction`, a syntax
structure (see Part 7). A grep for a general-family `eval` declaration returns nothing. `GeneralState.lean`
stops at the ready-cohort layer, and G1 added selection on top of it — the family reaches the point of
deciding *which* actor runs and has never said what running *is*.

### Part 2 — so §7's "one file, one Lake job" is really ten modules and ten jobs

§13's work-plan row read `| 3 | **G2a** Relico/Semantics/GeneralLTS.lean — both LTSs, the action type, the
τ classification | 1 | 514 |`. The honest decomposition, at the granularity Part 5 forces:

| Commit | Modules | Jobs |
|---|---|---|
| G2a-i | `Relico/DTR/GeneralEvaluation.lean`, `Relico/LF/GeneralEvaluation.lean`, `Relico/Correctness/GeneralEvaluation.lean`, `Relico/Tests/GeneralEvaluation.lean` | 513 → 517 |
| G2a-ii | `Relico/DTR/GeneralRuntime.lean`, `Relico/LF/GeneralRuntime.lean`, `Relico/Tests/GeneralRuntime.lean` | 517 → 520 |
| G2a-iii | `Relico/DTR/GeneralSemantics.lean`, `Relico/LF/GeneralSemantics.lean`, `Relico/Tests/GeneralSemantics.lean` | 520 → 523 |

**This table was itself one module short when first written, and is corrected above — see F67 part 5.**
G2a-i's fourth module is the `Correctness/` one, omitted because part 2 was written before part 3's
convention was applied to it: a theorem about `Translation.compileGeneralExpr` cannot live in either
language's module without inverting the dependency. The count below reads *ten* for the same reason.

Ten modules where the design named one, and ten Lake jobs where it predicted one. The stage's endpoint of
518/519 jobs is therefore void; the revision restates it as an estimate near **527** and moves the binding
prediction onto each commit's own row, which is where the project's prediction discipline can actually
check it.

Note what is *not* saved by retreating to the coarser granularity: **the evaluators are needed either way.**
A big-step dispatch rule still has to say what a message-server body did to the valuation, or the `e_x ≡ η_r`
component of the paper's `R` compares two things that never change. Granularity buys the continuation, the
small-step body relation and the τ classification — not the evaluator.

### Part 3 — `Relico/Semantics/` contradicts the repository's own layout

§7 names five deliverables under `Relico/Semantics/`. That directory does not exist, and the repository's
subdirectories are `Benchmark`, `Common`, `Correctness`, `DTR`, `Frontend`, `Investigation`, `LF`, `Tests`,
`Translation`. The convention those nine encode is consistent and load-bearing: **source semantics live in
`DTR/`, target semantics in `LF/`, and cross-language results in `Correctness/`.** No family has ever used a
`Semantics/` directory. Creating one would put the two step relations in a third place while the syntax they
are stated over stays in the first two, and it would put them somewhere no existing correctness module looks.
The five files are redistributed accordingly: the step relations to `DTR/` and `LF/` beside their syntax, the
correspondence and bisimulation results to `Correctness/`.

### Part 4 — the τ set was inherited from the paper's misnomer instead of read off Table II

§7 states that τ is *"assignments on both sides plus LF scheduler steps"*, and §14 built its highest-risk
prediction on the second half of that. **Table II has no scheduler rule.** Its seven rules are ASSIGN,
INTERNAL SEND, EXTERNAL SEND, TAKE, CONDITIONAL-T, CONDITIONAL-F and TIME PROGRESS. The paper's actual τ set
is ASSIGN, both send forms and both conditionals — and on the DTR side ASSIGN, SEND and both conditionals —
so the τ steps stand in bijection across the two tables and `τ*` has no surplus to absorb.

The design took that phrase from Theorem 1's proof, which says *"scheduler steps are internal to LF and have
no corresponding observable transition in DTR"*. The proof is reaching for a real gap and misnaming it. The
step with no DTR counterpart is the **microstep-only TIME PROGRESS**, which the paper labels `t`, observably.
That is a defect in the paper, filed as **P24**, and stage G adopts its repair — TIME PROGRESS split so that
a microstep-only advance is τ and a logical-time advance is `t`. Two consequences for this stage: the τ
classification G2a-iii writes is not the one §7 describes, and the divergence is the *third* one the stage
carries, so §10 and §15 both gain an entry.

The transferable point is narrow and worth stating: the design cited the paper's **prose** where it should
have cited the paper's **rules**, and the prose was the one place the paper is wrong. Trust order already
ranks the elaborating artefact above the narrative about it; Tables I and II are the artefact.

### Part 5 — dispatch granularity and a continuation component of `R` cannot both be kept

§4 chose to mirror the `GlobalMultiStorePayload*` development, which F65 established is strict lock-step:
*"one target event per source event, no internal steps, no τ."* That is dispatch granularity. §7
simultaneously commits `R` to the paper's three components, `e_x ≡ η_r ∧ b_x ≡ q_r ∧ π_x ≡ µ_r`. The two
commitments are incompatible, and the paper's own definitions say why:

- `π_x` is *"remaining statements of"* the executing message server;
- `µ_r` is *"remaining statements of the currently"* executing reaction;
- and **both** TAKE rules carry the premise that the continuation is `ε`, which is exactly what stops a new
  message being accepted mid-body.

At dispatch granularity the third component is permanently empty on both sides, `π_x ≡ µ_r` is trivially
true, and the stage would ship a relation that reproduces the paper's `R` in shape while one of its three
conjuncts does no work — then report it as Theorem 1. That is the failure mode this file exists to catch,
one level up from **F60**, where an assertion turned out invariant under the sort it was credited with
pinning.

So statement granularity is required. The measurement that settled it is that statement granularity is also
**available and symmetric**, which is not obvious and was the thing actually worth checking: `LF.GeneralStmt`
has three constructors including `assign`, `GeneralBody` is a statement list on both sides, and both families
now carry `GeneralType` and `GeneralValue` with identical `int : Int | bool : Bool` constructors. Had the LF
reaction body been opaque, fine granularity would have been impossible and the design's inherited choice
would have been forced rather than mistaken.

### Part 6 — no conditionals: a fragment restriction to declare, not a divergence

Tables I and II both carry CONDITIONAL-T and CONDITIONAL-F. Neither `GeneralStmt` has a conditional —
`DTR.GeneralStmt` is `assign | send`, `LF.GeneralStmt` is `assign | schedule | setPort` — and `GeneralBody`
is a flat list whose docstring already states that the stage admitting branching and iteration must change
the type so that every walker becomes a build error. So G2a's step relations simply have no conditional
rules, and what stage G proves is the **conditional-free sub-fragment**.

This is a restriction on the input, not a divergence from the semantics, and it is the right shape under the
standing doctrine that a limitation is declared rather than quietly absorbed. **G6** owns the declaration and
must state it there; a bisimulation theorem quantified over a body type that cannot branch says nothing about
one that can, and no reader should have to derive that from a constructor count.

### Part 7 — the design's name for the action type is already taken

§7 writes *"with `action : GeneralAction` carrying a `tau` constructor"*. `Relico/LF/GeneralSyntax.lean:534`
already declares `structure GeneralAction` — the LF **logical action declaration**, sitting between
`GeneralStateVariableDecl` and `GeneralTrigger`. Declaring an LTS label type of that name in the `LF`
namespace is a clash, and declaring it anywhere is worse than a clash: it would put "LF logical action" and
"LTS label" behind one identifier in a development whose whole subject is the correspondence between labels.
The revision therefore declares **two** label types rather than one, which the paper's own `ϕ : Act_1 → Act_2`
argues for independently — a bijection between two action sets needs two types, and collapsing them to one
would also erase the `map_A` / `map_M` naming content stages E and F built.

The names this part first proposed, `GeneralDtrAction` and `GeneralLfAction`, are **not** the names that
landed. G2a-ii declares `DTR.GeneralLabel` and `LF.GeneralLabel`; three measurements taken while writing the
modules forced the respelling, and one of them is that `GeneralLfAction` would not have removed the very
collision this part identifies, since it would have lived in `namespace LF` one word away from
`LF.GeneralAction`. Nothing in the argument above changes — there are still two types, still one per
language. `docs/STAGE_G_DESIGN.md` §13 carries the measurements, and
`Relico/DTR/GeneralRuntime.lean`'s module docstring carries them at the point of the decision.

### One dependency stated rather than assumed: the single store

The paper's TAKE rule sets the valuation to `e_x ∪ v⃗`, merging the message's parameters into the actor's
variable valuation. So one `Store VarName GeneralValue` serves both state variables and parameters, and
`DTR.GeneralExpr`'s separate `stateVar` and `parameterVar` constructors can both resolve in it. That is sound
**only because** a formal shadowing a state variable is already a well-formedness violation — the
`.parameterShadowsStateVariable` clause added in stage E. Without it, one store would silently let a
parameter overwrite a state variable of the same name and the evaluator would be wrong in a way no type
error catches. The evaluators must cite that clause as a precondition rather than inherit it by luck.

### Why this matters for the paper

Three of these seven parts change what the paper can claim. P24 means the paper's Theorem 1 as printed is
false of its own commonest idiom, and a corrected paper must either carry the split rule or restrict the
fragment to strictly positive delays. Part 5 means a formalization that transcribed the paper's `R` at the
wrong granularity would have supported a "we mechanised Theorem 1" claim that a referee could deflate in one
question. Part 6 means the fragment sentence in any theorem statement has to say *conditional-free*, and the
project has already been burned once — F63 — by a headline claim quantified over a fragment nothing declared.

### The transferable check

Every one of the seven was found by comparing the design against an **elaborating artefact** rather than
against the narrative that produced it: the file listing, the constructor lists, the two SOS tables, the
existing `GeneralAction` declaration. The design's own §14 asked "what would refute this plan" and answered
with one risk, which F64 then voided; none of these seven appear there, because §14 was written by asking
what might go wrong rather than by reading what is already there. **A design section that names a deliverable
should be checked against `ls` and `grep` before the stage it governs opens**, and the check costs minutes
against the several commits it saves.

---

## F67 — the general fragment's arithmetic is C++'s rather than chosen, division by zero is unguarded target undefined behaviour, and the correctness theorem is structurally unable to notice either

*Read* for the target semantics and for both absence claims; *inferred* for the undefined-behaviour
consequence, which names the fragment restriction that would settle it. Found while writing G2a-i's
evaluators — the first modules in the general family that have to say what an operator *computes* rather
than how it is spelled.

### Part 1 — the operator semantics was never a modelling choice

`LF.renderGeneralBinaryOp` emits `.div` as `"/"` and `.mod` as `"%"`, and its docstring already states why
those spellings needed no `lfc` probe: every operator "appears inside a `{= … =}` block where the text is
verbatim C++, so the spellings are guaranteed by the C++ standard rather than by anything about LF."

That argument is correct, and it proves more than it claims. The same standard that fixes the *spelling*
fixes the *arithmetic*: since C++11, integer division truncates toward zero and the remainder takes the
sign of the dividend. So the general fragment's `/` and `%` are not operators this development gets to
define — they are `Int.tdiv` and `Int.tmod`, and a model built on `Int.ediv`/`Int.emod` or on flooring
division would agree with the emitted program on non-negative operands and disagree at `(-7) / 2`, which
would make the correctness result a false statement about the artefact the tool produces.

### Part 2 — there was no in-repo precedent, so the choice had to come from the target

A repository-wide search for `Int.div`, `Int.mod`, `Int.tdiv`, `Int.tmod`, `Int.ediv`, `Int.emod`,
`Int.fdiv` and `Int.fmod` across `Relico/`, excluding the two new evaluator modules, returns **nothing**.
Five families of source semantics and four printers existed before stage G and not one of them ever divided
an integer: the older families' expression languages have `+`, `-` and `*` and stop there.

This is worth recording rather than filing as a triviality, because the project's usual safeguard was
unavailable. Every other operator in G2a-i could be checked against an existing definition; these two had
to be derived from the target's standard, and a wrong derivation would have been invisible to every
instrument the repository owns. Which is Part 3.

### Part 3 — the theorem that ought to catch a wrong choice cannot see it

`Correctness.compileGeneralExpr_preserves_evaluation` is a **relative** statement: it says the two sides
compute the same thing. Replace `Int.tdiv` with `Int.fdiv` and `Int.tmod` with `Int.fmod` in *both*
`DTR.GeneralBinaryOp.apply` and `LF.GeneralBinaryOp.apply` and every theorem in G2a-i still holds — the two
sides would still agree, and would simply agree on the wrong answer. The build stays green and the
development now contains a false claim about generated C++.

The only instrument that discriminates is a value pin at a **negative dividend**, because that is the sole
input class on which truncating and flooring division differ: `-7 / 2` is `-3` truncating and `-4`
flooring; `-7 % 2` is `-1` truncating and `1` flooring. `Relico/Tests/GeneralEvaluation.lean` therefore
pins all four values, on both sides, as **literals**.

Stating them as literals rather than as `Int.tdiv (-7) 2` is the load-bearing detail, and the reason is
already on the record: **F60** is an entry about an assertion that was invariant under the very sort it was
credited with pinning. An expected value written in terms of the function under test is a tautology that
holds under any definition of it. The general lesson is that a *correspondence* theorem between two models
can never establish either model's fidelity to a third thing — here, a C++ compiler — and only an absolute
pin can.

### Part 4 — a divide-by-zero program is well-formed, translated, printed, and undefined

Division by zero is undefined behaviour in C++. The evaluators return `none`, which makes both sides stuck
at the same statement and so keeps Theorem 1 true; `Correctness.compileGeneralExpr_evaluation_none_iff`
proves the failure corresponds. But being stuck is not what the emitted program does, so the correctness
result transfers to real target behaviour only on executions in which no division or modulo by zero occurs.

And nothing excludes such a program. `DTR.GeneralWellFormed` places no restriction on expressions at all —
it resolves the names an expression mentions and stops — so `x / 0` passes well-formedness, is translated,
is printed, and reaches `lfc`. The gap is not hypothetical or hard to trigger; it is one literal.

**This is where the project's target-fault doctrine applies, and where the current modules deliver only
half of it.** The standing rule is that when a limitation is the *target's* fault, dependent source models
go out of scope through a **checkable guard refusal plus a stated fragment restriction** — never through a
quietly narrowed theorem. G2a-i's module notes state the fragment restriction and hand its declaration to
G6. They do not propose a guard, and they should, because part of this defect *is* syntactically decidable:

- **Decidable, so it should be refused.** A literal zero divisor — `.binary .div e (.intLiteral 0)` and the
  `.mod` counterpart — is visible in the syntax tree. A well-formedness clause can reject it, and then a
  refusal test can pin the rejection, which is the shape every other target limitation in this project has
  been given since stage E.
- **Undecidable, so it belongs in the fragment restriction.** `x / y` where `y` is zero only on some
  execution cannot be refused without an analysis nothing here has. That residue is what G6 declares.

**Sequencing is a decision, not an inference, and it is flagged rather than taken.** Adding this clause
touches landed stage-E code and collides with **G3**, which is already scheduled to add a clause of its own
for a populated LF reaction priority. Two clauses arriving in either order both renumber the same list, and
**F49** is an entry about that exact hazard: its "ninth clause" prose is *positional*, so it must be
re-read at each addition rather than mechanically renumbered. Whether the divide-by-zero guard lands before
G3, after it, or is folded into G6 as restriction-only is left open here.

### Part 5 — F66's own work-plan table is one module short, and F66 states the rule that makes it so

F66 part 2 replaced §13's single-module `G2a` row with a three-commit decomposition, and gave G2a-i as
`DTR/GeneralEvaluation.lean`, `LF/GeneralEvaluation.lean` and `Tests/GeneralEvaluation.lean` — three modules,
513 → 516 jobs. Writing the commit showed it is **four**.

The missing module is `Relico/Correctness/GeneralEvaluation.lean`, and it is missing for a reason F66 itself
supplies. `Translation.compileGeneralExpr` is defined in `Relico/Translation/GeneralBasic.lean`, which
imports both languages; a theorem about it therefore cannot live in either language's module without
inverting the dependency. F66 **part 3** states the convention exactly — "source semantics live in `DTR/`,
target semantics in `LF/`, and cross-language results in `Correctness/`" — and part 2's table then omits the
`Correctness/` module that convention requires. The precedent it should have been read against is
`Relico/Correctness/ExpressionStore.lean`, which is the integer-only family's module of precisely this kind.

Two consequences beyond the count. The §7 deliverable list described G2a-i's two evaluators as "expression +
statement evaluation" on each side, which cannot be right under the reslice: statement evaluation needs the
continuation that G2a-ii introduces, so G2a-i is expression evaluation only. And every job number downstream
of G2a-i moves by one — the corrected chain is 513 → **517** → 520 → 523 → 525 → 526 → **527**, and the
stage endpoint estimate becomes **527**. Both documents are corrected in place; this part exists so that a
reader who finds the old numbers quoted elsewhere can tell which way the correction ran.

### Why this matters for the paper

Parts 1 through 4 are a fragment question, and the paper currently has no sentence for it. Any theorem
statement about the general fragment has to say *division-and-modulo-by-zero-free* alongside
*conditional-free*, or it claims correctness for programs whose target behaviour is undefined — and **F63**
is already an entry about a headline claim quantified over a fragment nothing declared. Part 3 is the
sharper point for a referee: a mechanised correspondence between a source model and a target model is
evidence about the translation and *no* evidence about either model's fidelity to the real compiler, so the
absolute pins are not test hygiene but part of the argument.

### The transferable check

**When a model's behaviour is dictated by an external standard rather than chosen, the correspondence
theorem cannot check it — so pin it absolutely, at an input where the plausible wrong answers differ.**
Choosing the input matters as much as writing the pin: every non-negative dividend makes truncating,
flooring and Euclidean division agree, so a pin at `7 / 2` would have looked like coverage while testing
nothing. The generalisation of F60 is that an assertion earns its place only if some specific wrong
implementation fails it, and it is worth naming that implementation when the pin is written.

---

## F68 — the AST fixes the absent-priority ordering convention for message servers only, and three sites credit it for actor priority as well

**Provenance:** parts 1–3 **measured** (`grep`/`sed` over the named files, 2026-08-24); part 4 **read**;
the repair **decided**, with the rejected alternative stated.

Filed here rather than in [`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md) because that file's header already
closes stage F's range at **F62** and directs the reader onward — *"F63 onward is in
`STAGE_G_FINDINGS.md`"* — so the pointer a reader follows from stage F lands here without a new
cross-reference. The subject matter is stage F's; the discovery is stage G's, made while verifying a cite
that stage G's authoring had flagged as suspicious.

### 1. What the AST actually says

Both priority fields exist and both default to absent — `DTR.GeneralMessageServer.priority : Option Nat
:= none` and `DTR.GeneralActorInstance.priority : Option Nat := none`. So absence is **representable**
for both. What is stated for only one is how absence **orders**.

`Relico/DTR/GeneralSyntax.lean:335-337` sits inside **`GeneralMessageServer`**'s docstring and opens by
naming its subject:

> *"`priority` is local message-server priority. An absent priority is a priority class in its own right
> and is ordered after every explicit one, which is the convention the earlier payload family already
> fixed."*

The second source usually cited beside it, `:385-386`, is the projection
`GeneralReactiveClass.messageServerPriorities` — message-server again.

`GeneralActorInstance`'s own docstring says only:

> *"`arguments` are the positional constructor arguments. `priority` is actor-level priority and is
> independent of message-server priority."*

It is **silent on absence**. Nothing in the AST says how an unannotated actor instance orders.

### 2. Three sites credit the AST for actor priority anyway

- **`Relico/DTR/GeneralPriority.lean:21`** — *"The convention is inherited, not chosen here."* plus
  *"discharges the paper's P5 … and the tie half of P4 at the AST level"*. This is the **generic**
  module, and its two instantiations are `GeneralActorPriority` and `GeneralMessageServerPriority`, so
  the claim covers actor priority.
- **`Relico/Translation/GeneralRouting.lean:1494`** — *"An unannotated **instance** is a priority class of
  its own … that convention is the AST's, at `Relico/DTR/GeneralSyntax.lean:335-337`"*. Explicitly about
  instances, cited to message-server text.
- **`docs/STAGE_F_DESIGN.md` §4.1** — lists **both** priority fields, then *"More importantly, the AST
  **already fixed the absence convention**, and stage F inherits it rather than choosing it"*, quoting
  only the two message-server sources. This is the load-bearing site, because the paper is drafted from
  these documents.

The control that shows the defect is scope rather than citation: **`Relico/Translation/GeneralBasic.lean:1723`**
makes the *same* cite to the *same* lines and is **correct**, because it speaks of an unannotated
*server*. One citation, four uses, three of them over-scoped.

### 3. Where the convention is really fixed

`DTR.GeneralPriority.PriorityPrecedesOrEqual`, a generic order on `Option Nat` with four arms
(`some/some` numeric, `some/none` true, `none/some` false, `none/none` true), whose docstring states it
directly: *"Explicit priorities compare numerically, every explicit priority precedes an absent one, and
two absences tie."* `GeneralActorPriority.priorityOf` merely projects `actor.priority` into it.

So for actor priority the convention is fixed by a **shared, type-checked definition** — which is
strictly better evidence than a docstring, and is the thing the design should have been claiming.

### 4. The module contradicted a rationale written five lines above it

`Relico/DTR/GeneralPriority.lean:14-19` argues against monomorphic copies on exactly this ground:

> *"§1.1 … argues that the two levels compose … **on the assumption that both use the same convention for
> an absent priority**. Two copies could drift on exactly that point, and the drift would be invisible …
> Sharing one definition makes the shared convention a type-checked fact instead of a comment."*

Two lines later the same docstring credited the AST with fixing the convention. The correct account was
already written immediately above the incorrect one — the same shape as **F53**, where three
"by construction" claims outlived the findings that refuted them, and as **F49**, where a docstring
argued away a clause it sat beside.

### Why this matters for the paper

**P5** (priorities may be absent) and the tie half of **P4** are genuinely discharged; the defect is
*where*. For actor priority they are discharged at the **sort** level, not the AST level. A paper
sentence sourced from §4.1 would therefore be false of one of the two priorities it covers — and, less
obviously, would **understate** the project's own guarantee, since one shared type-checked order is
stronger than two independently worded docstrings that could drift.

Stage F's own design corroborates that "already fixed" could not have been true of actor priority: the
paragraph directly beneath the corrected sentence records that `GeneralActorInstance.priority` was read
by *exactly one* place in the repository, *"inside a predicate that nothing enforces"*, and that level 1
introduced *"the first consumer of actor priority in the translation"*. A convention cannot have been
already fixed for a field nothing ordered.

### The repair, and the alternative rejected

The tempting repair is to **add** the absence sentence to `GeneralActorInstance`'s docstring, making all
three cites true. **Rejected:** five cites into `Relico/DTR/GeneralSyntax.lean` sit above line 407
(`:409`, `:422`, `:436`, and `:685` twice), so inserting lines at `GeneralActorInstance` shifts all five,
and this project's standing rule is that **no line-number arithmetic detects a stale Lean cite** — each
would need re-verifying, turning a two-docstring fix into a five-claim sweep.

Adopted instead: rewrite the two *citing* docstrings, **line-neutral**, so nothing moves. Verified after
editing — `GeneralPriority.lean` is still 1490 lines with `PriorityPrecedesOrEqual` still at `:55`, and
`GeneralRouting.lean`'s closing `-/` is still at `:1495` with the two filed unused-`simp` warnings still
at `:3790`/`:3796`. `docs/STAGE_F_DESIGN.md` §4.1 receives a **dated correction blockquote** beside the
original rather than a substitution, per the convention `docs/STAGE_G_DESIGN.md` §14 uses; safe to append
to because the only line-cites into that file are `:18`.

### The transferable check

**A citation can be accurate and mis-scoped at the same time, and only one of those is detectable by
re-reading the cited lines.** The quoted text really is at `:335-337`; it is simply about a narrower
subject than three of its four users needed. Line-number verification — the check this project runs
often — catches staleness and is *blind* to over-scoping.

So when a cite supports a claim about **two** things, check that the cited text mentions both; and prefer
citing the **declaration whose docstring states the convention, by name**, over a line range that merely
happens to contain the sentence. Here the honest cite is
`DTR.GeneralPriority.PriorityPrecedesOrEqual`, which needs no line number and cannot go stale.

---

## F69 — the design specified four already-proved definitions as new work, and the method that produced the error would have landed a second definition of the tag order

**Status:** corrected in `docs/STAGE_G_DESIGN.md` §7 and §13 before any of G2a-ii was built. No duplicate
declaration reached a commit.

### What the design said, and what the repository already had

`docs/STAGE_G_DESIGN.md` §13's work plan listed G2a-ii as delivering *"runtime state with continuations, the
superdense tag and `upd`"*, and §7's module table said *"runtime state, superdense tag, upd"*. Four of the
things that phrasing covers already existed, proved, since vertical slice v0:

| Design treats as new | Already exists | Where |
|---|---|---|
| the superdense tag | `structure LF.Tag` with `time` and `microstep` | `Relico/LF/State.lean` |
| `upd` | `LF.Tag.schedule`, with `schedule_zero`, `schedule_positive`, `schedule_time` | `Relico/LF/State.lean` |
| the tag order | `LF.Tag.PrecedesOrEqual`, lexicographic, plus five companion lemmas | `Relico/LF/Scheduling.lean` |
| that `upd` never moves a tag earlier | `LF.Tag.precedesOrEqual_schedule` | `Relico/LF/PendingNotPast.lean` |

`Tag.schedule` is not merely tag-shaped — it **is** P24's `upd`, branch for branch: a zero delay keeps the
time and advances the microstep, a positive delay advances the time and resets the microstep to zero.

### What is genuinely missing, and why it is missing

`LF.Tag.PrecedesOrEqual` has no `Decidable` instance, no transitivity and no totality. Verified absent under
any name rather than absent from one file.

The reason is the interesting part, because it says which obligation owes them. Every existing consumer —
thirty-three modules use the order, in `LF`, `Correctness` and `Tests` alike — proves **one specific
inequality**: this pending action is not before the current tag, that microstep cannot precede this one.
None of them **computes a minimum**. A scheduler does,
and a scheduler needs exactly those three: decidability to compute, totality to know a minimum exists,
transitivity to know the computed one is least. So the gap is real but narrower than the design implied,
and it is scheduler-shaped rather than tag-shaped. G1 needed the same three facts about its *source*-side
order one obligation earlier and declared them there; G2a-ii is the target-side other half.

### The method error, which is the transferable part

The false claim was not a slip. It was reached as a **load-bearing docstring argument**, by reading
`namespace Tag` in `Relico/LF/State.lean`, counting its declarations, and concluding that the block contains
exactly four — `schedule`, `schedule_zero`, `schedule_positive`, `schedule_time` — none of which compares two
tags, and therefore that the tag order did not exist. Every step of that is **true of the file and false of
the type**. `namespace Tag` is opened in four separate files besides the one this obligation
adds — `State.lean`, `Scheduling.lean`, `PendingNotPast.lean`, `PriorityTimingInvariant.lean` — and the
last two exist precisely to add tag lemmas from outside the declaring module. `Relico/LF/Scheduling.lean`'s
block holds `PrecedesOrEqual` and five companion lemmas.

Acting on it produced a draft of `Relico/LF/GeneralRuntime.lean` that declared a parallel `TagPrecedesOrEqual`
with the same lexicographic body as the landed `LF.Tag.PrecedesOrEqual`, together with lemmas restating
`precedesOrEqual_schedule` and `precedesOrEqual_refl`. That draft was never written to disk — it was replaced
during authoring, so unlike most findings here **this one has no in-repo witness**, and the description of it
is testimony rather than measurement. What is measurable is the state that survived: the landed module reopens
`namespace Tag` and declares only the three facts that were genuinely absent. The defect avoided is the one
this development keeps finding in its own history — two definitions of one convention, free to drift, with
nothing type-checked holding them together — and it would have been introduced here by the module whose
whole job is to *reuse* the target's tag.

It was also drift against a measurement the project had already made and written down. G1's own module
docstring in `Relico/DTR/GeneralActorSelection.lean` **cites `LF.Tag.PrecedesOrEqual` by name** as the
shape `DTR.GeneralActorSelection` mirrors. The information needed to prevent this was one file away, in
text written by the immediately preceding obligation.

### The transferable check

**A type's API is not the block that declares it.** Before declaring anything, grep the **qualified name**
repository-wide (`Tag.PrecedesOrEqual`, not `PrecedesOrEqual`) and grep `^namespace <Type>` for every place
the namespace is reopened. Reading the declaring file is necessary and not sufficient.

The corollary matters as much as the check: because reopening a namespace from a later module is this
repository's established convention, the right repair for a genuinely missing lemma is to **reopen the
namespace where it is needed** — never to declare a parallel name in a parallel namespace. G2a-ii adds its
three facts inside `namespace Tag`, leaving every existing call site untouched.

There is a second, cheaper smell worth naming: a new identifier that gets **zero** grep hits outside the
file introducing it is suspicious in a corpus this size — either it is genuinely new, or it is a second
spelling of something that already has a name. That check is what caught F70.

---

## F70 — the weak-transition machinery stage G plans to build is already generic and already proved, and its signature silently constrains the label types G2a-ii declares

**Status:** consumed while authoring G2a-ii. Two declarations in the new runtime modules were changed
before any build as a direct result.

### What exists

`Relico/Common/WeakTransition.lean` is a 400-line, universe-polymorphic, **family-agnostic** weak-transition
foundation. It is parameterised on an arbitrary `LabeledTransition State Label` and an arbitrary
`isTau : Label → Prop`, and it already proves what stage G's §7 describes as work to be done:

* `TauSteps`, the reflexive-transitive closure of τ steps, with `single` and a proved `trans`;
* `WeakStep`, with its `tau` and `visible` constructors, plus `of_tauSteps`, `of_step` and `tau_refl`;
* `observableProjection project trace = List.filterMap project trace`, with `_nil`, `_cons_none` and
  `_cons_some` as `@[simp]` lemmas.

This is a level below **F65**, which found aims 8 and 9 already proved *twice* for the multi-store family.
F65's two proofs are instances; this is the generic layer they instantiate. So G2c and G2d should
instantiate `Common.WeakStep` and `Common.observableProjection` rather than restate either, and G2d's
"generic" file in the work plan is generic over a foundation that is *already* generic.

### The constraint that was not visible from the design

The signature is not neutral about how G2a-ii declares its labels. `TauSteps` and `WeakStep` both take
`isTau : Label → Prop`. A draft of both runtime modules declared `isSilent : GeneralLabel → Bool` with
three `@[simp] rfl` lemmas — which would have needed a coercion at every use in G2c and would have become
a second spelling of one convention, the F69 defect again in a different place. Both were changed to
`isTau : GeneralLabel → Prop` returning `True`/`False` by pattern match, which is also the built house
idiom: `Relico/Tests/WeakTransitionFoundation.lean` declares exactly that shape as `exampleIsTau`.

Two consequences follow that a reader of the design would not predict:

1. **No `Decidable` instance on `isTau` is owed.** `Common.WeakStep.of_step` reaches for `classical` before
   splitting on `isTau`, so the generic development already handles an undecidable τ predicate. This is the
   opposite of the tag order, where decidability is exactly what F69 says is owed — the two look alike and
   are not.
2. **A projection is owed that the design never mentions.** `observableProjection` needs
   `project : Label → Option Observable`; the draft declared no such function on either label type. Both
   now declare `project`, with the label type itself as the observable alphabet, following `exampleProject`.

`Relico/Tests/GeneralRuntime.lean` pins both projections **through** `Common.observableProjection` rather
than in isolation, so the pins assert the composition and not merely the values — if a future edit changed
either `project`'s type, those two pins stop compiling.

### A second τ convention exists, and it is the one not to follow

`Relico/DTR/DetailedMultiStorePayloadWeakSemantics.lean` and its LF counterpart classify τ with Prop-valued
**inductives** — `DetailedMultiStorePayloadSilentLabel`, `…VisibleLabel`, one constructor per label case —
rather than with a function into `Prop`. Both conventions are live and landed. The general family follows
`Common.WeakTransition`'s function shape, because that is the one the generic machinery consumes; the
inductive shape would have to be bridged to it.

### The transferable check

**Before building the shape a design names, grep for the shape's *signature*, not just its name.** The
design said "weak bisimulation" and the repository had `WeakStep` — but the finding that mattered was not
that a similar thing existed, it was that the existing thing's **argument types** dictated two declarations
in a module three obligations earlier. A generic foundation constrains its future callers, and that
constraint is invisible from any document that describes the foundation only by what it proves.

---

## F71 — a naming correction was applied to the identifiers that prompted it and not to their neighbours, and two adjacent claims went stale under the same edit

*Read.* Found while reading `docs/STAGE_G_DESIGN.md` §7 for the names G2a-iii's two step relations should
carry — that is, by going to the design to be told what to build, and finding it told me two different
things. Repaired in the design before any G2a-iii Lean was written. Nothing was built against the rejected
spelling, so this cost a measurement rather than a module.

### The correction that stopped halfway

F66 part 7 rejected `GeneralDtrAction` and `GeneralLfAction` for the two label types, and the reason it gave
was general: the `Dtr`/`Lf` infix *"is redundant inside `namespace DTR` and `namespace LF`"*, and one name in
two namespaces is the house convention. That reason does not mention labels. It is a claim about namespacing,
and it applies verbatim to any identifier the two families both declare.

Yet §7 continued to specify the two step relations as `GeneralDtrStep` and `GeneralLfStep`, in a paragraph
sitting eleven lines above the one that explains why the infix was wrong for labels. The design therefore
argued against a convention and specified it in the same section.

Measured before repairing, because "the corpus prefers X" is the kind of claim this project has been wrong
about twice: **the repository contains twenty-two step inductives declared on both sides, and not one carries
a `Dtr` or `Lf` infix.** They are one name in two namespaces, without exception —
`DTR.DetailedMultiStorePayloadStep` and `LF.DetailedMultiStorePayloadStep`, `DTR.MultiStoreStep` and
`LF.MultiStoreStep`, and in `DTR/Semantics.lean` and `LF/Semantics.lean` a bare `Step` on each side. So the
names that land are `DTR.GeneralStep` and `LF.GeneralStep`, and `GeneralStep` was free: it had zero hits
repository-wide before this obligation.

### Two neighbouring claims that went stale under edits that did touch the paragraph

The same §7 sentence at the earlier site carries two more errors, and both are informative because the
paragraph *was* revised — twice — without either being noticed.

First, it reads `GeneralDtrStep sourceModel config action configAfter`, with `action` where the later
paragraph already says `label`. The label renaming was applied at the site where the renaming was decided
and not at the site that merely *uses* the name, which is the identical failure mode one level down.

Second, and more consequential because it is a claim about behaviour rather than spelling: it says the
relation *"obtains the cohort internally as `GeneralConfiguration.readyActors config`"*. That was true when
the relation was to range over `GeneralConfiguration`. G2a-ii introduced `GeneralRuntimeConfiguration`, which
carries continuations, so `config` is no longer a `GeneralConfiguration` and `config.readyActors` does not
typecheck. The correct expression is `config.erase.readyActors` — and `erase` exists precisely so that this
inheritance works, as its own docstring in `Relico/DTR/GeneralRuntime.lean` says. The claim was falsified by
a *different* obligation's design decision, one section away, on the same day.

### What was deliberately left alone

`docs/STAGE_G_FINDINGS.md` F66 part 1 also contains `GeneralDtrStep … action …`, and it is **not** repaired.
That sentence records what the design specified at the time F66 was written; editing it would rewrite the
record of a past state to match the present one, which is the opposite of what a findings file is for. The
two files have different jobs: the design says what will be built and must be true now, the findings say what
was found and must stay true of then. Note that F66's text preserves `action` while the design has moved to
`label` — that divergence is the mechanism working, not a defect.

### The check was run, and it is noisy — here is how to read its output

`grep -rnE 'General(Dtr|Lf)[A-Z]'` over every `.lean`, `.md` and `.sh` in the repository returns about
seventy lines. Four of them mattered. A reader who runs this check and starts editing will do damage, so the
classification is recorded here:

* **Roughly fifty hits are `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`**, cited by path from
  documents and docstrings all over the corpus. That is a landed *file* in the bridge harness, not a type in
  `namespace LF`, and it has no `GeneralDtrPrinterTestMain` counterpart — the convention F66 part 7 settled is
  about identifiers the two families **both** declare. Out of scope; renaming it would churn fifty citations
  to fix nothing.
* **A dozen are the rejected names quoted inside the explanations of why they were rejected** — in
  `Relico/DTR/GeneralRuntime.lean`, `Relico/LF/GeneralRuntime.lean`, `docs/STAGE_G_DESIGN.md` §7's
  respelling paragraph, and F66 part 7 itself. Those must stay: an argument against a name has to be able to
  print the name.
* **One is a type that was never built.** `docs/STAGE_C_DESIGN.md` mentions a `GeneralLfState` in a sentence
  explaining that stage C declined to invent one. It has exactly one occurrence repository-wide, nothing
  declares it, and the role it would have filled is now `LF.GeneralRuntimeState`. Left as written, because a
  correctly-recorded decision *not* to build something is not a false claim, and a hypothetical name cannot
  be misspelled.
* **The four that mattered** are `docs/STAGE_G_DESIGN.md:168` and `:395–396`.

### The transferable check

**A naming decision is a decision about a convention, so grep the convention, not the identifier.** After
settling that `Dtr`/`Lf` infixes are wrong, the check owed was `grep -nE 'General(Dtr|Lf)[A-Z]'` across every
document and module — not an edit to the two names under discussion. The same check, run once, would have
caught both the step relations and the stale `action`. Run it, but classify before editing: on this corpus its
signal-to-noise is four in seventy.

And the corollary, which is the sharper half: **a design paragraph that names a type is a claim that decays
when a neighbouring obligation renames the type.** `readyActors config` went false because G2a-ii introduced
a richer configuration type, not because anyone edited the sentence. So the sweep after introducing a new
state type is not "which modules mention it" — those do not exist yet — but "which documents describe code
that will now be written against something else".


---

## F72 — `omega` is blind to the `LogicalTime` abbreviation, so two fields of one structure behave differently in one proof, and G1's proofs are not the precedent they appear to be

**Provenance:** the tactic behaviour **measured**, from the diagnostics of the first `lake build` over the
G2a-ii modules, 2026-08-24 — five failures whose messages enumerate the constraints the tactic collected. That
transcript is a terminal capture and is **not** a file in this repository, so the reproduction instruction is
below rather than a path. The three declarations the explanation rests on are **read**, at cited lines. The
repair is **decided**; the alternative that was not taken is named, and the reason it was not taken is that it
would have required a measurement this obligation did not need to make.

`LF.Tag` has two fields, declared in `Relico/LF/State.lean`:

```lean
structure Tag where
  time : LogicalTime
  microstep : Nat
```

`LogicalTime` is `abbrev LogicalTime := Nat`, at `Relico/Common/Time.lean:10`. The two fields are therefore
the same type. **`omega` does not treat them as the same type.** A hypothesis or goal whose comparison is at
`LogicalTime` is silently ignored; the identical comparison at `Nat` is used.

### The measurement

G2a-ii's target-side runtime module owes a `Decidable` instance, transitivity and totality for
`Tag.PrecedesOrEqual`, whose body is
`left.time < right.time ∨ (left.time = right.time ∧ left.microstep ≤ right.microstep)` — one comparison per
field. Written with `omega` discharging the arithmetic, five goals failed across the two theorems, and
`omega`'s own diagnostics name the cause without ambiguity, because it prints the constraints it collected:

* Where the branch had only time facts in context — `left.time < middle.time` and `middle.time < right.time`,
  concluding `left.time < right.time` — the message was **"No usable constraints found."** Two usable
  hypotheses were in scope and none was seen.
* Where the branch mixed the fields, every collected atom was a microstep. Concluding `left.time < right.time`
  from `left.time < middle.time` and `middle.time = right.time`, alongside an incidental
  `middle.microstep ≤ right.microstep`, `omega` reported a counterexample over
  `a := ↑right.microstep, b := ↑middle.microstep` only. The two time hypotheses and the time goal contributed
  nothing.
* The reverse case is the control, and it is decisive. In the totality proof one time fact **was** collected —
  `a - b ≥ 0` over `a := ↑left.time, b := ↑right.time` — while `¬ (left.time = right.time)`, in the same
  context, was not. The collected one had been produced by `Nat.lt_or_ge left.time right.time`, so its type is
  literally `Nat`; the ignored one was written directly as a comparison of two `.time` projections, so its type
  is `LogicalTime`. Same two terms, same proof, one visible and one invisible, discriminated by nothing but
  which type the comparison was elaborated at.
* Two `omega` calls in the same theorems **succeeded** throughout: both had `microstep` goals.

The control has an exact counterpart on the source side, and it is the sharpest single item here.
`DTR.GeneralActorSelection.precedesOrEqual_total` splits with
`by_cases hTime : left.logicalTime = right.logicalTime` and closes its second branch with `Or.inl (by omega)`
at `Relico/DTR/GeneralActorSelection.lean:336` — an `omega` call that **needs** the negated equality `hTime`,
because `Nat.lt_or_ge` alone leaves it only `left.logicalTime ≥ right.logicalTime` and the goal is strict. That
call is green. Transcribed to `LF.Tag` it is the call that failed, in the same position, in the same proof
shape, on the same two hypotheses. Nothing distinguishes them but the field's declared type.

What is measured here is the behaviour, not `omega`'s implementation. Whether the mechanism is the atom
collector declining to reduce a reducible definition, or something about the instance argument, was not
measured and is not claimed. Nor was it measured whether a `show`, a `simp only`, or a `Nat`-typed
restatement could restore visibility — that is the alternative repair, and it was not taken because it costs
a measurement to establish and the explicit-lemma repair costs none.

**To reproduce:** in `Relico/LF/GeneralRuntime.lean`, replace the `Or.inl` argument of any one of the first
three branches of `Tag.precedesOrEqual_trans` — those are the three whose goal is a time comparison — with
`by omega`, and build. The failure is immediate and the message lists the atoms. The fourth branch is **not**
a witness: its arithmetic component is a `microstep` goal, so `omega` closes it.

### Why G1 is not the precedent

The source-side counterpart, `DTR.GeneralActorSelection.precedesOrEqual_trans` and `…_total` (obligation G1,
landed at `cc7b0c7`), proves the same two facts about the same lexicographic shape and uses `omega` freely —
`Or.inl (by omega)` on three of four branches. It is green. It was read before writing the target side
precisely *because* it was green, and its proof structure was mirrored deliberately.

The mirror does not hold, and the reason is one word in a declaration. G1's structure is `ReadyActor`, in
`Relico/DTR/GlobalMultiStorePayloadActorPriority.lean:24`, whose field is `logicalTime : Nat` — bare `Nat`,
not `LogicalTime`. The second `ReadyActor`, in `Relico/Investigation/ActorPriority/IsolatedScheduler.lean:15`,
also declares `logicalTime : Nat`. **No `omega` call on the source side has ever been handed a
`LogicalTime`-typed hypothesis.** G1's greenness is therefore evidence that the proof *shape* is right, and no
evidence at all about the tactic, which is the part that was being borrowed.

This is the same defect as the missing `Relico.Common.Store` import in the same obligation, one level up: a
property of the precedent was verified, and it was not the property being relied on. Existence is not
reachability; a green proof of the analogous statement is not a green proof at the analogous type.

### The repair

Both theorems now avoid `omega` on any time comparison. `precedesOrEqual_trans` closes its four branches with
`Nat.lt_trans`, `Nat.lt_of_lt_of_le`, `Nat.lt_of_le_of_lt` and `Nat.le_trans` — explicit terms, which
typecheck up to reducible unfolding and so are indifferent to the abbreviation. `precedesOrEqual_total`
deliberately does **not** copy G1's `by_cases` on time equality, because that tactic manufactures exactly the
invisible hypothesis; it splits twice with `Nat.lt_or_ge` and recovers the tie with `Nat.le_antisymm`. One
`omega` survives, on the sole genuinely `Nat`-typed goal. Both docstrings state the constraint and cite this
finding, so that the next reader does not re-derive it from five error messages.

### Scope, and why this is not merely a tactic note

Every remaining stage G obligation reasons about tags. G2a-iii owes the time-progress rule and P24's
zero-delay split; G2b owes Lemma 1, which relates `LF.GeneralRuntimeState.now` — a `.time` projection — to
`DTR.GeneralConfiguration.now`; G2c and G2d owe the transfer conditions and trace agreement over the same
projection. Each will present `omega` with `LogicalTime`-typed goals, and `omega` will not refuse them
loudly — it reports a counterexample, which reads like a false statement rather than an invisible hypothesis.
That failure mode is the finding's cost: it sent three wrong diagnoses ahead of the right one.

### The transferable check

**When a tactic reports "no usable constraints" or a counterexample over a strict subset of the hypotheses in
scope, read the list of atoms it printed before rereading the proof.** The list is a direct statement of what
the tactic could see. Here three messages named microsteps and no times, and a fourth named nothing at all,
which identified the discriminating field immediately — and that information was already on disk during three
successive wrong hypotheses, because the command that produced it printed only the error *line numbers* and not
the error text. A diagnostic that is captured but not printed is not evidence.

The corollary for borrowed proofs: **before mirroring a green proof, check the types of the fields it reasons
about, not just the shape of the statement.** `logicalTime : Nat` beside `time : LogicalTime` is invisible at
the level of statements — both read as "a lexicographic order on a time and a tie-breaker" — and decides
whether the tactic in the borrowed proof works at all.

## F73 — two docstring claims in one obligation were checked by nothing, and the instrument that would catch the class reports six false positives

**Measured 2026-08-24, during G2a-iii (row 6 of twelve), before its first build.** Three defects with one
root: in each case a claim's *checkability* was assumed rather than established. Two were in text this
obligation authored; the third was in the audit I wrote to look for the first two, and it is the one that
nearly produced a false finding.

### Part 1 — the weak-transition instantiation was claimed by two modules and checked by neither

`DTR.GeneralStep` and `LF.GeneralStep` each carry a docstring stating, and citing **F70**, that G2c may
**instantiate** `Common.TauSteps` and `Common.WeakStep` at the relation rather than restate either, and that
the `State → Label → State` index order was chosen for exactly that reason.

Grepping `WeakStep`, `TauSteps` and `isTau` across both modules returns **only docstring lines** — two in the
source module, one in the target module, zero lines of code. The claim is true, and it was worth writing down,
but nothing established it. `Common.WeakStep.of_step` had never been applied at either relation; neither
relation had ever been offered to `Common.LabeledTransition` as an inhabitant.

This is the shape [`STAGE_E_FINDINGS.md`](STAGE_E_FINDINGS.md) F53 records — a "by construction" claim that
outlives the finding refuting it — with the tense changed. F53's claims were about the past and had been
falsified. This one is about a future stage, so it cannot be falsified yet, and that is what made it
comfortable to leave unchecked. **A claim about work three obligations away is not deferred verification; it
is unverified text that reads like verified text.**

The generic machinery was already fully proved and generic before stage G began — that is F70's content — so
there was never a cost argument for deferring. The instantiation is five lines per relation.

### Part 2 — a citation took the right namespace from the wrong neighbour

`LF.GeneralStep.tau_pending_not_past`'s docstring cited `LF.Tag.PendingNotPast.append_one`. The theorem is
`LF.ActionQueue.PendingNotPast.append_one`: in `Relico/LF/PendingNotPast.lean`, `namespace Tag` closes and
`namespace ActionQueue` opens two lines later, and `PendingNotPast.append_one` is inside the second.

The wrong prefix was the *right* prefix for the other citation in the same sentence. That proof reaches for
two theorems from that one file — `LF.Tag.precedesOrEqual_schedule`, which genuinely is in `Tag`, and
`append_one`, which is not — and the `Tag.` that belonged to the first was carried onto the second. A reader
looking for the cited name finds nothing and has no way to tell whether the theorem was renamed, moved, or
never existed.

The same docstring also claimed the proof follows `append_one` "step for step". Measured against it: the
`simp only [List.mem_append, List.mem_singleton]` and the `rcases … with hExisting | hAdded` are indeed
identical, and then the two **diverge at the final line** — `append_one` closes the added case with the
ordering premise it was *given* as `hNew`, while the general version has no such premise and *derives* the
ordering from `precedesOrEqual_schedule`. That divergence is not a detail: it is the whole reason the
general statement can be proved one rule at a time while the full invariant needs a six-rule induction. The
overstatement flattened the one interesting thing about the proof.

### Part 3 — the audit instrument is format-blind, and the findings series has two formats

To look for more of Part 2's defect I wrote the obvious check: collect every `F`/`P` number that has a record
heading in `docs/`, collect every such number cited from Lean, and difference them. It reported **six dangling
citations** — F22, F23, F25, F27, F28 and F29, across ten sites in six modules, one of them the module this
very obligation authored.

**All six are false positives.** Every one is recorded, in
[`STAGE_D_FINDINGS.md`](STAGE_D_FINDINGS.md), as a **bold paragraph lead** (`**F22 — …**`) under a single
grouped range heading, `## F21–F29 — carried over from the design, with their status after implementation`.
Format census over the series as it stood when this entry was written: **eighty-seven of the then
ninety-six `F`/`P` records use one heading each; nine — stage D's entire set — use the grouped form.** A
format-aware re-run reports **zero** dangling citations. The
repository is sound; the instrument was not.

What makes this worth a finding rather than a shrug is that the artefact was *plausible*. The range heading
`## F21–F29` matched the naive pattern well enough to yield exactly one number, F21, so the recorded set read
as a clean run F1–F21 and then a jump to F30. A gap at precisely F22–F29 is believable to anyone who has read
`STAGE_D_FINDINGS.md`, because that file documents a renumbering — the design's own `D1–D9` became `F21–F29`
at review, and it records a second pass in which three findings were cited under wrong numbers and had to be
corrected. An instrument artefact landing exactly on the range with a renumbering history is the most
convincing possible false positive, and it was two keystrokes from being written up as eight missing records.

The real defect underneath is structural and is **F54**'s lesson one level up: **a record that no
structural index can see is reachable only by full-text search.** F54 was about a finding invisible from
where a reader looks, and it cost a duplicate task. Here nine findings are invisible to any heading-level
outline — an editor's document map, a generated table of contents, and any future automated citation check.
`grep` still finds them; nothing else does.

### The repair, and one repair deliberately not made

Part 1: five pins in `Relico/Tests/GeneralSemantics.lean`, each failing under a different specific mistake.
Two offer each relation to `Common.LabeledTransition` — a *declaration*-level check, the only pin here that a
wrong index order breaks. One closes the microstep advance into `Common.TauSteps` via `TauSteps.single`, which
demands `isTau label` as a **proposition** and so fails against a `Bool`-valued `isTau` — the shape a reader
arriving from `GeneralTrigger.matchesKind` next door would reach for. One absorbs that advance into a
`Common.WeakStep` at an internal label, which is **P24** at the weak level: the target may
take that step and a bisimulation may match it with nothing at all on the source side. Two more build the
observable time steps, one per language.

Those last two use the `WeakStep.visible` **constructor** rather than `Common.WeakStep.of_step`, deliberately.
`of_step` decides the two cases with a classical `by_cases` on the τ classification, so it elaborates
*whichever way that classification goes* — it is invariant under the very thing being pinned, which is
**F60**'s disqualifying property. `visible` takes `¬ isTau label` as an argument, so a τ
set that wrongly swallowed `timeAdvance` fails those two pins and nothing else in the repository would
notice. **F60's standard applies to a proof term exactly as it applies to a `decide`.**

Part 2: both defects corrected in place, and the docstring now names the namespace trap explicitly and states
where the two proofs diverge rather than claiming they do not.

Part 3: the instrument is recorded here in its format-aware form. **Stage D's grouped block is deliberately
not reformatted.** `STAGE_D_FINDINGS.md` documents what a renumbering pass over that exact block already
cost — three findings cited under wrong numbers, caught only by re-reading the design — and the citations into
it are live in six built modules. Trading a real risk of breaking live citations for an aesthetic consistency
gain is the wrong trade. The two formats are now written down, which is what makes the difference navigable.

### The transferable check

**A claim about what a future obligation will be able to do is checkable now, and costs less now.** If a
docstring says a later stage can instantiate, reuse, or extend something, the cheapest possible instance of
that instantiation belongs in the same changeset. It is not extra work brought forward; it is the difference
between a design note and a verified one, and it converts a defect discovered three obligations later into an
elaboration error discovered on the first build.

**When an audit reports a cluster of failures that falls exactly on a range with known history, suspect the
instrument before the repository.** Real defects of this kind are scattered, because they come from
independent authoring mistakes. A contiguous block is the signature of a format the instrument does not
recognise. The cheap discriminator is to check one alleged failure by hand, full-text — which is what turned
six missing records into one broken regex.

**And cite a Lean declaration by its full name, read from the file, including the namespace it is actually
in.** Two namespaces adjacent in one file, both containing a name the same proof uses, is enough to move a
prefix from one citation to its neighbour. No line-number arithmetic and no build failure detects this: the
proof was green throughout, because a docstring is not type-checked.

---

## F74 — the source's time rule advanced to *any* later time, which makes false the one lemma the next obligation exists to prove

**Measured 2026-08-24, while deriving row 7's obligations (G2b, task #105) from the two relations row 6 had
just landed — before a line of row 7 Lean was written.** Two defects with one root, and the root is that
*"earliest"* was a name in this development long before it was a theorem. Repaired in the same changeset as
this entry, on the **source** side, which is the side that was wrong.

Grades: Part 1 **read**, Part 2 **inferred** (with a witness exhibited in Part 1), Part 3 **read**, Part 4
**measured**, Part 5 **read** (absence established by a described search), Part 6 **decided**, Part 7
**decided**, and Part 7 leaves one question for the user rather than answering it.

### Part 1 — the two time rules were not each other's mirror, and quiescence did not make them one

`DTR.GeneralStep.timeProgress` shipped with exactly two premises:

```
(hForward   : config.now < future)
(hQuiescent : DTR.GeneralConfiguration.readyActors config.erase = [])
```

`future` is an implicit binder and nothing else mentions it. `LF.GeneralStep.timeAdvance` instead premises

```
(hSelected : GeneralRuntimeState.earliestPendingEvent? state = some event)
(hForward  : state.currentTag.time < event.tag.time)
```

so the target may only land on the tag of an event that is actually in its queue, and the source could land
anywhere later at all.

**Quiescence looks like it closes this and does not.** `readyActors` reaches `readyActorsOf`, then
`GeneralActorState.dueArrival`, then `DTR.earliestDueArrival` — and that function inspects only messages
with `arrival ≤ now`. Its `none` therefore means *"nothing due"*, never *"nothing pending"*. A bag holding
one message arriving at 5 with `now = 3` is quiescent by that measure, so the rule admitted

```
now = 3  →  now = 100
```

with the message still sitting unconsumed in the bag afterwards, at an arrival the clock had already passed.
The two premises read the same bag over two ranges that do not meet: quiescence covers `arrival ≤ now`, and
the constraint that was missing covers `now < arrival`. Neither range constrains the other, which is exactly
why adding the second premise makes the rule strictly harder to apply and why its absence was invisible.

### Part 2 — what it broke was row 7's own obligation

Row 7 *is* Lemma 1: source logical time equals the logical-time component of the target tag, carried along
the correspondence relation. The step above refutes it directly — the source reaches 100 while the target,
holding the corresponding event at 5, cannot go past 5 — so the lemma was false of the relations as landed,
not merely unproved.

It also broke Definition 1's **forward** transfer condition, which is the direction G2c needs: a source step
existed with no target step to match it. Worth stating plainly, because the forward direction is the one a
reader is tempted to wave through as the easy one.

Had the repair not been made, Lemma 1 could still have been *stated and proved* — by adding a hypothesis
constraining `future`, or by quantifying the source's `future` existentially and choosing it to be the
target's event time. Both were considered and both are hiding rather than fixing: the transfer condition
quantifies over **all** source steps, so choosing a convenient witness leaves the inconvenient steps
unmatched and the theorem's scope quietly narrower than its name. The standing rule for this repository is
that a scoped theorem is the honest answer when the **target** is at fault and the input should be refused;
it is not the answer when our own transcription of the source is the loose one. Here it was.

### Part 3 — the paper is right, our own corrections file had already transcribed it right, and every other family in the repository does it right

This is a **repo** defect, not a paper one, and it is worth being explicit about that because the P series
had been the busier of the two in this stage.

The paper constrains the advance in both places it discusses it. Lemma 1's time-progress case reads *"When no
untimed transitions are enabled, DTR applies the time progress rule and advances logical time to the minimum
message arrival time `ar_min`"*, and Theorem 1's time case opens *"Suppose in DTR time progresses to the next
message arrival `ar_min`"*. Table I's TIME PROGRESS premise defines `ar_min` as a minimum over the bags. Both
sentences are transcribed from the PDF for this entry; the subscript renders as `armin` in extracted text.

`docs/PAPER_CORRECTIONS.md` had already transcribed it correctly, before the general step relation existed:
**P24**'s dependency note writes *"TIME PROGRESS sets `now := ar_min` where `ar_min` is the minimum arrival in
any bag"*, and uses exactly that to argue that an arrival equal to `now` must enable a take. P24 landed at
task #113 and the general step relation at task #117, so the correct rule was in our own documentation, in
prose, four tasks before the Lean that contradicts it — and the Lean was written without consulting it.

**And every other family in the repository already ties its time advance to a selection, on both sides.**
`DTR.DetailedMultiStoreStep.timeAdvance` (`Relico/DTR/DetailedMultiStoreSemantics.lean:176`) premises a
`DTR.MultiStoreDispatchStep` carrying a `selectedMessage` and a `selectedServer`, plus `hFuture`;
`LF.DetailedMultiStoreStep.timeAdvance` (`Relico/LF/DetailedMultiStoreSemantics.lean:229`) premises an
`LF.MultiStoreDispatchStep` carrying a `selectedAction` and a `selectedReaction`, plus `hFuture`. That is the
family with a *landed* weak bisimulation. The general family — the one whose bisimulation was being written —
was the only one in the repository where a clock could move without anything selecting where it moved to.

### Part 4 — the root cause: `earliest` was a name, and the neighbouring family had already shown what it costs to leave it one

The due-arrival theory carries **soundness** (`earliestDueArrival_sound`: the answer is a real message's
arrival), **completeness** (`earliestDueArrival_complete`: a due message forces an answer), and five equation
lemmas. Full census of the family, `grep`ped by prefix: `_sound`, `_complete`, `_cons_cases`,
`_cons_not_due`, `_cons_due_none`, `_cons_due_some_le`, `_cons_due_some_gt`. **There is no
`earliestDueArrival_minimal`, and there never was.**

Nothing before this obligation needed one. Soundness and completeness together answer *"is there something
to take, and is it real"*, which is all `take` asks. A minimum only has to *be* a minimum once a source clock
has to agree with a target tag — and that is the first thing row 7 does. So the word "earliest" carried the
property in the reader's head for four modules and was never a theorem.

What makes this a root cause rather than an excuse is that **the pattern was already in the repository, one
row earlier.** G1 proved `selectedActor_minimal` (`Relico/DTR/GeneralActorSelection.lean:998`) for the
lexicographic actor selection — a minimality theorem, deliberately written, about a minimum that a later
proof would have to rely on. The very next obligation defined a second minimum for the clock and did not
carry the pattern across. A convention that exists in one file and is not applied in its neighbour is worse
than no convention: it makes the missing theorem look like a deliberate omission.

The repaired module now carries the full quartet for the new function — `earliestFutureArrival_sound`,
`_complete`, `_minimal`, plus the four equation lemmas and `_cons_cases` — and `_minimal` is the one the
repair exists for.

### Part 5 — a second defect in the same obligation: a docstring that defers to a finding nobody wrote, and argues in the wrong direction while doing it

Row 6's `inductive GeneralStep` docstring on the target side analysed the mid-body case correctly and then
closed the paragraph with *"It is recorded as a finding rather than repaired here, because repairing it means
changing the source relation too, and that is not row 6's obligation."* The quotation is of the text **this**
changeset replaces; it is recoverable from the row 6 landing, the commit immediately preceding this one.

**No such record exists.** `grep -rniE "mid-body|midbody|mid body"` over all of `docs/` returns exactly two
hits, and neither is it: **F66**'s bullet that both TAKE rules premise an `ε` continuation, which is about
message acceptance rather than the clock, and `docs/PAPER_CORRECTIONS.md`'s **P17** note that the paper's
`ar_min` comprehension is restricted to `π_x = ϵ` actors, which is about the paper rather than about us. The
docstring is a forward reference to a document that was never written.

That is **F73**'s class — a docstring claim that nothing checks — recurring one entry later, and in a form
that is strictly harder to catch. F73's two claims were about the state of the file they sat in, so a reader
of that file could refute them. This one is a claim about the *absence* of something in a *different*
directory, and the only instrument that detects it is a grep for a record you have to already suspect is
missing.

The same paragraph also reasons in the wrong direction, and this is the part that cost real work. It observes
that a target rule *forbidding* mid-body advance would be **stricter** than the source, so a source step
would go unmatched and the forward condition would fail. That observation is true. The conclusion it draws is
that the target's permissiveness is therefore correct and the matter is closed. But "the target must not be
stricter than the source" has two solutions, and row 6 saw only one of them: make the target loose, or make
the source tight. Where the source is the one that diverged from the paper, only the second is available.

The workaround was already being planned in the same file. `LF.GeneralStep.selected_of_timeAdvance`'s
docstring said that because `DTR.GeneralStep.timeProgress` advances to *any* strictly later `future`, G2b
could satisfy the transfer condition by *choosing* the source's `future` at instantiation. That is precisely
the quantifier trick Part 2 refutes: the forward condition quantifies over all source steps, so choosing a
convenient one hides the unmatched steps instead of removing them. Both docstrings are rewritten in this
changeset to record the verdict rather than the workaround.

### Part 6 — the repair, as authored

**Source side, `Relico/DTR/GeneralState.lean`.** A new `earliestFutureArrival` / `earliestFutureArrivalOf`
pair computes the minimum arrival **strictly greater** than `now`, which is the range `earliestDueArrival`
cannot see. It ships with four equation lemmas, `_cons_cases`, `_sound`, `_complete` and `_minimal`.
`_minimal` quantifies its arrival inside the goal so that `induction` generalises it, and every arithmetic
step uses an explicit `Nat` lemma rather than `omega`, per **F72**. `GeneralConfiguration.nextArrival` lifts
it to the model-wide minimum over every actor's bag — the shape `ar_min` has in Table I.

**Source side, `Relico/DTR/GeneralSemantics.lean`.** `timeProgress` gains a third premise,
`hSelected : nextArrival config.erase = some future`, which removes `future`'s freedom: it is now determined
by the store rather than merely bounded below by `now`. The five existing inversion theorems each gained a
third `_` in their `| timeProgress` alternative, and a sixth theorem,
`DTR.GeneralStep.selected_of_timeAdvance`, was added as the exact mirror of the target's
`LF.GeneralStep.selected_of_timeAdvance`, so that a proof can read the constraint **back off** a step instead
of having to re-derive it.

**Target side: nothing changed.** `LF.GeneralStep.timeAdvance` already premised
`earliestPendingEvent? state = some event`. The whole repair moves the source to meet the target, which is
the direction Part 3 establishes is the correct one.

**The landed regression pin had to be rewritten, and that rewrite is the evidence.**
`Relico/Tests/GeneralSemantics.lean`'s `sourceTimeStep` built a time step on an **empty** configuration from
5 to 8. The repaired rule refuses it: with no messages anywhere, `nextArrival` is `none` and no `future`
satisfies `hSelected`. It is rebuilt around one actor holding one message arriving at 8 with `now = 5`, which
makes the two premises read one bag in opposite directions — `8 ≤ 5` is false so `readyActors` is empty, and
`earliestFutureArrival` returns 8. The three premises are discharged `by decide`, following
`readyActors_discriminates`, the repository's measured precedent that `decide` reduces over a populated store.
A new `example` then reads `nextArrival sourceConfig.erase = some 8` back out of the witness through the new
inversion lemma, so the pin now *exercises* the premise rather than merely surviving it.

What the pin does not do is witness the refusal. A negative would have to quantify over every `future`, and
no test can. The evidence that the rule tightened is that the old pin stopped type-checking.

**Deliberately not authored here.** Row 7 still owes the store-level lemmas that relate a per-actor
`earliestFutureArrivalOf` to the model-wide `nextArrival`, and the bag↔queue component of `R` that turns
`nextArrival config.erase = some t` into `earliestPendingEvent? state = some ⟨t, _⟩`. This changeset's job was
to make Lemma 1 **true**, not to prove it; §13's work plan already assigns the proof to row 7.

**Carried in the same changeset, because they are the same defect's blast radius.** Three docstrings that
called `nextArrival` "the paper's `ar_min`" without recording the restriction we drop (Part 7); one
F59-class evidence overclaim in the rule's docstring, which pointed at the Tests pin as evidence for a
negative it cannot show; and two `docs/STAGE_G_DESIGN.md` citations that this changeset's own insertion
staled, `GeneralConfiguration.readyActors` and `readyActors_discriminates` having each moved by several
hundred lines. Their line numbers were **dropped** rather than corrected — a line-number cite into a file
under active extension re-breaks on the next insertion, and the declaration names are unambiguous.

### Part 7 — three things measured alongside the repair, one of which is a question for the user

**(a) The repair deliberately drops one restriction the paper puts on `ar_min`, and the docstrings now say
so.** Table I minimises over actors whose continuation is `ϵ`, so in the paper an actor part-way through a
message server contributes no arrival at all. P17's closing note in `docs/PAPER_CORRECTIONS.md` already
observes that the restriction is **vacuous there**: such an actor has a `τ`-transition available, so TIME
PROGRESS could not have fired. It is *not* vacuous here, because our rules let the clock move while an actor
is mid-body, so restoring the restriction would reintroduce F74's defect with the direction flipped. Witness:
actor A mid-body holding a message arriving at 8, actor B idle holding one arriving at 20, `now = 5`. Under
the restriction A contributes nothing, `ar_min` is 20, and the source advances 5 → 20 — while the target's
queue, which ignores what any reactor is doing, advances 5 → 8. The source would step over a tag the target
must stop at. Three docstrings that had called `nextArrival` "the paper's `ar_min`" without qualification are
corrected; the difference is deliberate and its reason is recorded where the definition lives.

**(b) The repaired source rule and the target rule reach the same condition by different shapes, and that is
not a defect.** After the repair the source rule has three premises and the target rule has two, which looks
like a residual asymmetry and is not one. The target's `earliestPendingEvent?` is an **unfiltered** minimum
over the whole pending queue, so `hSelected` together with `hForward` already implies that no event is due —
`microstepAdvance`'s own docstring makes exactly this argument. The source's `earliestFutureArrival` is
**filtered** to arrivals strictly after `now`, so it cannot imply anything about the due ones, and quiescence
has to stay an explicit premise. The two combinations are logically equivalent: filtered-minimum plus
`readyActors = []` and unfiltered-minimum plus `now < future` each say *"nothing is due, and the next thing
arrives at `future`"*. `readyActorsOf` was read to confirm the first half — it consults only
`state.dueArrival now` and says nothing about `activeBody`, so `hQuiescent` is exactly arrival-quiescence.

The filtered shape was chosen because `hQuiescent` is a landed premise with a landed consumer,
`quiescent_of_timeAdvance`, and five inversion theorems whose statements stay true under an *added* premise
but not under a *replaced* one. No theorem states the equivalence, because nothing needs it; it is recorded
here so that a future reader comparing premise counts does not "fix" a rule that is already right.

**(c) Both rules still permit the clock to advance while an actor or reactor sits mid-body. This is
symmetric, so no transfer condition fails — and it is left as a question rather than decided.** Neither
`DTR.GeneralStep.timeProgress` nor `LF.GeneralStep.timeAdvance` mentions `activeBody`, so both admit a time
step in a state where some body is half-executed. Because the permissiveness is the same on both sides, the
bisimulation is unaffected. What is affected is what the two relations *mean*: each over-approximates its own
reference. The paper's DTR forbids it three ways over — Lemma 1's case opens *"When no untimed transitions
are enabled"*, Table I's comprehension carries the `π_x = ϵ` restriction, and **F66** records that both TAKE
rules premise an `ε` continuation. Real LF forbids it too: a reaction body runs to completion within a tag.
So a bisimulation between the two as they stand is a true statement about two models that are each slightly
larger than the thing they model, and **F74**'s own Part 2 argument — that a relation between two
over-approximations proves less than it appears to — applies to it.

The cost of closing it is measurable and small: one predicate per side asserting every continuation is empty,
as a fourth premise on `timeProgress` and a third on `timeAdvance`, plus one extra `_` in five source and
five target inversion alternatives and in both `microstepAdvance` sites. The rewritten source pin survives
unchanged, since its single actor already has `activeBody := []`. The cost of leaving it open is that G2c's
transfer conditions will be proved about a pair of relations that admit unreachable states, and the `π_x ≡ µ_r`
component of `R` will do no work at time steps. **Nothing in the repair depends on the answer**, which is why
it is not taken here.

**(d) The bag↔queue component of `R` cannot reuse the landed `PendingCorresponds`, and this is a design fact
rather than a defect.** `Correctness.PendingCorresponds` (`Relico/Correctness/Correspondence.lean`) has two
fields: `logicalTime`, which equates `targetAction.tag.time` with `sourceMessage.arrivalTime`, and
`actionName`, which equates `targetAction.name` with `Translation.actionNameFor sourceMessage.name`. The first
is exactly what Lemma 1 needs and transfers unchanged. The second does not transfer at all: since **F56**'s
repair the general action name is computed per **send site** by `generalActionNameAtSite`, and
`DTR.GeneralMessage`'s four fields are `sender`, `messageName`, `payload` and `arrival` — a source message
records no site. There is therefore no function from a general message's name to its action name for the field
to equate. Row 7 has to relate the two collections by target actor and arrival, with the name related through
the routing, or else carry the site in the source message. Recorded here so the choice is made deliberately
rather than discovered while a proof is half-written.

### The lesson

The obligation that catches a defect is usually the first one that has to *use* a definition, not the one
that writes it. `timeProgress` was written in row 6 and looked right; it was read in row 7, against the lemma
it has to satisfy, and was wrong. Four modules of due-arrival theory had the same shape — sound, complete, and
never asked to be minimal, because nothing had needed the minimality until a source clock had to agree with a
target tag.

Two habits would have caught it at authoring time, and both were available. The first is to write the
consumer's statement before the producer's definition, even informally: *"Lemma 1 says the source advances to
`ar_min`"* does not survive a premise that leaves `future` free. The second is the one this file keeps
relearning — our own documentation is evidence. P24 had transcribed `now := ar_min` four tasks earlier, in
prose, in a file the author of row 6 had written. The correct rule was already in the repository; nobody
looked.

And the corollary about deferral, which is Part 5's real content: **a docstring that defers to a finding is a
claim that the finding exists.** "Recorded as a finding rather than repaired here" is checkable, it was
false, and it converted a known defect into an unknown one for a whole obligation. If the record is not
written in the same changeset as the deferral, the deferral is not a deferral.


---

## F75 — three claims stage G's design makes about row 7's own deliverables, and the semantics rows 5 and 6 landed refutes each one

*Read*, all three, measured at the point `R` was defined and before any of row 7's Lean was authored. They
are one finding because they share one cause: §7 was written from the paper on 2026-08-23 and revised twice
against the *paper*, while the two artefacts it describes — the τ sets and the two runtime state types — were
built afterwards, by rows 5 and 6. Nothing re-read §7 against them. Each part changes what row 7 can state,
which is why none of the three is a wording nitpick.

### Part 1 — "`τ*` has no surplus behaviour to absorb" is true of the paper's tables and false of ours, and it decides how many τ theorems row 7 can state

§7's τ paragraph closes:

> *"Nothing on either side is unmatched, and `τ*` in Definition 1 has no surplus behaviour to absorb."*

and §15 item 4 summarises the stage as proving weak bisimilarity *"with **assignments and both send forms**
as τ on both sides"*.

Read against the landed relations, both sentences describe the paper's labelling rather than stage G's.
`DTR.GeneralStep` has four constructors — `assign`, `send`, `take`, `timeProgress` — of which **two** carry
`DTR.GeneralLabel.tau`. `LF.GeneralStep` has six — `assign`, `schedule`, `setPort`, `fire`,
`microstepAdvance`, `timeAdvance` — of which **four** carry `LF.GeneralLabel.tau`. The fourth is
`microstepAdvance`, and it is τ *because* P24's split is adopted, three paragraphs below the sentence quoted
above. So the two τ sets are not in bijection, `τ*` has exactly one piece of surplus behaviour to absorb, and
absorbing it is the entire purpose of the divergence the same section lists third.

The plan is not self-contradictory: the sentence is scoped to Tables I and II *as printed*, where a
microstep-only advance is labelled `t` and the τ sets really are matched pairwise. But nothing marks the
scope, and §15 item 4 — whose subject is what stage G proves, not what the paper prints — states the paper's
τ set as though it were ours.

What makes this worth a finding rather than a re-reading is what the sentence implies if taken at face value
about our semantics: that `R` survives every τ step. That is false for **five of the six** τ-emitting
constructors, and not merely unproved. `R` constrains a valuation, a bag against a queue, and a
continuation. DTR `assign` and LF `assign` each change a valuation; DTR `send` changes a bag; LF `schedule`
and `setPort` each change the queue. For a matched τ pair `R` is *restored by the partner step*, never
preserved by either half alone, so a single-step preservation theorem for any of those five would be a false
statement. `microstepAdvance` is the one τ constructor that touches nothing `R` reads: it advances
`Tag.microstep`, and `R`'s only tag component reads `Tag.time`. Row 7 therefore states exactly one τ
theorem, `generalCorrespondence_microstepAdvance`, resting on the general fact
`generalCorrespondence_retag` — and that one theorem is the whole checkable residue of the absorption claim.

### Part 2 — the initial case is specified "Unconditional", and the general family has no initial state to be unconditional about

§7's theorem list, item 1:

> *"`generalCorrespondence_initial` — `R` relates the initial states. Unconditional; the paper's 'holds
> initially' line, and cheap."*

There are no initial states. Every other family in the repository has an initializer on each side —
`Relico/DTR/Initialization.lean`, `DTR/StoreInitialization.lean`, `DTR/MultiStoreInitialization.lean` and
`DTR/GlobalMultiStorePayloadInitialization.lean`, each mirrored under `Relico/LF/` — and the general family
has none. What it has is `DTR.GeneralRuntimeConfiguration.ofConfiguration`, which lifts an *already
existing* configuration by attaching empty continuations, and on the target side nothing at all:
`Relico/LF/GeneralRuntime.lean` declares the two runtime structures, `idle`, `now`, the label type, `isTau`
and `project`, and no state builder. Nor is there a function from a `DTR.GeneralModel` to a
`DTR.GeneralConfiguration` anywhere in the repository: the only three definitions that produce a
`DTR.GeneralConfiguration` are hand-built fixtures in `Relico/Tests/GeneralActorSelection.lean`. And §13's
twelve rows create no initialization module in any of them.

"The initial states" is therefore not nameable and the theorem cannot be stated as specified. Row 7 states
the scoped form instead: quantify over an arbitrary source configuration and an arbitrary target reactor
store, and hypothesise the three things an initializer would have established by construction — every bag
empty, and each store covering the other with agreeing valuations and empty reaction bodies. The conclusion
is about `ofConfiguration config` and a hand-built target state at microstep `0` with an empty queue.

The word that is wrong is "Unconditional", not "cheap": the proof is one `rfl`, two symmetric applications of
`generalActorCorresponds_idle`, and a `simp` on membership in the empty queue. Nor is the scoped form a dead
end, which is why row 7 is not blocked on two new modules — the hypotheses are exactly what any initializer
will satisfy, so the unconditional statement will follow by instantiation rather than by re-proof. It is
nevertheless **owed**: as things stand the paper's "holds initially" line is discharged only relative to
hypotheses. **G5 is where it belongs**, and not arbitrarily: a runnable witness has to start somewhere, and
"somewhere" on each side is precisely the initial state this theorem cannot name. Filed against row 11 rather
than left to be rediscovered by whoever writes the witness.

### Part 3 — the paper gives each reactor its own queue and our target state has one for the program, so `R` has four components rather than three

§7 transcribes the paper's relation and then commits to it:

> *"Stage G defines `GeneralStateCorrespondence` with exactly these three components, per actor, keyed
> through the existing translation's reactor naming rather than an abstract `map_A`."*

In the paper the LF global state maps each reactor `r` to `(ηr, qr, µr)`, so `qr` is *that reactor's* trigger
queue and `bx ≡ qr` compares two collections belonging to one actor-reactor pair. `LF.GeneralRuntimeState`,
built by row 5, has three fields — `currentTag`, `reactors`, and a single `pending : LF.GeneralEventQueue`
for the whole program — and `LF.GeneralReactorRuntime` carries a valuation and an active body and no queue.
There is no `qr` to project. The information is the same, since `LF.GeneralPendingEvent` carries a `target`,
but it is distributed differently and `R` has to do the redistribution.

Two consequences, both visible in the landed module. The bag/queue component is
`GeneralPendingAgrees name bag pending`: per actor, but extracted from the global queue by that actor's name —
every message in the bag has a pending event targeted at the name and sharing its arrival, and every pending
event targeted at the name has a message in the bag sharing its arrival. (Two implications rather than a
bijection, and no multiplicity; **F74** part 7(d) records why the landed `PendingCorresponds` cannot be reused
and why the name is related through the routing rather than by an equation.) And `R` acquires a **fourth**
field, `pendingTargeted`: every pending event's target is an actor of the source configuration. Per-reactor
queues make that free — an event in `qr` is an event of `r` by construction — and one global queue does not,
because nothing in the state type stops an event naming a target no actor has.

The fourth field is load-bearing rather than tidy. `generalSourceMessageOfEvent`, the bridge both directions
of Lemma 1 run through, starts from an arbitrary member of `pending` and has to produce the *source* actor
whose bag backs it before any arrival theorem applies. Without `pendingTargeted` there is no such actor and
the backward direction of Lemma 1 is unprovable. This is a difference in representation rather than in
semantics, so it is **not** a fifth divergence from the paper and is deliberately not added to §7's list of
four; what has to change is the sentence that claims three components.

### The repair

Five edits to `docs/STAGE_G_DESIGN.md`, in this changeset, each at the sentence the part above quotes: the τ
paragraph in §7 gains the scope it was missing and a pointer here; §15 item 4's τ summary is corrected to the
τ set stage G actually uses; §7's theorem item 1 states the scoped form it will get and records the
unconditional one as owed; §7's `R` transcription says four components and why the fourth exists; and §13
gains one line under the work-plan table so the owed theorem is attached to row 11 where a reader of the plan
will meet it. No job count in the table is changed, because whether the two initializers arrive as new modules
or as additions to the existing `GeneralRuntime` pair is not yet decided, and inventing the number would be
worse than recording the dependency.

A sixth edit was forced by the third of those five rather than planned. Writing "not a fifth divergence" into
part 3 meant asserting that there are four, which made it worth checking every place the design states that
number: §7 says *"Four, and all four are forced"* directly above the list, §15 item 4 enumerates them as
`two + one + one`, and the **provenance paragraph in the preamble said `three`** — stale since P24's split
`TIME PROGRESS` became the fourth, in the same changeset that revised §7's list. The provenance sentence now
defers to §7 rather than restating the number, because a count kept in two places is a count that will
disagree with itself again. That is `F46`'s lesson (`docs/STAGE_E_FINDINGS.md`, *a count that was false the
moment it was written*) reaching a second document, and the reason the repair removes the duplicate instead of
correcting it.

One thing is deliberately **not** repaired. §7's τ table still lists the paper's τ sets read off Tables I and
II, unchanged, because that table's subject *is* the paper and F66 part 4 exists to keep it accurate. The
sentence about our own τ sets is the one that needed scoping.

### The transferable check

The three parts differ in what they got wrong — a scope, a modality, an arity — and are identical in how they
got there: **a design section that describes an artefact is stale the moment the artefact is built, and
nothing re-reads it.** §7 was revised twice, both times against the paper, and both revisions were correct.
What neither revision could do is check §7 against rows 5 and 6, which did not exist yet.

So the check is cheap and mechanical, and it belongs at the start of every obligation rather than at the end
of a stage: **before authoring row N, re-read the design's description of what rows 1..N−1 built, against
what they actually built.** Three sentences failed it here, and each would have been caught by opening one
Lean file. The alternative — discovering the mismatch while a proof is half-written — is what F74 part 7(d)
was already filed to prevent, and it is more expensive every time.

Note also which instrument would *not* have caught these. Every one of the three sentences is internally
coherent, cites the paper accurately, and contains no stale identifier, no stale count and no unreachable
citation. The audit habits this file has accumulated — grep for spelled-out counts, check citation
reachability per changeset, check that a deferral's target exists — all pass. Only reading the design against
the code refutes them.

The count audit did fire in this changeset, and where it fired is the point. It caught nothing in the three
sentences; it caught the preamble's `three`, in a paragraph no part of F75 quotes and no row-7 obligation
touches, and only because part 3 had to commit to a number before it could say "not a fifth". So the two
checks are complements rather than substitutes: the mechanical audits find sentences that disagree with *other
sentences*, and only re-reading the design against the code finds sentences that disagree with *the artefact*.
A changeset that runs one and not the other will land looking clean either way.

## F76 — the source selects the next message by priority and the target selects it by queue order, so the transfer condition the stage exists to prove is false, and the guard the design names for it is aimed at the wrong side

Measured during row 8's opening research, before any row 8 Lean was authored, by the check F75 had just
finished prescribing: re-read the design's description of what earlier rows *built*, against what they built.
F75 found three claims that were merely unstateable. This one is load-bearing — it refutes row 8's central
deliverable.

### The two selectors

Both languages choose the next message with the **same fold**: carry an incumbent, and at each candidate keep
the incumbent when it precedes-or-equals the candidate, otherwise adopt the candidate. Both are therefore
**first-wins on a tie**. They differ only in the key they compare.

| side | selector | key | consults priority |
|---|---|---|---|
| source | `DTR.GeneralActorSelection.selectedActor`, via `selectMinimum` and its `PrecedesOrEqual` (`Relico/DTR/GeneralActorSelection.lean`) | `(ReadyActor.logicalTime, priorityOf model actor)`, lexicographic | **yes** |
| target | `LF.GeneralRuntimeState.earliestPendingEvent?`, via `LF.selectEarliestEvent` (`Relico/LF/GeneralSemantics.lean`) and `LF.Tag.PrecedesOrEqual` (`Relico/LF/Scheduling.lean`) | `(Tag.time, Tag.microstep)`, lexicographic | **no** |

The target's key cannot express priority, so the target's same-tag tie-break is decided entirely by the order
of `state.pending`. That order is **append order**: both send rules build the queue with `state.pending ++
[event]`, so it is the order in which sends were executed.

The source's tie-break, when arrival *and* priority are equal, is the traversal order of `DTR.readyActorsOf`,
which is the order of the `config.actors` store. Store order and queue order are unrelated quantities — the
first is a declaration-time artefact, the second a run-time one — so the two sides do not even agree on their
*fallbacks*.

### Why the forward transfer condition is false

`LF.Tag.schedule` is P24's `upd`: a zero delay keeps the time and increments the microstep, and a **positive**
delay advances the time and leaves the microstep at zero. Two positive-delay sends that land at one logical
time therefore carry **byte-identical tags**, and the target's key has nothing left to separate them.

One body with two sends is enough. Let actor `a` hold a better priority than actor `b`, and let some body
execute `b.m() after 5; a.m() after 5;`:

* the queue afterwards is `[event → b @ (5,0), event → a @ (5,0)]`
* the target's fold meets `b` first, the tie holds, the incumbent is kept, and `fire` consumes **`b`**
* the source's `readyActors` holds both, the arrivals are equal, priority decides, and `take` consumes **`a`**

The labels are `.consume b …` and `.consume a …`. G2b's `ϕ` drops the payload and nothing else, so the two do
not become equal under it. A source step exists with no matching target step, which is exactly Definition 1's
forward transfer condition failing.

Two escape routes are already closed. `fire` carries `.consume` and is **observable**, not τ, so `τ*`
absorption cannot reorder it — the surplus τ step P24 introduced buys nothing here. And **neither side can
choose to accommodate the other**: `take` is premised on `hSelected : selectedActor model config.erase = some
selected` and `fire` on `hSelected : earliestPendingEvent? state = some event`, so both selections are forced.
This is not a nondeterminism that could be aligned by picking the right witness; both relations are
deterministic at this point and deterministically disagree.

### The guard the design names is aimed at the wrong side

§7 item 5 makes the two transfer conditions guard-relative on `ActorPrioritiesDistinct`
(`Relico/DTR/GeneralWellFormed.lean`), with the reason: *"without it the target's chosen reaction need not be
the source's chosen actor, and the witness for the existential cannot be constructed."*

The observation is right and the remedy is pointed backwards. `ActorPrioritiesDistinct` is a predicate on the
**source** model, and its effect is to make the source's priority key a strict order, hence the source's choice
unique. It says nothing whatever about `earliestPendingEvent?`, which is where the disagreement lives. Three
consequences follow, and the third is the one worth keeping:

1. The guard does not repair the counterexample above. Distinct priorities is exactly what that
   counterexample assumes.
2. Removing the guard does not repair it either. With priorities *equal*, the source falls back to store order
   and the target to queue order, and those still differ.
3. **The guard makes the divergence more reachable, not less.** Distinctness is precisely the condition under
   which the source's priority component discriminates, and therefore the condition under which the source
   overrides its own store order and departs from anything the target could be following. A guard that
   increases the reachability of the failure it is named to prevent is worse than an absent one, because it
   reads as a discharged obligation.

### Why stage F does not bridge it

§7 item 3 rests Lemma 2 on stage F's compile-time ordering theorems "rather than restating them", and stage F
did land real ordering results. They are the wrong shape for this gap. §III-D orders the **port reactions of
one reactor** by sender-actor priority; Lemma 2 orders the **reaction blocks of one reactor** by message-server
priority. Both feed `LF.GeneralProgram.reactionFor?`, which answers *which reaction of the target reactor
handles this event*. Neither is consulted when choosing *which of two reactors acts*, because that choice is
made before `reactionFor?` is reached, by `earliestPendingEvent?`.

The `fire` docstring states both halves of this itself, and is accurate: declaration order decides the
reaction, and a lookup consulting `GeneralReaction.priority` "would be reading a field G3 is about to make a
well-formedness violation". So the target's own design deliberately keeps priority out of the run-level
choice, and G3 is about to harden that. Stage F's theorems are sound, in scope, and orthogonal.

This also confirms the scope reading recorded when the paper's SOS rules were read for the same-arrival case:
the paper's `take` has no priority term, and its Lemma 2 is the **same-actor** case. Row 8's Lemma 2, scoped to
one actor as §7 item 3 already says, is unaffected by everything above. The transfer conditions are not.

**The two sentences above are REFUTED, by the paragraph above them — see F80.** Measured 2026-08-25, before
any Lemma 2 Lean existed. `LF.selectEarliestEvent` compares tags only and cannot see a reactor, so *"that
choice is made before `reactionFor?` is reached"* holds verbatim when the two same-tag events target **one**
reactor: there too the order is queue insertion order, and declaration order is consulted only afterwards, to
answer which reaction handles an event already chosen. Since a translated reactor's reactions all carry
distinct kinds, `reactionFor?` is invariant under permutation of `messageReactions`, so stage F's two theorems
are not *orthogonal* to Lemma 2 — they are **inert**, and Lemma 2 rests on them. F80 also finds Lemma 2's
*premise* unrepresented on the source side, and finds that within one reactor the over-specification recorded
below **inverts** into a mis-specification, which narrows candidate (e) to a partial quotient. What survives
here is the mechanism; what does not is the exemption.

### What this costs, and what it promotes

**Row 8's central deliverable cannot be proved as specified.** This is F75's class with a heavier bill: §7 item
5 was written from the paper before rows 5 and 6 existed, describes a target selector those rows later built
priority-blind, and passes every mechanical audit this file runs.

**But the damage is confined to one label, and that is measurable rather than consoling.** `DTR.GeneralStep`
has four constructors and `LF.GeneralStep` six; the observable labels are `.consume` and `.timeAdvance`, and
priority enters the semantics only at `take`/`fire`. Both time rules are selector-driven yet priority-blind —
the source tied to `nextArrival` by F74's repair, the target to `earliestPendingEvent?` — and Lemma 1 already
equates the two selectors' answers. So the `.timeAdvance` case of **both** transfer conditions is provable
exactly as §7 specifies, and is proved: `generalTimeAdvance_forward` and `generalTimeAdvance_backward` in
`Relico/Correctness/GeneralWeakBisimulation.lean`, green with no guard and no scoping hypothesis. What the
repair decision below governs is the `.consume` case **alone**. That case is deliberately not stated even in
weakened form, because a quietly narrowed theorem is the under-delivery the standing doctrine forbids where the
target is at fault. The practical consequence for the paper is that Definition 1 should be presented
case-by-case rather than as a single claim, since one of its two labels is settled and the other is open.

**The `lfc` reaction-priority probe is promoted.** It was recorded as gating G3 alone. It now also decides row
8's repair, and the load-bearing half of it is not "does a priority attribute exist" but **"does any attribute
order reactions across reactors, or only within one"**. If the target has no cross-reactor same-tag ordering
mechanism, then it genuinely cannot implement cross-actor actor priority, and the project's standing doctrine —
if the target is at fault, refuse the input rather than silently under-deliver — chooses a guard or fragment
restriction over a narrowed theorem. The probe needs a terminal and is therefore not ours to run.

**The probe has since been run, and the paragraph above needed one correction — see F77.**
Nine probes against `lfc` 0.11.0 on 2026-08-25. Summary: `@priority` does not exist, and no attribute
could have worked anyway because attributes attach to a reaction and hence to a *class*, never to one of
two instances; instance-declaration order influences the runtime but by no rule three instances confirm;
and a zero-delay `uses` edge **does** order reactions across reactors, which is the one mechanism that
rests on a construct LF assigns meaning to. The correction is to the sentence above beginning *"If the
target has no cross-reactor same-tag ordering mechanism"*: it presents that as the only route to a guard
or fragment restriction, whereas F77 finds the ordering mechanism to exist and the guard to be warranted
anyway, because the mechanism costs a topology the source model does not have. The conclusion survives;
the reasoning offered for it does not.

**Row 9 inherits it.** G2d's finite-trace agreement fails on the same witness, because the two traces differ by
a permutation inside one tag.

**And the target is over-specified, which is a second finding inside the first.** Real LF does not order
same-tag reactions in *independent* reactors; they are logically simultaneous. `earliestPendingEvent?` imposes
a total order on them anyway. So the total order is our artefact rather than the target's semantics, and any
statement that quantifies over it is stronger than the target supports. That observation is what makes a
correspondence stated up to within-tag permutation a candidate repair rather than a retreat — and it is
measurable rather than rhetorical, because `take` and `fire` each update a single store key and remove a single
queue element, which for distinct actors are disjoint. Whether that yields a genuine commutation result is a
confluence question over interleaved bodies, since both sides permit taking one actor's message while another
actor's body is half-executed, and it is not settled here.

### The decision, left open deliberately

Five directions, all measured, none picked: guard on the absence of cross-actor same-tag contention and prove
the scoped version; give the target a priority-aware tie-break, which needs the probe and may invent semantics
the target does not have; drop priority from the source, which contradicts the standing scope decision that
actor priorities are in scope and the repo is definitive; restrict the fragment and refuse such models, which
is doctrine-preferred but would reject the two corpus models where actor priority is irreducible; or prove the
commutation and state the correspondence up to within-tag permutation, which the paragraph above argues is the
most faithful reading and the most work.

Recording the five and choosing none is the point. The failure being repaired is a design sentence that chose a
remedy before the artefact existed; replacing it with a second unmeasured choice would reproduce it.

**Revised after the probe: F77 closes one direction, prices a second, and promotes a third.** The
reaction-attribute route is gone — `@priority` does not exist, and no attribute could serve, because
attributes attach to a reaction and therefore to a *class*, never to one of two instances of it. The
priority-aware tie-break survives but is realisable only by injecting zero-delay dependency edges among
receivers, which buys a language-level ordering guarantee at the price of ports, connections and forced
serialisation the source model does not have. And the within-tag-permutation reading is strengthened,
because the over-specification argued above is now established a second way, from our own two definitions
rather than from a reading of LF. Four directions remain rather than five, and the choice is still the
user's.

### The transferable check

F75 prescribed re-reading the design's description of earlier rows against what they built, and this finding is
that check paying for itself one row later. But note the sharpening it needs. F75's three claims were caught by
reading §7 against **row 7's own outputs** — the relation, the state types, the τ sets. This one was caught by
reading §7 against a **selector two rows upstream** that row 8 merely composes against and never mentions. The
rule as F75 stated it — re-read the description of what rows 1..N−1 built — is broad enough to cover it, and
the narrower reading that would have missed it is the tempting one: check the artefacts this obligation
*produces*, not the ones it *consumes*. Both halves are required, and the consumed side is where the
expensive errors are, because nothing in the obligation's own text points at them.

---

## F77 — the probe commissioned to decide F76 observed the order through a channel the language does not model, so it settles the runtime and not the semantics, and the finding it appeared to refute is confirmed

*Measured, with one part graded read.* Nine probes, `tools/paper-measurements/lf_semantics_probe.sh`
section 16, run against `lfc` 0.11.0 on 2026-08-25. The measurement succeeded; the inference drawn from
it in the same session did not, and that is the transferable half of this entry.

### What was asked

F76 left the repair open and promoted one measurement above the others. The load-bearing question was
recorded deliberately as **"does any mechanism order reactions across reactors at one tag"** rather than
the narrower "does a priority attribute exist", because F76's counterexample puts two same-tag events on
two **different** actors, and everything the file had measured before — section 1, and all six probes of
section 15, in three trigger shapes — moved reaction **declaration** order *within one reactor*. A
declaration list belongs to a reactor **class**; F76's divergence is between two **instances**. Nothing
in the file before section 16 had ever put two reactions in two different reactors at one tag.

### What the nine probes returned

All nine share F76's counterexample shape: one sender body, two sends, two receiving instances, one tag.

| probe | what varies from the control | measured |
|---|---|---|
| 16a `stageG_xr_control` | — | `sink2` then `sink1` |
| 16b `stageG_xr_sendorder_swap` | the two `set()` lines only | `sink2`, `sink1` — **unmoved** |
| 16c `stageG_xr_instorder_swap` | the two `new Sink` lines only | `sink1`, `sink2` — **moved** |
| 16d `stageG_xr_determinism` | byte-identical, run 7× | all 7 agree; `--workers 1` and `4` agree |
| 16e `stageG_attr_label_control` | adds `@label(...)` | compiles; order unchanged |
| 16f `stageG_attr_priority` | `@priority(2)` / `@priority(1)` | **rejected**: `Unknown attribute: priority`, 2 errors |
| 16g `stageG_uses_reverse_chain` | `k2.done -> k1.gate` | **confounded, do not cite** |
| 16h `stageG2_xr_three_instances` | three instances `k1,k2,k3` | `sink3`, `sink1`, `sink2` |
| 16i `stageG2_uses_forward_chain` | `k1.done -> k2.gate` | `sink1`, `sink2` — **overrides the default** |

Three of these are worth reading twice. **16f is a measured absence, not a syntax accident**, and it is
readable as one only because 16e exists: without a control establishing that *some* attribute is accepted
in that position, the rejection would have been ambiguous between "no priority attribute" and "no
attributes here at all". **16g is confounded by its own design** — it was built so that a `sink2`-first
result would be unexplainable by anything but the dependency edge, and 16a then revealed `sink2`-first to
be the default, so the outcome is equally consistent with the edge doing everything or nothing. It is
marked `DO NOT CITE` in the script and replaced by 16i, which chains **forward** so that the edge's
prediction *opposes* the measured default. And **16h refuted the rule 16c appeared to establish**: at two
instances the order is consistent with reversal, at three it is `sink3, sink1, sink2`, which reversal does
not predict. The function fitting both points is *last-declared first, then the rest in declaration
order* — a two-point fit to an undocumented scheduler, with n ≥ 4 unmeasured. It is recorded in the
script as a shape and explicitly not as a rule.

### The defect: every probe but one measures an unmodelled channel

Each probe observes order by calling `std::printf` from a reaction body. That is the flaw, and it is
structural rather than a matter of probe hygiene.

LF's determinism guarantee fixes **port values and reactor state** at a tag. It does not fix the
execution interleaving of raw target-language statements inside reaction bodies. Two reactions in
independent reactors at one tag cannot observe each other through anything LF models: had the two sinks
written to output ports instead of stdout, a downstream reactor would read identical values at that tag
whichever body executed first. `printf` reaches the terminal *outside* the model, so it exposes an
ordering the semantics deliberately leaves free.

So sections 16a through 16h measured **reactor-cpp 0.11.0 being incidentally stable on a channel the
language does not specify**. The stability is real — seven runs, two worker counts — and it is worth
having recorded, because it means a generated program's stdout is reproducible in practice. But
reproducibility of an unmodelled side effect cannot license a correctness theorem, and in particular
16c and 16h cannot license a printer that realises actor priority by ordering its instance declarations.
Such a printer would be correct against this runtime at this version and against nothing stated.

### The one probe that escapes, and why it escapes by construction

16i is the exception, and not by luck. A zero-delay connection into a `uses` clause creates a genuine LF
**dependency** between the two reactions, and dependencies are precisely what LF's semantics **do**
order — the same mechanism §III-E of the paper already relies on when it treats connections without
`after` as instantaneous and rejects causality cycles. 16i's result is therefore a language-level
guarantee; every other result in section 16 is an implementation observation. That distinction, not the
list of outcomes, is what the section is for.

Its cost is equally structural and must travel with any repair that uses it: the chain injects input
ports, output ports and connections the source model does not have, and it **serialises reactors the
source leaves concurrent**. The generated program stops being a transliteration of the source topology
and starts encoding a scheduling decision in its dependency graph.

### A limit that holds regardless of any measurement

`@priority` turned out not to exist, but even a version of `lfc` that accepted it could not have repaired
F76 in general. An attribute annotates a **reaction**; a reaction belongs to a reactor **class**; so no
attribute can distinguish two **instances** of one class. The corpus model that makes actor priority
irreducible, `phils`, is built from instances of one class. This is an argument about where attributes
attach, so it survives any future `lfc` release, and it removes an entire branch of the candidate space
without needing a run.

### What this does to F76, including one thing it does not do

**F76's over-specification paragraph is confirmed, and was briefly and wrongly reported as refuted.**
That paragraph says real LF does not order same-tag reactions in independent reactors, so
`earliestPendingEvent?`'s total order is our artefact rather than the target's semantics. On seeing
16d's seven agreeing runs the immediate reading taken was the opposite — that the target *does* order
them deterministically, so our model merely picks the wrong total order rather than inventing one. That
reading survived about as long as it took to ask which channel the agreement was observed on. It is
recorded here rather than quietly dropped, because it is the same error the two findings above it
record, arriving one level further up: F75 caught a design describing artefacts it predated, F76 caught
a design describing a selector built after it, and this is a *measurement* being read as evidence for a
proposition it does not address. The instrument that caught it was the probe's own pre-run comment,
which already said in as many words that a confirmed rule "would be true of this runtime rather than of
the language" — written before the run, forgotten within an hour of reading the output, and recovered
only by re-reading the script rather than the results.

**The over-specification is provable from our own definitions, with no probe at all.** This is worth
separating out, because it means the load-bearing claim does not rest on the flawed channel. `pending`
is extended by `++ [event]` at both send rules, so queue order is send order; `selectEarliestEvent` is
first-wins on a tag tie. Therefore swapping two sends in one source body changes which event our model
consumes first, and `.consume` is an **observable** label in `LF.GeneralStep`. Our target model thus
promotes to observable behaviour a choice LF's semantics do not determine at all. The probes were needed
to learn whether the target *could* be made to determine it; the over-specification itself is a reading
of two of our own definitions.

**The candidate space F76 left open has changed shape.** Of its five recorded options: dropping priority
from the source is still excluded by the standing scope decision; giving the target a priority-aware
tie-break survives but is now known to be realisable **only** by 16i's dependency injection, with the
port, connection and forced-serialisation costs named above; the fragment restriction survives unchanged
and remains conservative enough to reject `phils`; and stating the correspondence up to within-tag
permutation is **promoted** rather than demoted, since the over-specification that justifies it is now
confirmed from two independent directions. The reaction-attribute route is closed outright, by
measurement and, more durably, by the class-versus-instance argument above.

**And one option is safe to exercise before the decision is made.** Guarding on the absence of
cross-actor same-tag contention and proving the scoped `.consume` case is monotone with respect to every
remaining choice: a theorem proved under an explicit guard stays true if the guard is later discharged
by dependency injection, subsumed by a permutation-quotiented statement, or made vacuous by a narrowed
fragment. It is not the same as quietly weakening the theorem, which is what the standing doctrine
forbids, provided the guard is named in the statement and the unguarded case is left recorded and open.
That distinction — a guard written into the statement versus a scope silently assumed — is the whole
difference between a scoped result and an under-delivered one.

### The transferable check

**Name the channel before citing the result.** A probe does not measure a semantics; it measures
whatever channel its output travels on, and the two coincide only when that channel is one the semantics
constrains. Section 16 ran nine probes through `printf` and produced exactly one citable result, and the
one that survived did so because it was built around a **dependency** — a construct the language assigns
meaning to — rather than around an observation. The check is cheap and belongs beside every probe in
this file: write down which construct of the specification the observed quantity is supposed to be a
consequence of, before reading the output. Where the answer is "none", the probe measures the
implementation, which is worth knowing and is not evidence.

The companion check is narrower and specific to how this session failed. A measurement that appears to
strengthen the position of whoever commissioned it deserves the re-read that a disappointing one gets
automatically. Here the disappointing readings were taken correctly on the spot — 16f's rejection, 16g's
confounding, 16h's refutation of a prediction stated in advance — and the one flattering reading, that a
prior finding had been overtaken by a decisive measurement, was the one that went unexamined.

---

## F78 — the transfer conditions conclude with strong steps where the architecture claims weak ones, and the label correspondence the `.consume` case needs is not merely missing but refutable in the shape every other family uses

*Read.* Established at the declarations, by four searches over `Relico/` described below, on 2026-08-25,
after row 8 part 1 landed at `e47161d` and before any part 2 Lean was authored. Two defects with one
cause; the second is the one that changes what later rows can claim, and it is **not** waiting on F76.

### Part 1 — every family in the repository has a label correspondence except the one stage G is about

Enumerating declarations whose names end in `LabelCorresponds` or `LabelsCompatible` across `Relico/`
returns **eleven** relations of the first kind — nine `inductive`, two Prop-valued `def` — and **ten** of
the second, spread over the machine, store, multi-store, multi-store-payload, payload, bound-payload,
concrete-detailed, detailed-bound-payload and both direct-LF families. The count of those whose name
begins `General` is **zero**. Four further inductives named `*WeakLabelTraceCorresponds` lift the relation
to traces, and none of those is general either.

So the general family is the only one whose two label types are never related to each other. Only four
files in `Relico/` so much as mention `DTR.GeneralLabel` and `LF.GeneralLabel` together —
`Relico/Tests/GeneralRuntime.lean`, `Relico/Tests/GeneralSemantics.lean`,
`Relico/LF/GeneralRuntime.lean` and `Relico/Correctness/GeneralWeakBisimulation.lean` — and of those the
first two are tests, the third mentions the source type only inside docstrings, and the fourth mentions
both only because it holds one theorem per direction.

The docstrings are worth crediting rather than faulting, because they are careful in exactly the place a
stale claim would have been cheap. `LF.GeneralLabel`'s own note says the three shapes are "what makes a
label translation **possible** at all" — possible, not present — and `LF.GeneralLabel.project`'s note
says the two projections "must be independently statable" because row 9 compares
`Common.observableProjection` on a source trace against the same function on a target trace. Neither
oversells. What neither says, and what nothing in the repository says, is what relates the two
projections' **outputs**.

### Part 2 — the `.timeAdvance` cases evade this by inlining, which is why row 8 part 1 could land at all

`generalTimeAdvance_forward` does not quantify over a label correspondence; it *constructs* the target
label as the literal `LF.GeneralLabel.timeAdvance state.currentTag.time event.tag.time`. The
correspondence is inlined into the statement rather than stated, and that is sound here for a structural
reason: `timeAdvance` carries `(LogicalTime, LogicalTime)` on **both** sides, so the two constructors are
interchangeable up to which namespace they are read in.

The precedent confirms this is the right reading rather than a shortcut.
`MultiStorePayloadDetailedLabelCorresponds`'s `timeAdvance` constructor relates the two labels by exactly
two premises, `targetBefore = sourceBefore` and `targetAfter = sourceAfter` — which is what an inlined
literal delivers definitionally. Row 8 part 1 therefore satisfies what the precedent's relation would
demand at this label, without the relation existing.

`consume` is where that stops working. The source constructor carries
`(receiver : ActorName) (message : DTR.GeneralMessage)`; the target carries
`(target : ActorName) (kind : LF.GeneralEventKind)`. Those are different types, no literal bridges them,
and so the `.consume` case cannot be stated at all until something relates them. The design's shorthand
for that something has been a label map ϕ, and **that shorthand is itself wrong**: all eleven
`*LabelCorresponds` precedents are Prop-valued **relations** rather than functions, and the multi-store
one has a `microstep` constructor sending source `.tau` to target `.microstepAdvance before after`. A
function could not do that, and P24 measured that the general family needs precisely that asymmetry.

### Part 3 — in the precedent's shape the general `.consume` correspondence is refutable, and F56's repair is the reason

The precedent's `consume` constructor pins the target component **functionally**: its second premise is
`targetReaction = Translation.compileMultiStorePayloadReaction sourceServer`. Transposed to the general
family that would demand the target's `kind` be a function of the source's `message`. It cannot be.

`LF.GeneralEventKind` is `.logicalAction (name : ActionName)` or `.inputPort (name : PortName)`, so the
target's `.consume` label carries a **name**. Both families of name are **per send site**:
`Translation.generalActionNameAtSite` computes its suffix from `selfSendOrdinalAt site message`, the F56
repair, and P20 settled external port names per send site as well. `DTR.GeneralMessage` has four fields —
`sender`, `messageName`, `payload`, `arrival` — and **no site**.

That gives a two-element counterexample, not merely an absence of proof. A body that sends the same
message to itself twice produces two source messages that are equal in all four fields, hence equal under
the structure's derived `DecidableEq`, and two target events whose action names differ by ordinal. A
function from the one to the other would have to send a single value to two distinct names. The witness is
already in the repository: it is the two-sends-in-one-body fixture built for F56.

`Relico/Correctness/GeneralCorrespondence.lean` had **already written this argument down**, one level
below where it bites. Its module note says the multi-store `PendingCorresponds` "is not reusable" because
it pins the action name as a function of the message name while general action names are per send site,
and concludes that "an agreement that mentioned the action name would be unprovable rather than merely
stronger" — which is why `GeneralPendingAgrees` relates a bag to a queue on `(target, logical time)` only
and mentions neither the message name nor the event kind.

The step this finding takes is to notice that the same obstruction applies to the **label**, where it is
strictly worse. On `R`'s pending component the missing field is internal bookkeeping. On `.consume` it is
part of an **observable** label, so the irrecoverable component is part of what a trace *says*. And the
cause is a repair: F56 made action names per site to stop repeated identical self-sends silently
collapsing into one, and per-site names are exactly what a source message cannot determine.

### Part 4 — the transfer conditions produce strong steps, not weak ones

Independent of all of the above, and cheaper to see. Both landed transfer conditions conclude with a bare
step relation: `LF.GeneralStep program state (LF.GeneralLabel.timeAdvance …) …` forward, and
`DTR.GeneralStep model config (DTR.GeneralLabel.timeAdvance …) … ∧ GeneralStateCorrespondence …`
backward. The architecture stage G is building toward is a **weak** bisimulation, and a step
correspondence with an owed lift proves something strictly weaker than that, because nothing in it
permits the matched transition to sit inside internal traffic.

`Relico/Correctness/GeneralWeakBisimulation.lean` did not import `Relico.Common.WeakTransition` at all,
and no transitive import reached it: `GeneralTimeEquivalence`, `GeneralCorrespondence`,
`DTR/GeneralSemantics`, `DTR/GeneralRuntime` and `LF/GeneralRuntime` were each measured at zero. The
`Detailed*` families import it at their semantics file instead. So the weak machinery F70 recorded as
already generic and already proved was, for the general family, exercised only by the five concrete pins
at `emptyProgram`/`emptyModel` in `Relico/Tests/GeneralSemantics.lean` — which is F73 part 1's defect
recurring one row later, in the module that exists to discharge it.

This half **is** repaired in the same changeset as this entry. `generalTimeAdvance_forward_weak` and
`generalTimeAdvance_backward_weak` restate both directions over `Common.WeakStep`, and the τ padding they
supply is empty at both ends — which is the *stronger* statement, and the honest one for these two rules,
since a source time advance is matched by exactly one target advance with no administrative traffic
around it. Genuine padding is owed only at `.consume`, where P24 measured the microstep the source does
not take.

Both lifts go through the `WeakStep.visible` **constructor** rather than `WeakStep.of_step`. `of_step`
takes only `hStep`, splits on `isTau label` with `classical` `by_cases`, and therefore elaborates
whatever the τ classification says; a statement proved through it would still typecheck if `isTau` were
changed to accept `.timeAdvance`, so it would be invariant under the very classification that decides
whether the label is observable. The constructor demands `¬ isTau label`, discharged by
`not_isTau_timeAdvance` on each side, which is the component that would break.

### What this costs row 9

Row 9's finite-trace agreement inherits a constraint §7 does not record. `Common.observableProjection`
applied to a source trace yields `List DTR.GeneralLabel`; applied to a target trace it yields
`List LF.GeneralLabel`. Those are different types, so "agreement" cannot be an equality, and by part 3 it
cannot be a name-preserving relation either: the target's `.consume` names record a send site that the
source alphabet has no field to record. What row 9 can state is agreement up to a relation that projects
the site away, or agreement on `(receiver, messageName)` with the site existentially quantified. The four
`*WeakLabelTraceCorresponds` inductives are the shape to copy, and they are relations for this reason.

Definition 1 should also be re-specified in the design as **per-rule transfer lemmas plus an owed label
relation**, rather than as one claim quantified over all labels. Row 8 landed two rules by inlining, #129
owes the third, and the quantified form conceals that the third needs a definition before it can have a
theorem.

### The repair, and the question it leaves

Part 4 is repaired here. Part 3 is recorded and **not** repaired, because closing it is a design choice
with observable consequences, and per the standing doctrine a target-side obstruction is refused and
recorded rather than quietly worked around. The choices are: relate `.consume` labels on
`(receiver, messageName)` and existentially quantify the site, which keeps both alphabets and weakens the
observable to what both sides can determine; add a site field to `DTR.GeneralMessage`, which makes the
functional shape provable but changes the source language's runtime state to suit the target; carry the
site only on the target label and quotient the trace statement by it; or restrict the fragment to bodies
with no repeated identical self-send, which is conservative and rejects a case F56 exists to support.

The first is the smallest and is what the existing `GeneralPendingAgrees` already does one level down, so
it is the consistent choice rather than merely the cheapest. It is written down here rather than taken,
because it decides what stage G's headline theorem *observes*, and that is the user's call. Note that
this question is **independent of F76's**: F76 decides *which* event is consumed, this decides whether the
consumption can be *related* to a source message at all. #129 is blocked on both, and a decision on F76
alone does not unblock it.

**Superseded the same day, by evidence rather than by a decision — see F79.** The first option is not the
smallest of four choices; it is the only one left standing once the paper's own Fig. 2 is read, and the
"user's call" framing above was wrong. Fig. 2a's `Controller` declares one message server and Fig. 2b's
`Controller` reactor answers it with two reactions, so the functional shape is refuted in the paper's own
illustrative translation and the fragment-restriction option would refuse that example. What remains of
this paragraph is its last sentence, halved: **#129 is blocked on F76 alone.**

### The transferable check

**An obstruction recorded for one component of a correspondence applies to every observable that mentions
the same field.** The argument in part 3 was already written, in prose, in the module that defines `R`'s
pending component — and it was written *well*, with the alternative named and the reason it is unprovable
spelled out. It still failed to travel one level up to the label type, because nothing links a note on a
`def` to the `inductive` in a different directory that will later need the same fact. The cheap version of
this check: when a definition is deliberately coarsened to stay provable, list the other declarations that
mention the dropped field, and record the coarsening against each of them.

The narrower lesson is about the shorthand. Calling the missing artefact "ϕ" carried a false assumption —
that it is a function — for as long as it went unexamined, and all eleven of the repository's precedents
are relations. A one-letter name for something that does not exist yet will quietly assert a type; check
the precedents' *keyword* before adopting the design's notation.

---

## F79 — F78 part 3's four-way choice was already answered by the paper's own Figure 2, two pages from the definition it is about

Graded *Read*: the paper's figures and §IV definitions, plus five declarations read in-tree. No build and
no `lfc` probe. Measured 2026-08-25, after F78 landed at `e703c5d` and before any `.consume` Lean was
authored. Issued as **P25** on the paper side.

### What F78 left open, and why it should not have

F78 part 3 established that the general `.consume` correspondence is refutable in the functional shape every
other family uses, listed four candidate repairs, and handed the choice to the user on the ground that it
"decides what stage G's headline theorem *observes*". Three of the four are refuted and the fourth is
forced, by evidence that was already in the paper.

Definition 1 requires a **bijection** `f : Act_1 → Act_2`, and §IV instantiates it as
`ϕ : Act_dtr → Act_lf` mapping `ms ↦ rct`, glossed *"each DTR message server maps to an LF reaction"*.
Fig. 2a's `reactiveclass Controller(5)` declares **one** message server, `msgsrv receiveReading(int w)` at
line 31, and both sensors send to it (lines 10 and 25). Fig. 2b's `reactor Controller` answers with **two**
input ports and **two** reactions, `reaction(readingFromTemp)` and `reaction(readingFromSmoke)`. One server,
two reactions: `ϕ` is not a function, in the paper's own illustrative translation.

### The four options, decided

1. **Relate `.consume` on `(receiver, messageName)` with the site existentially quantified — TAKEN, and now
   forced rather than preferred.** It is what all eleven precedents do structurally, what
   `GeneralPendingAgrees` already does one level down, and what the paper's figure requires.
2. **Add a site field to `DTR.GeneralMessage` — REFUSED.** It makes the source language's runtime state carry
   target bookkeeping and diverges from Table I, and it is unnecessary: functionality is only ever needed in
   the *target-to-source* direction, where it already holds. Each emitted reaction comes from exactly one
   site or route of exactly one message server, so "which server does this reaction serve" is total.
3. **Carry the site on the target label only and quotient at the trace statement — REFUSED as strictly
   worse.** Same content as option 1, deferred to row 9, which needs the label relation regardless.
4. **Restrict the fragment to bodies with no repeated identical self-send — REFUTED.** The standing doctrine
   licenses refusal only when the *target* is at fault, and it is not; and Fig. 2a's `Controller` is the
   fan-in shape, so this option would refuse the paper's own example.

### The repo half, measured

- `generalReactionNamesOf` (`Relico/Translation/GeneralBasic.lean`) emits, per message server, one reaction
  per self-send **site** followed by one per **route into** that server. The count is `sites + routes`; one
  reaction per server is the special case, not the rule.
- `compileGeneralReactiveClass_reactionNames` pins a reactor's entire reaction-name list to exactly that
  list, so the multiplicity is a proved property of the translation and not an accident of an emitter.
- `keep-alive.rebeca` is the committed fixture whose route list is empty and whose group is still two
  reactions long — an in-tree witness, no new fixture needed.
- `generalActionNameAtSite` is `generalActionNameFor message (generalActionSiteSuffixFor …)`, and
  `generalActionInfixFor s = "_action" ++ s`, so a target action name is `<message>_action<suffix>` with the
  suffix empty for a single-site message and the site ordinal otherwise.
- `generalActionNameFor_message_injective` is injectivity **with the site suffix fixed**. The unrestricted
  form is neither proved nor needed: a forward-defined relation never inverts a name. Its own docstring says
  the converse is unstated deliberately rather than pending, and the `/-!` section further down the same file
  — *"What can be proved about the port names, and what cannot"* — records that the analogous both-components
  reading is false outright for the port names, by case folding and by an unmarked suffix boundary.

### What this changes

**#129 is blocked on F76 alone.** F78 said it was blocked on two independent decisions; one of them is now
answered, and the remaining one is the F76 repair, which genuinely is the user's because it decides
*behaviour* rather than *notation*. The `.consume` statement can be authored the moment F76 is settled, in
the shape option 1 fixes, and row 9's projection agreement inherits the same relation rather than an
equality.

### The transferable check

**Before escalating a decision to the user, read the artefact the decision is about.** F78 offered four
options on the shape of a label correspondence while the paper's illustrative translation — two pages from
the Definition 1 text F78 quotes, in a figure this project has already cited in P20 and P23 — contained a
worked counterexample that eliminates three of them. The escalation was not wrong to exist; it was wrong to
be *cheap*, because writing down four options costs less than reading the figure and produces something that
looks like diligence.

The narrower version, and the reason this recurs: I read Fig. 2 for the question I had at the time. P23 read
the same figure for `map_M`'s domain and noticed that `TempSensor` and `SmokeSensor` each get their own
`sendReading` reaction — while the third reactor on the same page breaks the same map in a second, unrelated
way. **A figure that has already refuted one claim is the first place to look when a neighbouring claim needs
refuting, and the prior reading of it is not a substitute for a fresh one.**

## F80 — F76's own argument refutes the exemption F76 grants Lemma 2, and stage F's two ordering theorems are not orthogonal to it but inert

*Measured.* No build and no new `lfc` probe: four in-repo reads, plus two `lfc` measurements this project
has already landed. Written during `#106`'s pre-authoring measurement, before any Lemma 2 Lean existed.

### The sentence, and the paragraph immediately above it

F76's *Why stage F does not bridge it* section argues that stage F's ordering results are the wrong shape
for the transfer conditions. The argument is correct, and worth quoting because it is the argument that
refutes the sentence after it:

> *"Both feed `LF.GeneralProgram.reactionFor?`, which answers* which reaction of the target reactor handles
> this event. *Neither is consulted when choosing* which of two reactors acts, *because that choice is made
> before `reactionFor?` is reached, by `earliestPendingEvent?`."*

Two paragraphs later, the exemption:

> *"Row 8's Lemma 2, scoped to one actor as §7 item 3 already says, is unaffected by everything above."*

The first passage is phrased about two **reactors**, and the second reads the gap as confined to them.
`LF.selectEarliestEvent` does not know what a reactor is. It folds on `LF.Tag.PrecedesOrEqual` and on
nothing else, and its own docstring says so in terms that leave no room: *"The comparison is on tags only
… nothing here consults the reactor, and nothing may."* So *"that choice is made before `reactionFor?` is
reached"* is true word for word when the two events target **one** reactor. The exemption is refuted by
the paragraph it follows.

### Measured

1. **`LF.selectEarliestEvent` compares tags and keeps the incumbent.** It is the accumulator fold
   `if best.tag ≼ candidate.tag then best else candidate`, and `PrecedesOrEqual` is reflexive, so a tie
   retains the earlier-inserted event. `earliestPendingEvent?` seeds it with the queue head. For two
   events sharing a tag — whatever they target — the firing order is **queue insertion order**.
2. **`reactionFor?` is keyed on the trigger name, not on list position.** It reaches
   `LF.findReactionForKind?`, whose `matchesKind` is name equality on both `GeneralEventKind`
   constructors. First match wins, so list position arbitrates **only** between two message reactions of
   one reactor that share a trigger.
3. **A translated program never contains two such reactions.** `generalReactionNamesOf` gives a message
   server one logical action per self-send **site** and one input port per **route into** it, so every
   emitted reaction of a reactor carries a distinct kind. Therefore `reactionFor?` — and with it every
   `LF.GeneralStep` derivation, since `fire`'s `hReaction` is the only premise in either step relation
   that reads `messageReactions` — is **invariant under permutation of `reactor.messageReactions`** on
   all translated input.
4. **Well-formedness does not forbid the sharing case, and G3 will not either.**
   `LF.GeneralReactor.wellFormed` requires `declaredNames.Nodup` and then tests `messageReactions` with
   `.all` twice; there is no distinct-trigger conjunct. `#108`'s tenth clause is about the reaction
   `priority` **field**, a different gap.

### The corollary, which is the sharp form

Declaration order is consulted at run level in **exactly one** situation — two message reactions of one
reactor sharing a trigger — and that situation is one **well-formedness permits and the translator never
emits**. The mechanism is not merely inert on the input we produce; it is live only on input we cannot
produce.

So `portReactions_realizeActorPriority` and `messageServerReactions_realizeMessageServerPriority` are not,
as F76 concludes, *"sound, in scope, and orthogonal."* Sound: yes. In scope: yes. Orthogonal: no — Lemma 2
**rests** on them, and at run level they decide nothing. This is F60's class arriving at the step relation
rather than at a printer assertion: a result invariant under the very thing it is credited with pinning.
F60 caught it in an assertion whose two sides both moved with the sort; here both sides of the ordering
question are settled by a fold that never sees the sorted list.

### And the source has no order for Lemma 2 to preserve

The target half above says the conclusion of Lemma 2 is not derivable. The source half says its
**premise** has no run-level antecedent either.

- `ReadyActor` carries `actorName` and `logicalTime` and nothing else. The general family reuses the
  actor-priority layer's structure verbatim, so the selector's answer names an actor and a time — never a
  message.
- `DTR.GeneralStep.take` then chooses among that actor's due messages by an **arbitrary bag split**,
  `hDue : actor.state.bag = earlier ++ message :: later`, tied to the selector only by `hArrival`. Message
  server priority is not a premise of the rule.
- `priorit` does not occur at all in `Relico/DTR/GeneralRuntime.lean`, and occurs in
  `Relico/DTR/GeneralSemantics.lean` only in two comments naming the multi-store layer.

`LF.GeneralStep.fire`'s docstring already states the asymmetry, and states it accurately: *"This is
tighter than the source: the source's selection fixes only an actor and a time, leaving the choice among
equally-early messages open, while here the fold picks a single event outright."* What it does not do is
ask what that costs Lemma 2. It reads the source's looseness as a fact about the target being well
behaved, in a docstring whose next paragraph is about declaration order — so the two halves of this
finding sit four lines apart in the rule they are about.

Run-level Lemma 2 in the paper's form is therefore not an unproved theorem. It is a theorem whose
antecedent — *the source consumed `ms_i` before `ms_j` because `prty_l(ms_i) < prty_l(ms_j)`* — is not a
fact about any source step this repository defines.

### Within one reactor the target defect inverts, and that is what makes this decision-relevant

F76 closes with a second finding: the target is **over-specified**, because real LF leaves same-tag
reactions in *independent* reactors logically simultaneous while `earliestPendingEvent?` totally orders
them anyway. That is correct, and it is why F76 promotes a correspondence stated up to within-tag
permutation as its front-running repair.

Within **one** reactor the direction reverses. Real `lfc` does order those, by reaction declaration order
— measured in `#80` and reconfirmed in F77's own account of what preceded its cross-reactor probes:
*"everything the file had measured before — section 1, and all six probes of section 15, in three trigger
shapes — moved reaction declaration order within one reactor."* Our fold orders them by queue insertion
instead. So within one reactor the model is not over-specified but **mis**-specified, and the two are not
the same kind of defect: over-specification makes a theorem stronger than the target supports, while
mis-specification makes it **false of** the target.

**Consequence for the repair decision that is still open.** F76's candidate (e) — correspondence up to
within-tag permutation — is **too coarse as stated**. It would quotient away the one same-tag ordering the
target genuinely enforces, and which six `lfc` probes in three trigger shapes measured. It refines to a
partial quotient: free permutation among **distinct** reactors at one tag, order-**preserving** within one
reactor. Recording that refinement is a measurement and is done here; choosing among the candidates
remains the user's, because it still decides behaviour.

**The witness is the paper's own, and it is the same figure as P25's.** Fig. 2a's two sensors both send to
one `Controller`, so two same-tag events target one reactor, and the two reactions they trigger are
exactly the port reactions whose declaration order §III-D sorts by *sender actor* priority. The figure
that refuted `ϕ` in P25 is the witness that §III-D's mechanism is run-level inert.

### What row 8 can honestly deliver

The standing doctrine forbids a quietly narrowed theorem where the target is at fault, and prescribes
recording the defect and proving the scoped version. The scoped version here is not a weakened Lemma 2;
it is the **refutation stated as a theorem**, in the shape §10.2's refuted `setPort` obligation took at
F50/`#60`: that `reactionFor?`, and hence `LF.GeneralStep`, is invariant under permutation of a reactor's
message reactions whenever their triggers are distinct — with a companion fact that the translator always
makes them distinct. That converts "stage F's ordering theorems have no run-level consequence" from prose
into something the build checks, and it is the honest statement of what the general family's LF semantics
currently says about priority. Lemma 3, over `after d` delays, is untouched by any of this: it is
priority-free, and `#106` can proceed with it.

### The transferable check

**A scope disclaimer is a claim, and it goes stale under the argument that precedes it.** F76 established
that the run-level ordering choice is made by a selector that ignores everything stage F sorts, then
exempted the same-actor case in one sentence by pointing at the design's scope wording rather than at the
selector. The exemption was inherited by §7 item 5 as *"Lemma 2's same-actor case and Lemma 3 are sound
under every candidate repair"*, and would have been inherited by row 8's Lean.

The narrower version, and the reason this is the third finding of its family after F75 and F79: **the
cheapest place for a false claim to survive is the sentence that says a finding does not apply.** Findings
are audited; their scope limits are not, because a limit reads as modesty. F76 is a careful entry, it was
right about the mechanism, and it disclaimed one case using the one word — "orthogonal" — it had just
disproved.

---

## F81 — stage F's message-server sort is now a proof obligation of a theorem it cannot affect, and that theorem's own premises have no public discharger

*Measured and read.* Filed with the commit that lands
`Correctness.generalReactionFor?_perm_of_compiled`, the closing theorem F80 asked for, and about that
theorem's own text rather than about anything it replaces. Two parts. The first completes F80 with
something F80 could not see, because it is visible only once the theorem exists; the second is a limit on
what the theorem can currently be used for, and it is the reason `#129` does not become unblocked by it.

### Part 1 — the sort has to be reasoned around to prove a property it does not change

F80 established by argument that stage F's two ordering theorems are run-level **inert**: the selector
that decides which reaction fires ignores everything stage F sorts. The closing theorem converts that
from prose into something the build checks. What the build now also shows is stronger, and is a cost
rather than a defect in either language.

`Translation.compileGeneralReactiveClass_reactionTriggers` keys the emitted trigger list to
`generalPriorityOrderedMessageServers reactiveClass` — the **sorted** list,
`DTR.GeneralMessageServerPriority.normalize reactiveClass.messageServers`. The distinctness ladder
underneath it is proved at the model's **own** list, because that is where the guard's hypotheses live.
So `Translation.compileGeneralReactiveClass_reactionTriggers_nodup` has to `unfold
generalPriorityOrderedMessageServers` and cross the sort by
`DTR.GeneralMessageServerPriority.normalize_perm`, permuting its conclusion, before the ladder applies.

The sort therefore appears in the **proof** of the closing theorem and nowhere in its **statement** —
and by the theorem itself it *cannot* appear in the statement, since `reactionFor?` is invariant under
exactly the permutation being crossed. Stage F's level-2 ordering is, at this point in the development,
a step that every downstream distinctness result must pay for and that no downstream statement can
mention. That is a real observation about the design and not a complaint about the proof: a sort whose
only reachable consequence is an extra permutation lemma in each consumer is carrying cost with no
theorem attached. Stage G row 9 (`#108`), which makes a populated LF reaction `priority` a
well-formedness violation, is the first place that could change — it is the only tracked work that gives
the target a way to *observe* an order at all.

### Part 2 — three guard-relative hypotheses, and no public route to any of them

The closing theorem takes the three distinctness facts as hypotheses, at the source model's own lists.
That is the `#60`/F50 shape and it is deliberate. What is new, and measured 2026-08-26 by enumerating
every `Nodup`-concluding theorem in `Relico/Translation/GeneralBasic.lean` and
`Relico/Translation/GeneralRouting.lean` and then reading each one, is that **nothing public discharges
any of the three**:

*Input port names.* `Translation.inputPortNames_nodup_of_wellFormed` is exactly the projection wanted —
it turns a decided `LF.GeneralReactor.declaredNames` `Nodup` into this hypothesis's spelling — and it is
declared `private`. Its own docstring names the consumer it was written for,
`Translation.generalRouteEndpoints_nodup`, which is in the same module.

*Action names* and *message-server names.* There is no theorem anywhere in the repository whose
conclusion is either `Nodup`. The third fact is a conjunct of `DTR.GeneralModel.namesUniqueAndValid`, so
a projection could be written; the second has no obvious decided source at all, because
`generalActionNamesOf` mixes per-server names with the per-site names the F56 repair introduced.

The measurement that finds this is worth naming, because the obvious one fails. Grepping the
hypotheses' spellings is reassuring and wrong: `hInputPortNames` occurs twenty-seven times across three
modules, `hActionNames` twelve, `hServerNames` seven — and **every** occurrence is a hypothesis being
taken or forwarded, never a conclusion being produced. A hypothesis threaded through a long ladder looks
identical, under grep, to a hypothesis that gets discharged somewhere. Enumerate theorems by what they
**conclude**.

*Consequence, stated so it is not read as more than it is.* The theorem is sound and its premises are
satisfiable — they hold of every well-formed model. But it cannot yet be **applied** to a concrete
translated program without assuming them, so it does not by itself unblock `#129`, whose `.consume` case
still waits on F76's repair decision. Discharging the premises belongs to the commit that first has a
consumer, not to the one that states the theorem; de-privatising
`inputPortNames_nodup_of_wellFormed` ahead of that consumer would widen a module's public surface for a
caller that does not exist, which is the F75 defect in the other direction.

### The transferable check

**A guard-relative theorem is only as finished as the projection that discharges its guard, and the
theorem cannot show you whether that projection exists.** The `#60`/F50 shape — record the refuted
obligation, prove the scoped version against hypotheses the guard decides — is the right instrument, and
it has now been used often enough in this repository that its one blind spot is worth stating: the
scoped version reads as complete from its own text. Nothing in a statement distinguishes a hypothesis
that a public lemma supplies from one that no lemma anywhere supplies.

Narrower than F75 and F80, and a different family from both: those two are about claims going stale
against artefacts, this one is about a claim that was never checkable from the place a reader checks.
The check is cheap and belongs in every commit that lands a guard-relative theorem — for each
hypothesis, name the declaration that concludes it, or record that none does.

## F82 — the invariance F80 asked for holds, but only against a premise about every part of the program the permutation did not touch, and F80's own sentence has no room for it

F80 asks for the refutation of Lemma 2's run-level content "stated as a theorem", in the shape
`reactionFor?` is permutation-invariant "and hence `LF.GeneralStep`". Item 3 delivers that, and the
delivery is clean: `Common.WeakStep.mono`, `LF.GeneralStep.congr_of_projections` and
`Correctness.generalReactionFor?_perm_of_compiled_pointwise` compose into
`Correctness.generalWeakStep_perm_of_compiled`, which says that reordering a translated reactor's message
reactions changes no weak transition. What is worth recording is the premise that composition needed and
F80 did not name.

**The measurement.** `generalReactionFor?_perm_of_compiled` is stated at one instance and one event kind,
and those two restrictions behave differently. The `kind` restriction is not one: no hypothesis of that
theorem mentions `kind`, so quantifying over it is `fun kind => …`. The instance restriction is real.
`hLeft` and `hRight` pin the instance whose reactor is permuted, and **nothing in the statement constrains
either program at any other instance** — the two programs may disagree arbitrarily elsewhere and the
theorem still holds, because it never looks there.

The step relation does look there. `LF.GeneralStep.fire` resolves its reaction at `event.target`, and the
event is chosen by the runtime out of the pending queue, not by whoever states the theorem. So a claim
about one permuted reactor cannot become a claim about the step relation without saying what the two
programs do at the instances the permutation left alone. The closing theorem therefore carries

```
hElsewhere : ∀ other, other ≠ target → left.reactorOfInstance? other = right.reactorOfInstance? other
```

which is true of the situation the theorem exists for and absent from the sentence that commissioned it.

**Why a hypothesis and not a construction.** The alternative is a function that rebuilds a program with one
reactor's reaction list permuted, from which `hElsewhere` would follow by computation. That function does
not exist, and `LF.GeneralProgram.reactionFor?_perm` already records why it should not be written: no stage
has needed it, and adding it so that a theorem reads more tidily puts a definition in the tree with no
caller. The premise is the honest form. It also composes: the caller that eventually applies this — the
`.consume` case, once F76 is decided — will hold `hElsewhere` for the same reason it holds `hConnections`,
namely that it permuted one list and touched nothing else.

**What it costs.** One more guard-relative premise, on top of the three F81 measured. The count of premises
with no public discharger in this ladder is now four, and the honest reading of that is not that the
theorem is weak but that the ladder has consistently chosen to state true things against decidable
hypotheses rather than to widen module surfaces ahead of consumers.

**Two things deliberately not stated, recorded so their absence does not read as an oversight.** There is no
general-family `TauSteps` corollary: `WeakStep.mono` consumes `TauSteps.mono` internally on its three
segments, so a wrapper would have no caller. And there is no biconditional at the weak level, although
there is one at the step level (`LF.GeneralStep.congr_iff_of_projections`) — the step-level hypotheses are
symmetric equations, whereas the weak-level composition carries a translator hypothesis on one side only,
which `generalReactionFor?_perm_of_compiled` intends ("`right` is not required to be a translation of
anything"). An `Iff` here would force a translation hypothesis onto the reordered side.

**A placement fact worth keeping.** `Relico/Correctness/GeneralWeakBisimulation.lean` is the only module in
the repository that can see all three ingredients: it imports `Relico.Common.WeakTransition` directly and
reaches `Relico.Correctness.GeneralCorrespondence` through `Relico.Correctness.GeneralTimeEquivalence`.
`GeneralCorrespondence.lean` cannot host the composition — it never imports `Common.WeakTransition` — and
`Relico/LF/GeneralSemantics.lean` records under F70 that instantiating `Common.WeakStep` is G2c's job, not
the foundation's. The composition's home was therefore forced by the import graph, which is the third time
in this stage that graph has decided a placement rather than taste deciding it.

### The transferable check

**An invariance claim about a local edit needs a premise about everything the edit did not touch, and the
sentence commissioning the claim almost never contains that premise.** F80's wording is about a reactor's
reaction list; the theorem that discharges it is about a whole program, because the relation it quantifies
over reads the program at instances the wording never mentions. The gap is not an error in F80 — it is what
happens when a finding is written at the granularity of the thing that changed and discharged at the
granularity of the thing that observes it.

So when lifting a local invariance to a relation: list what the relation reads, not what the edit wrote.
Here that list was already available and already short — `LF.GeneralStep` reads its program through exactly
two projections — and reading it off is what turned the lift into three composition steps with no
induction anywhere.


