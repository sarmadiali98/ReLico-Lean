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




