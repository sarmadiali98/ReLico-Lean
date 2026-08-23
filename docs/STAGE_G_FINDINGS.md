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
