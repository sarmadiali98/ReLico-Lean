# Stage G design — priority as *behaviour*: selection from the state, and execution correspondence

**Status.** Written 2026-08-23, after stage F landed at `d91a1be`. Not started. All five decisions in §15
are settled — four by the decision-maker on 2026-08-23, one by measurement — and §7 was **rewritten** the
same day after reading the paper, which changed stage G's central theorem from a step correspondence to
weak bisimulation. The stage's correctness target is now the paper's own `Theorem 1`.

**Provenance.** Every claim below is either a citation to repository source at `path` with a declaration
name, a citation to a tracked document, a citation to the canonical paper, or explicitly labelled as a
proposal. Where this document disagrees with an earlier design document, the disagreement is stated rather
than silently corrected — three such corrections already landed in `docs/STAGE_D_DESIGN.md` on
2026-08-23, all of which credited stage G with work that stage F actually did. Where it diverges from the
**paper**, §7 says so explicitly and gives the reason; there are exactly three such divergences and each
is held to the narrowest form that still works.


---

## 1. What stage G is, stated from the project's own obligation list

`docs/trusted-boundary.md:28-38` is the authoritative statement of what the project undertakes to
prove. Of its nine numbered aims, **stage G owns three**, and they are the last three:

> 7. designer-specified priorities are preserved;
> 8. every permitted source execution has a corresponding target execution;
> 9. every target execution corresponds to a permitted source execution.

And the sentence immediately after the list, `docs/trusted-boundary.md:40`, is stage G's mandate in the
project's own words:

> The correctness theorem must preserve the permitted source execution structure. It must not assume
> that every permitted schedule is observationally equivalent.

This is worth dwelling on, because it settles a question that would otherwise be a judgement call. The
obvious reading of "stage G does priority" is that stage G is a *refinement* — a nicety on top of a
translation that already works. It is not. Aims 8 and 9 are the two halves of the correctness statement
itself, the forward and backward simulation, and `:40` explicitly forbids discharging them by declaring
schedules interchangeable. A translator that emits reactions in priority order but proves nothing about
executions has met aim 7's *letter* on the emitted text while leaving 8 and 9 untouched. That is exactly
the state stage F left the general family in, and §2 measures it.

**One-line statement of stage G.** Make the general family's priority claim a statement about
*executions* of the generated program rather than about the *order of lines in* the generated program,
by (a) deriving the ready cohort from the configuration instead of accepting it as an argument, (b)
selecting from that cohort by actor priority, and (c) proving the forward and backward correspondence
between a source dispatch step and a target reaction firing, guard-relative.

## 2. What stage F delivered, and the exact size of the gap

Stage F is complete and its result is real. Both levels landed and are gated: level 1 orders the port
reactions inside one message server's group by the priority of the **sending actor**, level 2 orders the
groups themselves by the priority of the **receiving message server**, and the two compose. The sort in
`Relico/DTR/GeneralPriority.lean` carries a locally defined `Sorted` predicate with an unconditional
sortedness theorem and a guard-relative strictness theorem per level, plus a `rfl` value pin in
`Relico/Tests/GeneralPriority.lean` that catches what sortedness cannot — tie order, and the direction of
the absence convention.

What that buys, precisely: **the emitted program's text is in priority order, and this is proved.** What
it does not buy, and stage F's own design says so at §1.3, is any statement about what the program
*does*. Three measurements bound the gap:

1. **The DTR side selects nothing.** `GeneralConfiguration.readyActors`
   (`Relico/DTR/GeneralState.lean:659`) returns the whole cohort, and its docstring says why: *"The
   cohort is a function of the configuration alone. Nothing about the model is consulted, because
   whether an actor has a message it may take now is a question about its bag and the clock; which of
   the ready actors is then selected is what priority decides, and that is the next stage's concern."*
   Stage G is that next stage. There is no `selectedActor` on the general DTR side at all.
2. **Neither side has a scheduling module.** `DTR.PriorityServerNamePrecedesOrEqual` and
   `LF.ReactionActionPrecedesOrEqual` exist only for the multi-store family. The general family has a
   *sort* and order-preservation theorems about compilation; it has no predicate that relates two
   elements of a *run*.
3. **The only ordering evidence is text.** `priorityFanInModel` in the printer test main is a
   hand-built model whose declaration order deranges its priority order — four instances declared
   `collector, alpha, beta, gamma` at priorities `4, 3, 1, 2`, emitting `beta, gamma, alpha, collector`,
   a permutation with no fixed point — and the assertions over it compare **emitted strings**. No
   executed program in the repository exhibits priority order, because no generated general-family
   program has any observable output at all (§10).

So the gap is not a missing lemma. It is a missing *layer*: the general family has a compile-time order
theory and no run-time order theory, and aims 8 and 9 live entirely in the second.

## 3. The defect stage G must close, already formalised as a theorem

The actor-priority layer that does exist has a shape defect, and it is pinned by
`readyActors_discriminates` (`Relico/DTR/GeneralState.lean:1149`, proved by `decide`). The theorem is a
five-way conjunction over a two-actor configuration at time 5 in which one actor holds a message due at
3 and the other's bag is empty. It establishes, simultaneously:

* the fabricated cohort satisfies `DTR.cohortSimultaneous`;
* the **idle** actor's record satisfies `earliestReady` against that cohort;
* that same actor's `dueArrival` at the configuration's current time is `none` — it has nothing to take;
* the configuration's own `readyActors` is the singleton list holding the *worker*;
* and therefore `readyActors config ≠ fabricatedCohort`.

The point is not that some list is unequal to another. It is that `cohortSimultaneous` and
`earliestReady` — **the only constraints existing selection statements place on their cohort argument**
— are jointly satisfiable by a cohort the state does not license, one that even certifies an idle actor
as earliest-ready. A theorem of the form "for any cohort satisfying these predicates, selection behaves
thus" has therefore assumed its subject rather than derived it, and every selection statement in that
layer has that shape. That is why the defect is worth a theorem rather than a comment.

**And the precedent repeats the defect.** The multi-store dispatch relation
`ActorPriorityDispatchStep` takes `ready : List ReadyActor` as an explicit argument
(`Relico/Correctness/GlobalMultiStorePayloadActorDispatchCorrespondence.lean:15-45`), constrained only
from outside. So mirroring the precedent verbatim would import the defect into the general family. Stage
G deviates deliberately: **its step relation is keyed on `GeneralConfiguration.readyActors config`, a
derived value, and takes no cohort parameter.** `readyActors_discriminates` is the evidence that this is
a correctness improvement and not a stylistic preference, and it is the reason the general family's
version cannot be a transcription of the multi-store one.

## 4. The shape to mirror, and where it comes from

The multi-store payload family already carries a full actor-selection development. It is **four
modules**, not one file, and the split is the thing worth copying:

| Role | Multi-store module | Anchor declaration |
|---|---|---|
| Source-side eligibility | `Relico/DTR/GlobalMultiStorePayloadActorPriority.lean` | `eligibleActorNames` (`:236`) |
| Target-side order | `Relico/LF/GlobalMultiStorePayloadActorOrder.lean` | `lookupReadyTargetActor` (`:51`) |
| Selection correspondence | `Relico/Correctness/GlobalMultiStorePayloadActorSelectionCorrespondence.lean` | `actorSelectionEligible_compile_iff` (`:327`), `_forward` (`:360`), `_backward` (`:379`), `eligibleActorNames_compile_eq` (`:399`) |
| Dispatch-step correspondence | `Relico/Correctness/GlobalMultiStorePayloadActorDispatchCorrespondence.lean` | `actorPriorityDispatchStep_forward_of_targetBase` (`:15`), `actorOrderDispatchStep_backward_of_sourceBase` (`:81`) |

Two features of that shape are load-bearing and stage G adopts both.

**The `_forward` / `_backward` pair is aims 8 and 9, spelled out.** Not one iff, but two implications
each conditioned on the *other* side's base correspondence — `_forward_of_targetBase`,
`_backward_of_sourceBase`. This is the honest form: neither direction is free, and the naming makes the
hypothesis visible at the use site. A single symmetric statement would hide which side's well-formedness
is being assumed.

**Eligibility and order are separated from the step.** Whether an actor *may* act is a different
question from what a step *does*, and proving the first as a standalone `iff` over compilation is what
makes the second tractable. Stage G keeps that separation.

**The precedent reaches further than selection, and this section first understated it (F65).** The same
family also carries a finite-execution development, and `trusted-boundary.md` aims 8 and 9 are **already
proved** there — twice, once without priorities and once with:

| Role | Multi-store module | Anchor declaration |
|---|---|---|
| Source finite executions | `Relico/DTR/GlobalMultiStorePayloadFiniteExecution.lean` | `Steps` |
| Target finite executions | `Relico/LF/GlobalMultiStorePayloadFiniteExecution.lean` | `Steps` |
| Execution correspondence | `Relico/Correctness/GlobalMultiStorePayloadFiniteExecutionCorrespondence.lean` | `ForwardStepsCompatible`, `BackwardStepsCompatible`, `finite_forward`, `finite_backward` |
| Priority-aware traces | `Relico/Correctness/GlobalMultiStorePayloadActorFiniteExecution.lean` | `SourceActorPriorityDispatchSteps`, `sourceActorPriorityDispatchSteps_forward`, `actorDispatchEventTraceCorresponds_length_eq` |

**That shape is strict lock-step — a stronger statement than the paper's, at a coarser granularity.**
`sourceActorPriorityDispatchSteps_forward` produces a target execution over the *same* `frames` list the
source execution was indexed by, and `actorDispatchEventTraceCorresponds_length_eq` proves
`sourceEvents.length = targetEvents.length`: one target event per source event, no internal steps, no τ.
Stage G does not extend it, and neither reason is that it is wrong. First, every frame carries the `ready`
snapshot that §3's defect is about, and `ActorDispatchFrame`'s docstring concedes the point in advance:
*"The ready-actor snapshot is local to this transition. It is deliberately not fixed globally across an
arbitrary execution."* Second, the theorem this project is measured against is the paper's `Theorem 1`,
which is weak bisimilarity. Where the general family's τ sets turn out empty, stage G's result and this
one coincide.

The one deviation is §3's: no cohort parameter. Concretely, where the multi-store relation reads
`ActorPriorityDispatchStep request ready sourceModel actorName before after …`, the general source
transition reads `GeneralDtrStep sourceModel config action configAfter` and obtains the cohort internally
as `GeneralConfiguration.readyActors config`. The cohort is a *derived* quantity, so nothing outside the
relation can supply a fabricated one.


## 5. The guards, and why they are hypotheses rather than well-formedness clauses

This is settled, not open. `docs/STAGE_B_DESIGN.md:593-611` records the decision of 2026-08-18 — option
**D**, guards as theorem-level hypotheses — under a heading that says the consequences are *"now binding
on stage B and on every later stage"*. The two that bind stage G:

> *"Every stage-F/G correctness theorem carries them as explicit hypotheses. A theorem that needs
> determinism and does not name them is a bug in that theorem."*

> *"The three actor-tie and two message-server-tie fixtures identified in §7's table are therefore
> elaborable but not theorem-eligible."*

So `GeneralModel.wellFormed` still does not mention priority — it conjoins only the four structural
clauses — and `ActorPrioritiesDistinct` / `MessageServerPrioritiesDistinct` live in
`Relico/DTR/GeneralWellFormed.lean` as `Prop` with hand-written `Decidable` instances. Every stage G
statement that claims a *unique* selection or a *unique* execution names the guard it needs.

The asymmetry between the two guards, measured during stage F, decides how the hypotheses thread and is
easy to get wrong: `ActorPrioritiesDistinct` is a single model-wide `Nodup` over `model.instances`, so a
bridge to it is literally `:= hDistinct`; `MessageServerPrioritiesDistinct` is
`∀ reactiveClass ∈ model.classes, DTR.GeneralMessageServers.PrioritiesDistinct
reactiveClass.messageServers`, so a bridge is `hDistinct reactiveClass hMem` and that membership
argument propagates through every lemma beneath it. Stage G's selection theorems need the **actor**
guard; only theorems that reach into a class's reaction group need the second.

**A statement stage G must be careful not to make.** With the actor guard, selection is unique *among
distinct-priority actors*. Without it, ties are possible and the paper supplies no tie rule (F27, and
the stage F verdict at `docs/PAPER_CORRECTIONS.md` on `#79`: the SOS take rule has no priority term at
all). Stage G therefore proves determinism relative to the guard and proves **nothing** about tie
behaviour, rather than quietly picking declaration order and calling it correct. Tie fixtures stay
elaborable and stay outside every theorem.

## 6. G1 — selection from the state

**Deliverable.** A general-family source-side selection function and its characterisation, replacing
"take a cohort as an argument" with "derive the cohort, then select".

```
-- Relico/DTR/GeneralActorSelection.lean  (new)
def GeneralConfiguration.selectedActor
    (model : DTR.GeneralModel) (config : DTR.GeneralConfiguration) : Option ReadyActor
```
selecting from `readyActors config` the **lexicographic** minimum on `(logicalTime, priority)` — earliest
arrival first, and the existing `GeneralPriority.PriorityPrecedesOrEqual` breaking ties among simultaneous
records, with stage F's absence convention (annotated before unannotated) reused rather than restated.

**Why lexicographic and not priority-first — measured 2026-08-23, before any code.** Timed Rebeca is
time-driven first and priority-driven second, and the state layer permits the distinction to bite:
`earliestDueArrival` (`Relico/DTR/GeneralState.lean:142`) returns the minimum arrival **among the messages
whose arrival is `≤ now`**, and `readyActorsOf` (`:621`) puts that arrival into each record as its
`logicalTime` while contributing no record for an actor with nothing due. Nothing constrains two ready
actors to carry the *same* arrival, so a cohort with mixed arrival times is reachable, and a priority-first
selection would let a later message overtake an earlier one whenever the later actor had the better
priority. That is a soundness defect no amount of proof would catch — it would prove the wrong function
correct — and it is the reason `cohortSimultaneous` and `earliestReady` exist at all: they are the
"restrict to the earliest arrival first" half, previously left to the caller. `selectedActor` absorbs
that half instead of assuming it.

**Theorems, in dependency order.**

1. `selectedActor_mem` — the selected record is a member of `readyActors config`. Unconditional.
2. `selectedActor_isSome_iff` — selection succeeds exactly when the cohort is non-empty. Unconditional,
   and the statement that makes `Option` safe to use downstream.
3. `selectedActor_minimal` — no member of the cohort strictly precedes the selected record.
   Unconditional; this is the analogue of stage F's sortedness theorem and, like it, cannot see ties.
4. `selectedActor_unique` — **guard-relative** on `ActorPrioritiesDistinct model`: any member that is
   not strictly preceded *is* the selected record. This is the theorem that discharges determinism, and
   the one that is false without the guard.
5. `selectedActor_ne_fabricated` — the reason the layer changed shape: a restatement of
   `readyActors_discriminates` in terms of `selectedActor`, showing that the discriminating configuration
   selects the worker and that no cohort-parameterised statement could have. This is cheap (`decide` on
   the existing constants) and it is the regression pin for the whole redesign.

**What G1 does not do.** It does not touch `readyActors`, `readyActorsOf`, `earliestDueArrival` or their
four soundness/completeness theorems; those are correct and stage G builds on them. It does not delete
`cohortSimultaneous` or `earliestReady` — they remain meaningful as *properties*; what stops is using
them as a cohort's only credential.

## 7. G2 — weak bisimulation: the paper's Theorem 1, for the general family

**This section was rewritten on 2026-08-23 after reading the paper, and then corrected the same day after
measuring the repository.** The original plan was a strong step-by-step correspondence with the lift to
whole executions stated as owed; that is *not* the paper's architecture, so it was replaced. The
replacement then carried an error of its own, recorded as **F64**. It claimed the strong version is
*false* of our generated programs because "the emitted reactor contains a `drain_reaction` whose firings
have no source counterpart". **The premise is real; the conclusion is false.** `drain_reaction` *is*
emitted — it is the message reaction generated from the DTR message server `drain` of
`fanInReceiverClass`, a `DTR.GeneralReactiveClass` in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean` that is fed through the real translation — and that
is precisely why it has a source counterpart: the server it is named after. It also never fires in that
model, because nothing sends `drain`, so it contributes no firings to correspond to anything. A
never-firing reaction is not an unmatched one. What the translator actually emits is measured next, and it
admits no internal reaction at all. Both the refuted plan and the withdrawn justification are recorded
here rather than deleted, because each is a conclusion a reader would otherwise expect to find.

**What the translator actually emits, measured 2026-08-23.**
`compileGeneralMessageServerReactionGroup` compiles a message server's body **once** and passes the same
`compiledBody` to both `assembleGeneralMessageReactions` and `assembleGeneralPortReactions`. A port
reaction therefore *runs the server's own body* rather than forwarding to the server's logical action.
Every reaction the general translator emits has a source counterpart — message reactions to self-send
sites, port reactions to routed send sites, the startup reaction to the constructor — so **no emitted
reaction is internal**. Weak bisimulation is consequently adopted on the paper's authority, `Theorem 1`
being the theorem this project claims to implement, and *not* because our output refutes lock-step. If the
granularity G2a picks leaves both τ sets empty, weak bisimilarity specialises to lock-step: a
*strengthening* of the stated result rather than a contradiction of it.

**What the paper proves.** `Definition 1` is weak bisimilarity w.r.t. a bijection `ϕ` on actions, with
the two standard transfer conditions and `⇒` expanded as `τ* γ τ*` for `γ ≠ τ`. `Theorem 1` states
*"TS_dtr is weakly bisimilar to TS_lf w.r.t. bijection ϕ"*, and its proof constructs a relation `R` and
discharges Definition 1's transfer conditions using Lemmas 1–3. There is **no separate induction over
executions** in the paper: whole-run agreement is what weak bisimilarity *means*, and the only induction
is inside Lemma 1 (Time Equivalence), which is proved *"by induction on the number of DTR transitions"*
carrying a bag↔queue bijection as its hypothesis.

**The relation, transcribed.** The paper's `R` relates a DTR global state mapping each actor `x` to
`(ex, bx, πx)` with an LF global state mapping each reactor `r = map_A(x)` to `(ηr, qr, µr)`, requiring
`ex ≡ ηr` (translated state variables hold identical values), `bx ≡ qr` (the Lemma 1 bijection between
pending DTR messages and LF triggers, corresponding pairs sharing an arrival time), and `πx ≡ µr`
(corresponding continuations). It holds initially because both executions start empty. Stage G defines
`GeneralStateCorrespondence` with exactly these three components, per actor, keyed through the existing
translation's reactor naming rather than an abstract `map_A`.

**What is τ, and why this is the crux.** The paper makes assignments τ on both sides — a DTR assignment
updates the local environment as `si →τ si[x ↦ …]` and the LF `ASSIGN` rule matches it — and it abstracts
scheduler stuttering steps in the same breath (`:1258`). Stage G's τ set is therefore: assignments on both
sides, and on the LF side the scheduler's own steps, which are the **only** τ candidates on that side now
that no emitted reaction is internal. Observable actions are message takes on the DTR side and the
corresponding message-or-port reaction firings on the LF side, related by `ϕ`. Getting this classification
right *is* G2's design content; everything else is bookkeeping over it. Note what it now rests on: the τ
sets are non-empty only if the LTSs are finer-grained than one-step-per-dispatch, so **G2a's granularity
choice decides whether any τ exists at all**, and that choice must be made explicitly rather than
inherited.

**Deliverables.**

```
-- Relico/Semantics/GeneralLTS.lean                    (new)  both LTSs, the action type, tau
-- Relico/Semantics/GeneralCorrespondence.lean         (new)  R, and that it holds initially
-- Relico/Correctness/GeneralTimeEquivalence.lean      (new)  Lemma 1: the induction and its invariant
-- Relico/Correctness/GeneralWeakBisimulation.lean     (new)  Theorem 1: both transfer conditions
-- Relico/Correctness/WeakBisimulationTrace.lean       (new)  generic: bisimilarity to trace agreement
```

The two transition relations are `GeneralDtrStep sourceModel config action configAfter` and
`GeneralLfStep program state action stateAfter`, with `action : GeneralAction` carrying a `tau`
constructor. **Neither takes a cohort parameter** — §4's one deliberate deviation from the multi-store
precedent, for §3's reason.

**Theorems, in dependency order.**

1. `generalCorrespondence_initial` — `R` relates the initial states. Unconditional; the paper's "holds
   initially" line, and cheap.
2. `generalTimeEquivalence` — Lemma 1. Every DTR event at logical time `t` corresponds to an LF event at
   tag `(t, m)`, by induction on transitions, carrying the bag↔queue bijection. This is where the
   chaining invariant lives, and it is the one genuinely inductive obligation.
3. `generalPriorityPreservation` — Lemma 2 at *run* level, resting on stage F's compile-time ordering
   theorems rather than restating them. **Same-actor case only as the paper states it**; see the
   divergence note below.
4. `generalCausalityPreservation` — Lemma 3, over `after d` delays, reusing stage E's delay machinery.
5. `generalWeakBisimulation_forward` / `_backward` — Definition 1's two transfer conditions, each
   producing a *weak* transition `τ* γ τ*` on the other side. **Guard-relative** on
   `ActorPrioritiesDistinct`: without it the target's chosen reaction need not be the source's chosen
   actor, and the witness for the existential cannot be constructed.
6. `weakBisimulation_traceAgreement` — **generic, model-independent**: from a weak bisimulation, the two
   systems agree on finite observable traces. This is what discharges `trusted-boundary.md` aims 8 and 9
   for the general family outright instead of owing them, and it is proved once over an abstract LTS, so
   it costs nothing per family. It is **not** what first gives this repository a finite-execution result:
   the multi-store family already has two, in a strict lock-step shape — see §4, and **F65** for the
   correction this sentence replaces.

**Scope limit, stated rather than discovered.** Aims 8 and 9 are discharged for **finite** executions.
Infinite runs would need a coinductive treatment, which the paper does not give either, and which no
part of this repository currently needs. That limit is a scope statement, not an owed theorem.

**Divergences from the paper, kept to the minimum and documented precisely.** Three, and all three are
forced:

* **Lemma 2's different-actor mechanism is not realizable and stage F already routed around it.** The
  paper argues that `map_A` orders reactor *declarations and instantiations* by `prty_g`, and that
  *"LF's deterministic scheduler executes upstream reactors before downstream reactors"*, so
  `prty_g(x) < prty_g(y)` yields `ri` before `rj`. Declaration and instantiation order does **not**
  order reactions across unconnected reactors at the same tag in Lingua Franca; only dependencies do.
  Stage F therefore realized cross-actor order as **reaction declaration order inside the receiving
  reactor**, ordering a message server's port reactions by *sending* actor priority — which is sound
  because those reactions are in one reactor, where declaration order is decisive. Stage G's
  `generalPriorityPreservation` rests on that mechanism. The paper's same-actor case (`prty_l`, ordering
  a reactor's own reactions) is adopted unchanged; only the different-actor argument is replaced, and the
  *conclusion* of Lemma 2 is preserved in both cases.
* **Actor priority participates in selection, which the paper's SOS take rule does not do.** Priority
  appears in the paper's correctness development (`prty_l`, `prty_g`, Lemma 2) and not in either SOS
  table — the verdict recorded when `#79` closed. §6's `selectedActor` uses it, on the authority of the
  2026-08-16 scope decision that actor priorities are in scope and that the repo is definitive where the
  two conflict. The divergence is held to the minimum available: priority discriminates **only** among
  equal-arrival candidates, so the paper's arrival-first rule is untouched and the extension is confined
  to a case the SOS leaves unordered.
* **Finite executions only**, as above.

Everything else follows the paper's shape deliberately, including the decision to prove transfer
conditions rather than a bespoke simulation: an artifact that proves a *different* theorem from the paper
it accompanies is worth much less than one that proves the same theorem executably.


## 8. G3 — F27's dropped field: justify it, reverse it, or refuse it

F27 is assigned to stage G in writing. `docs/STAGE_D_FINDINGS.md:506-509`:

> *"F27 belongs to stage G, which is where local message-server priority becomes observable and where the
> drop currently pinned by `assembleGeneralMessageReaction_priority` must be justified or reversed."*

The state of play: `LF.GeneralReaction.priority` exists as a field and is always emitted as `none`, and
three theorems pin that — `assembleGeneralMessageReaction_priority`,
`assembleGeneralPortReaction_priority`, `assembleGeneralStartupReaction_priority`. `docs/STAGE_F_DESIGN.md`
§7.4 correctly classifies them as **alarms rather than debt**, on the ground that wiring
`priority := some n` would produce byte-identical output text — the printer does not read the field.

That argument is sound and is also the problem. A field the printer never reads, set to `none` by three
theorems, is a **silent drop**: a future author who sets it will see a green build and unchanged output.
The standing doctrine on target-caused limitations is that the response is a checkable refusal, never a
quiet under-delivery. So this document takes a third option the finding did not list:

**G3, decided 2026-08-23.** Add a clause to `LF.GeneralWellFormed` requiring `reaction.priority = none`,
making a populated field a **well-formedness violation** rather than a no-op, and record in the field's
docstring that Lingua Franca expresses reaction precedence through declaration order within a reactor —
which is precisely the mechanism stage F used — so a per-reaction priority attribute has no target
spelling to compile to. The three inert theorems then become consequences of the clause instead of
coincidences, and the alarm becomes an invariant. This is an application of the standing doctrine rather
than a free choice, and it was put to the decision-maker in those terms and confirmed.


**Precondition, and it is a probe not an argument.** The justification above asserts something about
`lfc` that this repository has not measured: that there is no accepted reaction-priority attribute in
Lingua Franca 0.11.0. Before G3 lands, one probe must run — emit a reaction carrying a candidate
priority attribute and record whether `lfc` accepts, rejects, or silently ignores it. **If `lfc` accepts
one, G3 flips from "justify" to "reverse"** and the field gets wired to the printer instead, which is a
larger change and belongs in its own commit. Writing the justification before the probe would be an
inferred claim dressed as a read, which is the failure mode F51 records.

## 9. G4 — the `switch-pair` benchmark, which does not exist

`docs/STAGE_F_DESIGN.md:18-19` names a benchmark called `switch-pair` as stage G's, and that name appears
**nowhere else in the repository** — no fixture, no `.rebeca` file, no exporter output, no definition of
what it would contain. It is a forward reference that was never redeemed.

Two honest dispositions, and this document takes the second.

The first is to define it: a two-actor model in which each actor sends to the other, with priorities
arranged so that the priority order and the declaration order disagree, exercised end to end through the
real toolchain. The attraction is that it would be the first general-family model whose *behaviour*
depends on priority.

The second, taken here: **G4 is not a benchmark, it is a fixture, and it is subsumed by G5.** The
standing 2026-08-17 direction puts all benchmark work on hold until the translator accepts the paper's
DTR fragment, and a benchmark's defining property — that it is scored, tabulated in the suite, and
counted in `obligations.tsv` — is exactly what the hold suspends. What stage G actually needs from
`switch-pair` is a *witness*: a model whose run distinguishes priority order from declaration order.
That is G5's content. So G4 is discharged by renaming: the name `switch-pair` is retired, the forward
reference at `docs/STAGE_F_DESIGN.md:18-19` is corrected to point at G5's witness, and no suite row, no
`POSITIVE_COUNT` and no obligation count moves. Anything else would start benchmark work under a
different label, which the hold forbids in substance as well as name. **Confirmed 2026-08-23**: the name
is retired and the witness inherits its purpose.


## 10. G5 — the runnable witness

**G5, decided 2026-08-23: widen, and make the priority order observable.** Add one statement
constructor to each side — `DTR.GeneralStmt.trace` carrying a literal tag, and `LF.GeneralStmt.trace`
printing it — with the printer emitting a single C++ line into the reaction body, and a preamble only if
the probe shows one is needed. Then build one witness model whose two actors' priority order deranges
their declaration order, run it through real `lfc`, and assert on the **observed output order**. Gate it in
`check-general-lf-target.sh` as a new marker so the existing exit-code-only contract is extended rather
than reinterpreted.

The alternative — stage G stays proof-only and observability moves to stage H — was rejected on the
ground that it would prove aims 8 and 9 about a program nobody has ever seen behave. That is a real cost:
stage F's ordering is currently gated as *text*, and a translator that emits the right declaration order
while running in the wrong one would pass every gate in the repository today.

**The problem, measured.** No generated general-family program has any observable output. There is no
print statement in `DTR.GeneralStmt` (two constructors: `assign`, `send`), no preamble field on
`LF.GeneralReactor`, and no `cout`/`printf` anywhere in `Relico/LF/GeneralCppPrinter.lean`. The only
observable of a generated program is `lfc`'s exit code, which is why
`frontend/check-general-lf-target.sh` checks exit codes and nothing else — a design stage E's document
calls **forced, not lazy**, with an explicit instruction not to "improve" it by diffing a run log.

**Why the scope doctrine does not dispose of this.** The standing rule is that when a limitation is the
*target's* fault, dependent DTR models go out of scope through a checkable guard refusal plus a stated
fragment restriction. That rule does not apply here, and the distinction matters: `lfc` prints perfectly
well. The blocker is on **our** side — our AST has no statement to print with and our printer has no
preamble to declare one in. This is an AST widening of exactly the kind stages C and D performed
(bool expressions, instance arguments, port payloads), not a target limitation to refuse.

**Why it belongs to stage G rather than stage H.** Because the repository already says so, twice.
`docs/STAGE_D_FINDINGS.md:507` calls stage G *"where local message-server priority becomes observable"*,
and `docs/trusted-boundary.md:40` forbids satisfying the correctness theorem by assuming schedules are
observationally equivalent — a claim that cannot even be tested while nothing is observable. Stage F's
priority order is currently gated as *text*; a witness makes it gated as *behaviour*, and it is the only
proposed artefact that would catch a translator that emits the right order and runs in the wrong one.

**Cost, stated honestly.** This touches both syntax modules, both well-formedness modules, the printer,
the translation core's statement walk, and every theorem that does a case analysis on statements. That
last item is the real cost, and it is also the reason `GeneralBody` was deliberately left a flat `List`
on both sides: so that a new constructor is a **build error** at every case analysis rather than a silent
default branch. The work is mechanical but wide. It lands as the **last** commit of the stage, so that
G1–G3 are green independently of it.


## 11. G6 — the tracked fragment declaration F63 owes

This obligation did not exist when stage G's scope was first derived; it was created by filing **F63**
(`docs/STAGE_G_FINDINGS.md`), which is why this document lists six obligations where an earlier note
listed five. Two documents are owed:

1. **A declaration of the general family's accepted fragment.** `docs/supported-fragment.md` declares
   vertical slice v0 and is now marked as historical; but `README.md:3` and
   `docs/trusted-boundary.md:28`/`:62` quantify the project's claim over "the supported fragment", so
   something must declare the current one. It should be derived from the executable predicates —
   `GeneralModel.wellFormed`'s four clauses plus the guards — not from prose, and it should state
   `arbitrary LF programs` as excluded *by design* rather than by schedule.
2. **The theorem-eligibility table.** The binding 2026-08-18 decision required that the
   "elaborable but not theorem-eligible" boundary "has to be legible" and that §7's table graduate into
   the tracked docs. It never did — the phrase occurs once repo-wide, in the sentence promising it. Five
   tie fixtures elaborate and are excluded from every correctness theorem, and no tracked document says
   which five. This table names them.

Both are written **last** (§13, commit 9), because their content depends on G5: a fragment that includes a
`trace` statement is a different fragment, and G5 is settled but not yet built.


## 12. What stage G does not do

* **No control flow.** `if` and `for` remain stage H. G5's `trace` constructor is a statement, not a
  branch, and it introduces no new expression forms.
* **No benchmark work of any kind.** The 2026-08-17 direction holds until the translator accepts the
  paper's DTR fragment. §9 disposes of `switch-pair` precisely so that no suite row, `POSITIVE_COUNT` or
  obligation count moves during stage G.
* **No infinite executions.** Weak bisimilarity is proved, and finite observable traces follow from it
  (§7). Runs of unbounded length would need a coinductive treatment, which the paper does not give
  either. This is the one place stage G stops short of aims 8 and 9 read at their widest.
* **No new tie rule and no tie fixtures becoming theorem-eligible.** Ties stay outside every theorem
  (§5). The paper supplies no tie rule and stage G does not invent one; G6 merely writes down which
  fixtures are excluded.

* **No change to `GeneralModel.wellFormed`'s priority stance.** The guards stay hypotheses. G3's proposed
  clause is on the **LF** side and concerns a dropped field, not source priority.

## 13. Work plan, in commit order

Each commit is independently green. Job counts assume one Lake job per new module, which has held for
every stage since B (`503 → 506 → 507 → 508 → 511`); the current total is **511** with **120** PASS lines
(24 frontend, 96 printer).

| # | Content | New modules | Predicted jobs |
|---|---|---|---|
| 1 | This design + the F63 doc batch (docs only, no build owed) | 0 | 511 |
| 2 | **G1** `Relico/DTR/GeneralActorSelection.lean` + `Relico/Tests/GeneralActorSelection.lean` | 2 | 513 |
| 3 | **G2a** `Relico/Semantics/GeneralLTS.lean` — both LTSs, the action type, the τ classification | 1 | 514 |
| 4 | **G2b** `Relico/Semantics/GeneralCorrespondence.lean` + `Relico/Correctness/GeneralTimeEquivalence.lean` — `R`, initial, Lemma 1 | 2 | 516 |
| 5 | **G2c** `Relico/Correctness/GeneralWeakBisimulation.lean` — Lemmas 2 and 3 at run level, then both transfer conditions | 1 | 517 |
| 6 | **G2d** `Relico/Correctness/WeakBisimulationTrace.lean` — the generic finite-trace corollary, aims 8 and 9 | 1 | 518 |
| 7 | **G3** the `lfc` priority-attribute probe, then the LF well-formedness clause and the three theorem restatements | 0 | 518 |
| 8 | **G5** `trace` on both sides, printer, statement walk, witness model, new gate marker | 0–1 | 518–519 |
| 9 | **G6** the fragment declaration and the theorem-eligibility table (docs only) | 0 | — |

Commit 5 is the largest single step in the stage and the one most likely to split; if it does, the split
runs along Lemma 2 / Lemma 3 / transfer conditions, which are three independently statable results.
Commits 3–6 are the G2 rewrite of 2026-08-23 and replace an earlier two-commit plan built around a source
step relation and a target step relation — those two modules are no longer part of stage G, because the
LTS subsumes them and keying a *step relation* on an explicit cohort argument is the defect §3 indicts.


**The precondition on commit 2 — asked, then settled the same day, and it resolved toward the harder
branch.** The question was whether `selectedActor` may be a priority minimum or must be a lexicographic
minimum on `(logicalTime, priority)`. **Measured: lexicographic.** `earliestDueArrival`
(`Relico/DTR/GeneralState.lean:142`) minimises arrival over the messages due at `now` rather than
requiring a unique arrival, and `readyActorsOf` (`:621`) records that arrival per actor, so a cohort with
mixed arrival times is reachable and priority must not be allowed to overtake an earlier message. §6
carries the full argument. The lexicographic form is therefore not a defensive choice but the only sound
one, and the two predicates the old layer left to its caller — `cohortSimultaneous` and `earliestReady` —
are exactly the half `selectedActor` now absorbs.

**A count that moves with commit 5, flagged because this class of defect has cost the project four
findings.** `LF.GeneralWellFormed` currently has **nine** clauses, and F49's whole content is that the
ninth is independent of the other eight and therefore cannot be dropped. G3's clause makes it **ten**.
Every prose count of those clauses moves together, and F49's own phrasing — which speaks of "the ninth
clause" positionally — must be re-read rather than renumbered, since its independence argument is about a
specific clause and not about an ordinal. Spelled-out English counts, not numerals, are the ones that go
stale unnoticed; grep for the words.

## 14. What would refute this plan

Stated as falsifiable predictions, so that a failure is informative rather than a surprise.

1. ~~**If `readyActorsOf` admits several arrival times**, §6's selection function is wrong as
   specified.~~ **Resolved before writing any code, 2026-08-23.** It does admit several, so the
   lexicographic form of §6 is the required one and a priority-first selection is refuted rather than
   merely disfavoured. Recorded here rather than deleted because the refuted alternative is the one a
   reader would expect a stage called "priority" to implement.
   The residual risk moves downstream: `selectedActor_unique` must now be guard-relative **and**
   arrival-relative, so the guard alone does not give uniqueness — two distinct-priority actors with
   *different* arrivals are ordered by arrival, and the guard does no work there. A proof that closes
   without using the arrival component would be evidence the statement is too weak.
2. **If `lfc` accepts a reaction priority attribute**, G3 inverts from justification to reversal (§8),
   and the "byte-identical" argument in `docs/STAGE_F_DESIGN.md` §7.4 becomes a statement about our
   printer rather than about the target.
3. ~~**If a `drain_reaction` firing turns out to be observable**, the τ classification of §7 collapses and
   with it the whole architecture. The check is concrete: a τ step must not change any state that `R`
   constrains — no state variable in `ex ≡ ηr`, no pending trigger in `bx ≡ qr`. `drain_reaction`
   *consumes* triggers, so this is the assumption most likely to be wrong, and it is wrong in a specific
   way if it is: draining would have to be modelled as part of the observable take rather than as a step
   preceding it. **This is the single prediction whose failure would cost the most**, and it is checkable
   before the transfer conditions are attempted, at the point `R` is defined.~~
   **Void, 2026-08-23, and the defect is F64.** There is no such firing to observe. `drain_reaction` is
   the message reaction generated from a DTR message server named `drain`, so it has a source counterpart
   by construction, and nothing in that model sends `drain`, so it never fires at all. More generally the
   translator emits no internal reaction anywhere (§7's measurement). The test that mattered survives,
   stated positively —
   **a τ step must not change any state that `R` constrains** — but the risk it was guarding has moved to
   **G2a's granularity choice**. If the LTSs are one step per dispatch, both τ sets are empty and §7's
   `τ* γ τ*` machinery is dead weight threaded through five modules; if they are statement-granular, τ is
   non-empty on both sides and the transfer conditions must genuinely use it. That is decidable at the
   moment `GeneralLTS.lean` is written, before any correspondence is attempted, and it is now the
   prediction whose failure would cost the most.
4. **If the target LTS cannot be keyed on triggers alone** — because two reactions in one reactor share a
   trigger — then reaction identity needs the site keys from the F56 repair as an explicit index. F56's
   repair emits one action *and* one reaction per send **site**, so this is expected to be fine; it is
   listed because it is an assumption §7's action type rests on.
5. **If `generalWeakBisimulation_backward` needs `MessageServerPrioritiesDistinct` as well as the actor
   guard**, then §5's claim that selection needs only the actor guard is wrong, and the membership-indexed
   bridge propagates further than predicted. The signal is a proof that cannot close without reaching into
   a class's server list.
6. **If G5's `trace` constructor forces a change to `GeneralBody`** rather than being absorbed by the
   existing flat `List`, the widening is larger than stages C and D were, and the honest response is to
   split G5 into its own stage rather than to quietly reduce it — the observability decision is settled,
   so the variable is scheduling, not scope.


## 15. Decisions, and how each was settled

All five are settled; this section is the record, not a request. Four were put to the decision-maker on
2026-08-23 and one was resolved by measurement.

1. **G5 — proof-only or observable? → Observable.** The `trace` widening is stage G's deliverable, landing
   as the stage's last commit so G1–G3 are green without it. §10.
2. **G3 — is the refusal reading right? → Yes, refuse.** A populated `LF.GeneralReaction.priority` becomes
   a well-formedness violation rather than a documented no-op, gated on the `lfc` probe first. §8.
3. **G4 — retire `switch-pair`? → Retired.** What stage G needs from it is a witness, not a scored suite
   row, and the witness is G5's. No `POSITIVE_COUNT` and no obligation count moves. §9.
4. **G2's scope — how much of the correctness claim does stage G owe? → The paper's Theorem 1.** Delegated
   to my judgment with the instruction to read the paper first and to keep any divergence minimal and
   precisely documented. The paper read changed the answer: what I had drafted as a step correspondence
   with an owed lift is not the paper's architecture. A second reason offered the same day — that the
   strong form is refuted by our own `drain_reaction` — was **wrong, and is withdrawn as F64**; the
   decision rests on the paper alone. Stage G therefore proves weak bisimilarity (Definition 1) with
   assignments and scheduler stuttering as τ — a classification the paper itself licenses — and derives
   finite-trace agreement from it, so aims 8 and 9 are discharged for the general family rather than
   owed. Three divergences are documented in §7; two were already forced by earlier findings and the
   third is scope. §7.
5. **Commit order — may G6's documents land last? → Yes, and it is now the ninth commit.** F63 is filed
   and `docs/supported-fragment.md` carries a scope marker pointing at it, so the interval is documented
   rather than silent. §11, §13.

The precondition on G1 — priority minimum or lexicographic minimum — was **not** a judgment call and was
not treated as one: it was measured against `earliestDueArrival` and `readyActorsOf`, and it refuted the
simpler form. §6 and §14 item 1.




