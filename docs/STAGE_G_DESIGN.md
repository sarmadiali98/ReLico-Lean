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
**paper**, §7 says so explicitly, enumerates the divergences, and gives the reason for each; every one is
held to the narrowest form that still works. This sentence carried the count as well until 2026-08-24, and
the count was `three` — stale from the moment P24's split `TIME PROGRESS` became the fourth. The number now
appears only next to the list that can be counted.


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
   (`Relico/DTR/GeneralState.lean`) returns the whole cohort, and its docstring says why: *"The
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
`readyActors_discriminates` (`Relico/DTR/GeneralState.lean`, proved by `decide`). The theorem is a
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
which is weak bisimilarity.

**What this section must not be read as licensing, corrected 2026-08-24 (F66 part 5).** It said, until that
date, that *"where the general family's τ sets turn out empty, stage G's result and this one coincide"*.
They do not coincide, because the τ sets are not empty: §7 settles G2a at **statement** granularity, where
τ is assignments and sends on both sides. The two results are over LTSs of different granularity and
neither subsumes the other — this one is lock-step over dispatches, stage G's is weak bisimilarity over
statements. **The part of this precedent stage G copies is the module split and the `_forward` /
`_backward` shape, not its granularity.** That distinction was implicit here and §7 read it as inherited
permission to work one-step-per-dispatch, which would have made the paper's `πx ≡ µr` vacuous. A precedent
cited for its *structure* has to say which of its properties travel.

The one deviation is §3's: no cohort parameter. Concretely, where the multi-store relation reads
`ActorPriorityDispatchStep request ready sourceModel actorName before after …`, the general source
transition reads `DTR.GeneralStep sourceModel config label configAfter` and obtains the cohort internally
as `config.erase.readyActors`. The cohort is a *derived* quantity, so nothing outside the
relation can supply a fabricated one. Two corrections in that sentence, both recorded as **F71**: the
relation is `DTR.GeneralStep`, not `GeneralDtrStep`, and `config` is a `GeneralRuntimeConfiguration`, so the
cohort is read through `erase` rather than off `config` directly.


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
whose arrival is `≤ now`**, and `readyActorsOf` puts that arrival into each record as its
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
being the theorem this project claims to implement, and *not* because our output refutes lock-step. ~~If the
granularity G2a picks leaves both τ sets empty, weak bisimilarity specialises to lock-step: a
*strengthening* of the stated result rather than a contradiction of it.~~ **That escape hatch is closed as of
2026-08-24**: granularity is settled at statement level below, both τ sets are non-empty, and weak
bisimilarity does not specialise to lock-step here. The adoption still rests on the paper's authority, which
is what it should have rested on alone.

**What the paper proves.** `Definition 1` is weak bisimilarity w.r.t. a bijection `ϕ` on actions, with
the two standard transfer conditions and `⇒` expanded as `τ* γ τ*` for `γ ≠ τ`. `Theorem 1` states
*"TS_dtr is weakly bisimilar to TS_lf w.r.t. bijection ϕ"*, and its proof constructs a relation `R` and
discharges Definition 1's transfer conditions using Lemmas 1–3. There is **no separate induction over
executions** in the paper: whole-run agreement is what weak bisimilarity *means*, and the only induction
is inside Lemma 1 (Time Equivalence), which is proved *"by induction on the number of DTR transitions"*
carrying a bag↔queue bijection as its hypothesis.

**The word "bijection" in the sentence above is the paper's, and it is refuted by the paper's own Figure 2 —
recorded 2026-08-25 as F79 and issued as P25.** Fig. 2a's `reactiveclass Controller(5)` declares one message
server, `msgsrv receiveReading(int w)`, and both sensors send to it; Fig. 2b's `reactor Controller` answers
with two input ports and two reactions. So `ϕ(ms) = rct` is not a function under the only reading of
`Act_dtr = {ms, t} ∪ τ` that makes Lemma 2 statable — the reading indexed by message server, which `map_M`
and `prty_l` both require. Read the alphabet *literally* instead, as an unindexed two-element set, and `ϕ` is
a bijection but the theorem cannot say which message was consumed, so Lemma 2 and F76's selection divergence
become invisible to it. The paper cannot have both readings, and that dilemma is P25's substance rather than
a wording complaint.

**What stage G does about it.** The label correspondence is a **relation** `Φ ⊆ Act_dtr × Act_lf`, asymmetric
in force and not in shape: forward, a source `ms_m` step is matched by a target step on *some* `rct` with
`Φ(ms_m, rct)`; backward, nothing weakens, because target→source remains a total function — every emitted
reaction comes from exactly one send site or route of exactly one message server. Equivalently `ϕ` is a
bijection between source actions and *equivalence classes* of target actions, and the quotient collapses
nothing the source alphabet can express, because the send site is invisible in `Act_dtr`. This is what all
eleven of the repository's existing label correspondences already do, so it is a transcription correction
here rather than a design change. It also decides **F78 part 3**, which had parked a four-way choice as the
user's: three of the four options are refuted by Fig. 2 and the first is forced. **#129 is therefore blocked
on F76 alone.** The `ϕ` transcription in the τ-table paragraph below inherits this correction; its `τ ↦ τ`
and `t ↦ t` halves are unaffected, and the sentence there that *is* wrong for a different reason is
corrected in place.

**The relation, transcribed.** The paper's `R` relates a DTR global state mapping each actor `x` to
`(ex, bx, πx)` with an LF global state mapping each reactor `r = map_A(x)` to `(ηr, qr, µr)`, requiring
`ex ≡ ηr` (translated state variables hold identical values), `bx ≡ qr` (the Lemma 1 bijection between
pending DTR messages and LF triggers, corresponding pairs sharing an arrival time), and `πx ≡ µr`
(corresponding continuations). It holds initially because both executions start empty. Stage G defines
`GeneralStateCorrespondence` with these three components, per actor, keyed through the existing
translation's reactor naming rather than an abstract `map_A`.

**Four components, not three, and the reason is the target state type — F75 part 3.** This paragraph said
"exactly these three components" until 2026-08-24. The paper's LF state gives each reactor its own `qr`;
`LF.GeneralRuntimeState`, built by G2a-ii, carries **one** `pending` queue for the whole program whose events
each name a `target`, and `LF.GeneralReactorRuntime` has no queue field. The same information, distributed
differently — so `bx ≡ qr` becomes a per-actor agreement *extracted* from the global queue by target name
(`GeneralPendingAgrees`), and `R` needs a fourth field, `pendingTargeted`, saying every pending event's target
is an actor of the source. Per-reactor queues would make that free; one global queue does not. It is
load-bearing: the bridge both directions of Lemma 1 run through starts from an arbitrary queue member and must
produce a source actor before any arrival theorem applies. This is a representation difference, **not** a
fifth divergence from the paper.

**Both stores are related through membership, not lookup.** `Store` is an ordered association list whose
header says only the first binding for a key is observable, while the source's arrival minimum ranges over
*every* binding. So all four fields quantify over `∈` and none of them calls `Store.lookup`; a lookup-shaped
`R` would silently agree with a shadowed binding the semantics can still see. This is **F74**'s root cause
restated at the relation, and it is the reason G2b's support lemmas are membership lemmas
(`DTR.mem_eraseContinuations` and its converse) rather than lookup lemmas.

**What is τ — corrected 2026-08-24 by reading the two SOS tables, and recorded as F66 part 4.** This
paragraph previously said τ was *"assignments on both sides, and on the LF side the scheduler's own
steps"*. **Table II has no scheduler rule.** Its rules are `ASSIGN`, `INTERNAL SEND`, `EXTERNAL SEND`,
`TAKE`, `CONDITIONAL-T`, `CONDITIONAL-F` and `TIME PROGRESS`; Table I's are `ASSIGN`, `SEND`, the two
conditionals, `TAKE` and `TIME PROGRESS`. Read off the tables, the τ set is:

| | τ | observable |
|---|---|---|
| DTR | `ASSIGN`, `SEND`, `CONDITIONAL-T/F` | `TAKE` → `ms`, `TIME PROGRESS` → `t` |
| LF | `ASSIGN`, `INTERNAL SEND`, `EXTERNAL SEND`, `CONDITIONAL-T/F` | `TAKE` → `rct`, `TIME PROGRESS` → `t` |

`ϕ` maps `ms ↦ rct`, `t ↦ t`, `τ ↦ τ`. So the τ steps stand in **bijection** across the two tables:
`ASSIGN` matches `ASSIGN`, DTR's single `SEND` matches whichever of LF's two send forms the translation
chose for that site, and the conditionals match pairwise. Nothing on either side is unmatched, and `τ*`
in Definition 1 has no surplus behaviour to absorb.

**That last sentence is about Tables I and II as printed, and it is false of stage G's own semantics.**
Adopting P24's split three paragraphs below makes an LF microstep-only advance τ, and it has no DTR
counterpart — so our τ sets are *not* in bijection and `τ*` has exactly one surplus step to absorb, which is
the point of the split rather than an oversight in it. Measured after G2a-iii landed: two of
`DTR.GeneralStep`'s four constructors carry `DTR.GeneralLabel.tau` and **four** of `LF.GeneralStep`'s six
carry `LF.GeneralLabel.tau`. **F75** part 1 carries the measurement and the consequence for G2b — of those six
τ-emitting constructors, only `microstepAdvance` supports a single-step `R`-preservation theorem, because the
other five each change something `R` constrains and are *restored by their partner step* rather than preserved
alone.

The earlier wording was taken from Theorem 1's *proof*, which discharges surplus LF behaviour with
*"Since scheduler steps are internal to LF and have no corresponding observable transition in DTR, they
are subsumed by the weak transition relation ⇒."* That sentence is reaching for a real gap and naming it
wrongly. The step with no DTR counterpart is **microstep-only `TIME PROGRESS`**, which Table II labels
`t`, observably — and for a zero-delay send, which is the default and which the paper's own tool note
describes as translated to `after 0ms`, that surplus `t` breaks *both* of Definition 1's transfer
conditions. That is a defect in the paper, filed as **P24**, and it is not repaired by Lemma 1, which
tracks logical-time *equality* and is correct.

**Stage G adopts P24's repair**: `TIME PROGRESS` is split so that an advance of the microstep alone is
**τ** and an advance of logical time is **`t`**. This makes the proof's own sentence true, keeps `ϕ`'s
`t ↦ t` a bijection on observable time actions, and is semantically right — microsteps exist only to
order events within one logical time, so reporting one as an observable action reports a time the system
has already reached. It is the stage's fourth documented divergence, listed below, and G2a-iii pins the
zero-delay case as a regression so the split cannot silently regress to the paper's form.

**Granularity: statement-level, with continuations. Settled 2026-08-24, and the settlement is forced.**
This was the one question §4 left inherited rather than decided, and the inherited answer was wrong. §4
mirrors the `GlobalMultiStorePayload*` development, which is strict lock-step — one target event per
source event, no internal steps, no τ — i.e. **dispatch** granularity. But this section commits `R` to the
paper's three components including `πx ≡ µr`, and the paper defines `πx` as *"remaining statements of"* the
executing message server and `µr` as *"remaining statements of the currently"* executing reaction, with
**both** `TAKE` rules premised on the continuation being `ε`. The two commitments are incompatible: at
dispatch granularity the third component is permanently empty on both sides, `πx ≡ µr` is trivially true,
and the stage would ship a relation reproducing the paper's `R` in shape while one of its three conjuncts
did no work. So statement granularity is **required**.

It is also **available and symmetric**, which is the part that had to be measured rather than assumed:
`LF.GeneralStmt` has three constructors (`assign`, `schedule`, `setPort`), `DTR.GeneralStmt` has two
(`assign`, `send`), `GeneralBody` is a statement list on both sides, and both families carry `GeneralType`
and `GeneralValue` with identical `int : Int | bool : Bool` constructors — so a step relation can walk
either body and the value correspondence is a rename. Had LF reaction bodies been opaque, fine granularity
would have been impossible and §4's inherited choice would have been forced rather than mistaken. Note
what coarsening would *not* have saved: the evaluators are needed either way, because a big-step dispatch
rule still has to say what a body did to the valuation, or `ex ≡ ηr` compares two things that never
change.

**A fragment restriction this granularity exposes, and G6 must declare.** Tables I and II both carry
`CONDITIONAL-T` and `CONDITIONAL-F`. Neither `GeneralStmt` has a conditional, and `GeneralBody` is a flat
list whose docstring already states that the stage admitting branching must change the type. So G2a's step
relations have no conditional rules and what stage G proves is the **conditional-free sub-fragment**. That
is a restriction on the input, not a divergence from the semantics, and it belongs in **G6**'s declaration
where a reader will find it — a theorem quantified over a body type that cannot branch says nothing about
one that can.

**A precondition the evaluators must cite rather than inherit.** The paper's `TAKE` sets the valuation to
`ex ∪ v⃗`, merging message parameters into the actor's variable valuation, so one
`Store VarName GeneralValue` serves both state variables and parameters and `DTR.GeneralExpr`'s separate
`stateVar` and `parameterVar` constructors both resolve in it. That is sound **only because** stage E's
`.parameterShadowsStateVariable` well-formedness clause already makes the collision ill-formed. Without
it, one store would let a parameter silently overwrite a state variable of the same name, and no type
error would catch it.

**Deliverables.** Fourteen modules, not the five this section first named — see **F66 part 2** for the
undercount, **F67 part 5** for the one module that decomposition itself missed, and **F66 part 3** for why
none of them sit in a `Relico/Semantics/` directory, which does not exist and which no family has ever used.
Source semantics live beside source syntax, target beside target, cross-language results in `Correctness/`.

```
-- G2a-i
-- Relico/DTR/GeneralEvaluation.lean         (new)  expression evaluation, source
-- Relico/LF/GeneralEvaluation.lean          (new)  expression evaluation, target
-- Relico/Correctness/GeneralEvaluation.lean (new)  compileGeneralExpr preserves evaluation
-- Relico/Tests/GeneralEvaluation.lean       (new)  compile-time pins, incl. the truncation pins
-- G2a-ii
-- Relico/DTR/GeneralRuntime.lean            (new)  runtime state with continuation; GeneralLabel
-- Relico/LF/GeneralRuntime.lean             (new)  runtime state over the REUSED tag; GeneralLabel
-- Relico/Tests/GeneralRuntime.lean          (new)  compile-time pins, incl. the attached continuation
-- G2a-iii
-- Relico/DTR/GeneralSemantics.lean          (new)  Table I's rules, tau classification
-- Relico/LF/GeneralSemantics.lean           (new)  Table II's rules, with P24's split TIME PROGRESS
-- Relico/Tests/GeneralSemantics.lean        (new)  the zero-delay regression pin
-- G2b
-- Relico/Correctness/GeneralCorrespondence.lean    (new)  R, and that it holds initially
-- Relico/Correctness/GeneralTimeEquivalence.lean   (new)  Lemma 1: the induction and its invariant
-- G2c
-- Relico/Correctness/GeneralWeakBisimulation.lean  (new)  Theorem 1: both transfer conditions
-- G2d
-- Relico/Correctness/WeakBisimulationTrace.lean    (new)  generic: bisimilarity to trace agreement
```

The two transition relations are `DTR.GeneralStep sourceModel config label configAfter` and
`LF.GeneralStep program state label stateAfter`. **Neither takes a cohort parameter** — §4's one deliberate
deviation from the multi-store precedent, for §3's reason.

They are **not** spelled `GeneralDtrStep` and `GeneralLfStep`, which this section specified first and which
the label-naming paragraph below argues against without having applied its own reasoning here. The corpus
settles it: twenty-two step inductives are declared on both sides and not one carries a `Dtr` or `Lf` infix —
`DTR.DetailedMultiStorePayloadStep` beside `LF.DetailedMultiStorePayloadStep`, and a bare `Step` on each side
in `DTR/Semantics.lean` and `LF/Semantics.lean`. One name in two namespaces, as with the labels. **F71.**

**The label types are two, and neither is named `GeneralAction`.** This section first specified a single
`action : GeneralAction` carrying a `tau` constructor. That name is already taken:
`Relico/LF/GeneralSyntax.lean` declares `structure GeneralAction`, the LF **logical action declaration**,
between `GeneralStateVariableDecl` and `GeneralTrigger`. Reusing it would collide, and would put "LF
logical action" and "LTS label" behind one identifier in a development whose entire subject is the
correspondence between labels. Two types are declared separately, which `ϕ : Act_1 → Act_2` argues for
independently — a bijection between two action sets needs two types — and which preserves the
`map_A` / `map_M` naming content stages E and F built. F66 part 7.

They are spelled `DTR.GeneralLabel` and `LF.GeneralLabel`, not the `GeneralDtrAction` and
`GeneralLfAction` this section specified first. Three measurements forced the change and none of them
touches the reasoning above: the repository declares **thirty-nine** `…Label` inductives for transition
labels — thirty-seven predating G2a-ii, which contributes the other two — and **zero** `…Action`
inductives, so `Label` is the house word; `GeneralLfAction` would not
actually have removed the collision, since it would live in `namespace LF` one word away from
`LF.GeneralAction`, whereas `LF.GeneralLabel` does remove it; and the `Dtr`/`Lf` infix is redundant inside
`namespace DTR` and `namespace LF` and breaks the symmetry G2a-i established, where `DTR.GeneralValuation`
and `LF.GeneralValuation` are one name in two namespaces. The paper's `Act` sets are unchanged and nothing
in Theorem 1 reads an identifier, so this is a naming decision rather than a divergence; it is recorded in
full in `Relico/DTR/GeneralRuntime.lean`'s module docstring, at the point of the decision.

**The superdense tag and `upd` are reused, not built.** This section listed them as G2a-ii's work. They
already exist, proved, from vertical slice v0 — `LF.Tag`, `LF.Tag.schedule` (which *is* the paper's `upd`),
the lexicographic `LF.Tag.PrecedesOrEqual`, and its monotonicity lemma `Tag.precedesOrEqual_schedule`. What
G2a-ii genuinely adds to the tag is narrower and scheduler-shaped: decidability, transitivity and
totality of that order, absent until now because every earlier consumer proves one specific inequality
rather than computing a minimum. **F69** carries the correction and the method error that produced it.

**`Relico/Common/WeakTransition.lean` is instantiated, not rebuilt.** `TauSteps`, `WeakStep` and
`observableProjection` are already generic and already proved, over an arbitrary `isTau : Label → Prop`.
That signature reaches back into this obligation: G2a-ii's two `isTau` functions must be `Prop`-valued
rather than `Bool`-valued, and each label type owes a `project` this section never mentioned. G2c and G2d
instantiate the foundation. **F70**.

**Theorems, in dependency order.**

1. `generalCorrespondence_initial` — `R` relates the initial states. This said "Unconditional; the paper's
   'holds initially' line, and cheap" until 2026-08-24, and **there are no initial states to be
   unconditional about**: the general family has no initializer on either side, and §13's twelve rows create
   none. What G2b lands is the **scoped** form — arbitrary source configuration, arbitrary target reactor
   store, with the emptiness and valuation-agreement facts an initializer would establish by construction
   taken as hypotheses. Cheap it is; unconditional it is not, and the unconditional statement is **owed at
   G5**, which needs the two initializers anyway for its runnable witness. **F75** part 2.
   Row 11 landed both halves (2026-08-27): `DTR.GeneralModel.initialState` and
   `LF.GeneralProgram.initialState` under `Relico/{DTR,LF}/GeneralInitialization.lean`, and the
   unconditional `generalCorrespondence_initial` in `Relico/Correctness/GeneralCorrespondence.lean`,
   quantifying over a successful compilation and nothing else. The scoped form survives as
   `generalCorrespondence_initial_scoped` for callers relating two states they did not build, and F75's
   "by instantiation rather than re-proof" prediction was wrong in both halves — **F85**.
2. `generalTimeEquivalence` — Lemma 1. Every DTR event at logical time `t` corresponds to an LF event at
   tag `(t, m)`, by induction on transitions, carrying the bag↔queue bijection. This is where the
   chaining invariant lives, and it is the one genuinely inductive obligation.
3. `generalPriorityPreservation` — Lemma 2 at *run* level, resting on stage F's compile-time ordering
   theorems rather than restating them. **Same-actor case only as the paper states it**; see the
   divergence note below.

   **This item is REFUTED as written — see F80**, measured 2026-08-25 before any Lemma 2 Lean existed, and
   it is refuted twice over. Its *conclusion* is not derivable: `LF.selectEarliestEvent` compares tags only
   and keeps the incumbent, so two same-tag events targeting **one** reactor fire in queue insertion order,
   and `reactionFor?` — keyed on the trigger name — is reached only afterwards, to say which reaction
   handles an event already chosen. Because a translated reactor's reactions all carry distinct kinds,
   `reactionFor?` and hence every `LF.GeneralStep` derivation is invariant under permutation of
   `messageReactions`; the phrase *"resting on stage F's compile-time ordering theorems"* therefore rests on
   theorems that decide nothing at run level. Its *premise* is not represented either: `ReadyActor` carries
   an actor and a time, `take` picks its message by an arbitrary bag split, and message-server priority is
   absent from the source's run-level modules — so there is no source ordering for the lemma to preserve.
   What row 8 can honestly land in its place is the refutation as a theorem, in the shape F50 / `#60` used
   for §10.2's refuted `setPort` obligation: permutation-invariance of `reactionFor?` under distinct
   triggers, plus the fact that the translator always makes them distinct. **Lemma 3 (item 4) is untouched**
   — it is priority-free.
4. `generalCausalityPreservation` — Lemma 3, over `after d` delays, reusing stage E's delay machinery.

   **Expanded 2026-08-25, before authoring, because this line was the whole specification.** Lemma 3 is
   never stated anywhere in `docs/`, and the phrase *"Causality Preservation"* — its actual name — appeared
   in no document here until now, so the obligation was carried through the stage as a name without content.
   Verbatim: *"Let `ms_i` in actor `x` send a message to `ms_j` in actor `y` with delay `d ≥ 0`. Then the
   corresponding LF reactions `r_i` in `map_A(x)` and `r_j` in `map_A(y)` satisfy `TT_i < TT_j`."* Three
   things follow that this line did not say.

   First, **the conclusion is strict and no strict tag order exists.** `Relico/LF/Scheduling.lean` defines
   `LF.Tag.PrecedesOrEqual` and five lemmas about it; there is no `Tag`-level strict precedence anywhere in
   the repository. So the statement needs either a new strict definition or the `PrecedesOrEqual ∧ ≠`
   phrasing, and either way it is new API — the same omission class as the quiescence lemma of item 5's
   backward direction, which §7 also did not list. Note `namespace Tag` is reopened in **five** files, so the
   *qualified* name must be grepped across all of them before anything is added.

   Second, **the non-strict half is already landed and is family-independent.**
   `LF.Tag.precedesOrEqual_schedule` proves `PrecedesOrEqual currentTag (Tag.schedule currentTag delay)` for
   every delay, by cases on `delay.value = 0`. It lives in `Relico/LF/PendingNotPast.lean` — a file with no
   general-family content at all — but it is a `Tag` lemma, so the general family may use it directly. Only
   the strict upgrade is genuinely new. *"Reusing stage E's delay machinery"* pointed at the wrong place:
   what is reusable here is a tag lemma sitting in a multi-store file.

   Third, **the paper's proof of this lemma is defective in two ways, and neither breaks the lemma** — see
   **P26**. Its `d > 0` case states `TT_j = (t + d, m)` where the paper's own `upd` yields `(t + d, 0)`; the
   conclusion survives because `t < t + d` settles the lexicographic order first. And both its cases
   attribute the tag to an *"LF connection with `after d`"*, while its statement never requires `x ≠ y`, so
   the self-send route — which §III maps to `schedule()` on a logical action — has no case. Our side is
   uniform over both routes because one `Tag.schedule` serves `LF.GeneralStep.schedule` and
   `LF.GeneralStep.setPort` alike, so the theorem we state is the one the paper's proof was reaching for.
   **Lemma 3 is priority-free and is therefore untouched by F76 and F80** — it is the row's authorable core.
5. `generalWeakBisimulation_forward` / `_backward` — Definition 1's two transfer conditions, each
   producing a *weak* transition `τ* γ τ*` on the other side. **This item is REFUTED as written — see
   F76**, measured 2026-08-25 before any row 8 Lean existed. The two run-level selectors disagree:
   `selectedActor` keys on `(arrival, priority)` and `earliestPendingEvent?` keys on `(time, microstep)`
   and is priority-blind, so it breaks a same-tag tie by queue append order. Two positive-delay sends
   landing at one logical time carry identical tags, and the forward condition then fails on a
   two-send body. The guard this item named — `ActorPrioritiesDistinct` — does not repair it and is
   aimed at the wrong side: it constrains the *source*, making the source's choice unique, which is
   exactly the condition under which the source departs from queue order. F76 records five candidate
   repairs and deliberately picks none, because choosing a remedy before the artefact was measured is
   the error being corrected. **The rest of row 8 does not depend on this item**: the derived
   quiescence lemma, Lemma 2's same-actor case and Lemma 3 are sound under every candidate repair.
   **That last clause is itself REFUTED for Lemma 2 — see F80.** The quiescence lemma and Lemma 3 are
   sound under every candidate repair; Lemma 2's same-actor case is not sound under any of them, because
   its defect is not the selector disagreement this item records but the inertness of the mechanism it
   rests on, plus a premise the source never establishes. F80 also narrows F76's candidate (e): within-tag
   permutation as stated would quotient away the one same-tag ordering real `lfc` does enforce — reaction
   declaration order **within one reactor**, measured in `#80` — so it refines to a partial quotient, free
   across distinct reactors and order-preserving within one.
   Separately, and settled rather than open, the *label* shape this item assumes is corrected by **F79**:
   each condition produces a weak transition on **some** target action related to the source's by `Φ`, not
   on `ϕ` of it, because one message server becomes several reactions (§7). Two halves of this item were
   wrong for unrelated reasons; that one is now answered, and F76 is the one still open.
6. `weakBisimulation_traceAgreement` — **generic, model-independent**: from a weak bisimulation, the two
   systems agree on finite observable traces. Landed as the pair
   `weakBisimulation_traceAgreement_forward` / `_backward`, per this section's own rule that aims 8 and 9
   are two implications rather than one `Iff`. It discharges `trusted-boundary.md` aims 8 and 9
   **generically**, so that no family proves them again, and it is proved once over an abstract LTS, so it
   costs nothing per family. It does **not** discharge them for the general family outright, and an earlier
   wording of this line said it did: the theorems consume transfer conditions holding at *every* weak step,
   and the general family proves its `.timeAdvance` case only — the `.consume` case is `#129`, blocked on
   F76. So the general-family instantiation waits; see **F83**. It is also **not** what first gives this
   repository a finite-execution result: the multi-store family already has two, in a strict lock-step
   shape with no label list and no projection — see §4, and **F65** for the correction this sentence
   replaces.

**Scope limit, stated rather than discovered.** Aims 8 and 9 are discharged for **finite** executions.
Infinite runs would need a coinductive treatment, which the paper does not give either, and which no
part of this repository currently needs. That limit is a scope statement, not an owed theorem.

**Divergences from the paper, kept to the minimum and documented precisely.** Four, and all four are
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

  **Corrected 2026-08-25 by F80.** *"where declaration order is decisive"* is true of real `lfc` — that is
  `#80`'s measurement, in three trigger shapes — and **false of `Relico/LF/GeneralSemantics.lean`**, which
  orders two same-tag events of one reactor by queue insertion and consults declaration order only to pick
  which reaction handles an already-chosen event. Stage F's realization is therefore sound as a *compile-time*
  result and inert at run level, so the final clause — *"the conclusion of Lemma 2 is preserved in both
  cases"* — does not hold for either case in the modelled semantics. The divergence from the paper stands as
  described; what does not stand is the claim that stage G recovers Lemma 2's conclusion through it. This is
  a defect in **our LF model's fidelity**, not in the paper: the paper's within-one-reactor argument is the
  half that real `lfc` confirms.
* **Actor priority participates in selection, which the paper's SOS take rule does not do.** Priority
  appears in the paper's correctness development (`prty_l`, `prty_g`, Lemma 2) and not in either SOS
  table — the verdict recorded when `#79` closed. §6's `selectedActor` uses it, on the authority of the
  2026-08-16 scope decision that actor priorities are in scope and that the repo is definitive where the
  two conflict. The divergence is held to the minimum available: priority discriminates **only** among
  equal-arrival candidates, so the paper's arrival-first rule is untouched and the extension is confined
  to a case the SOS leaves unordered.
* **Table II's `TIME PROGRESS` is split, because as printed Theorem 1 is false of a zero-delay send.**
  `upd((t,m),d)` advances the microstep when `d = 0` and logical time when `d > 0`. For a zero-delay send
  — the default, and what the paper's own tool note says is translated to `after 0ms` — the DTR message is
  due immediately and `TAKE` fires, giving the trace `ms`; on the LF side the trigger sits at `(t,m+1)`,
  `enabled_tr` fails, the body is `ε` so no τ is available, and Table II's `TIME PROGRESS` fires labelled
  **`t`**, giving `t · rct`. Forward transfer needs `τ* rct τ*` with `t ∉ τ*`, and backward needs a DTR
  `τ* t τ*` that cannot exist. Stage G therefore labels a microstep-only advance **τ** and a logical-time
  advance **`t`**. This is the smallest available repair: it changes one rule's label, leaves Lemma 1
  untouched, and makes Theorem 1's own proof sentence about "internal" surplus steps true for the first
  time. The alternative repairs are worse and are named in **P24** — restricting the fragment to strictly
  positive delays would reject the commonest DTR idiom, and adding a τ self-loop to absorb the step would
  make `⇒` reflexive-by-fiat and weaken the theorem. **P24** carries the full argument, including the
  dependency on **P16** it declares rather than hides; G2a-iii carries the regression pin.
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


**Precondition — DISCHARGED 2026-08-25, and it was a probe not an argument.** The justification above
asserts something about `lfc` that this repository had not measured when this section was written: that
there is no accepted reaction-priority attribute in Lingua Franca 0.11.0. The probe was to emit a reaction
carrying a candidate priority attribute and record whether `lfc` accepts, rejects, or silently ignores it,
with the consequence that **if `lfc` accepted one, G3 would flip from "justify" to "reverse"** and the
field would be wired to the printer instead. Writing the justification before the probe would have been an
inferred claim dressed as a read, which is the failure mode F51 records.

It ran under task `#102` and it **rejected**: row 16f of F77's probe table in
`docs/STAGE_G_FINDINGS.md` records `@priority(2)` / `@priority(1)` producing *"Unknown attribute:
priority, 2 errors"*, and F77's summary adds that no attribute could serve. G3 therefore stays "justify",
and the flip described above is settled negatively rather than pending.

That the discharge sat in a different file under a different task, with nothing here pointing to it, is
itself recorded — see **F84**. A precondition should name the task that can discharge it.

**Landed.** Row 10 added `LF.GeneralProgram.reactionPrioritiesAbsent` as the tenth conjunct, with a tenth
mirrored refusal sentence in `Relico/Translation/GeneralBasic.lean`. One sentence of the decision above
did not survive contact: *"The three inert theorems then become consequences of the clause"* has the
implication backwards, and the direction that is actually load-bearing — the three per-reaction equations
composing up to the clause, for our own output — is owed as task `#147`. F84 has the argument.

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

**Landed in three parts, the last on 2026-08-27.** Part one, the plumbing (`trace` on both sides,
printer, statement walk), and part two, Option A's τ semantics, landed first; part three is the witness
itself: `priorityWitnessModel` in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean` (selector
`emit-priority-witness`), compiled with real `lfc`, run natively, and asserted on by
`frontend/check-general-lf-target.sh` under the new marker `GENERAL_LF_PRIORITY_WITNESS_OK` — the
observed stdout is `LATE` then `EARLY`, against a declaration order that says `early` first at both
levels. The model carries one derangement per sort: the hub's servers are declared `early, late` and
prioritised `late, early` (level 2, run-time observable through reaction declaration order), and the
senders are declared `early, late` with priorities `2, 1` (level 1, observable in the emitted
connection order only, because LF's cross-reactor order comes from the dependency graph — P1). The four
pre-existing target-gate cycles keep their exit-code-only contract untouched. This discharges audit
item C3 (`RELICO_FORWARD_ROADMAP_AUDIT.md` §C) and completes §13 row 11.

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
every stage since B (`503 → 506 → 507 → 508 → 511`). The baseline is now **513** jobs with **120** PASS
lines (24 frontend, 96 printer), measured after G1 landed at `cc7b0c7` — commit 2 added two modules and
two Lake jobs and moved no PASS line, because a tests-only module contributes compile-time pins rather
than gate output.

**This table was resliced on 2026-08-24.** Row 3 previously read *"**G2a**
`Relico/Semantics/GeneralLTS.lean` — both LTSs, the action type, the τ classification | 1 | 514"*. One
module and one job where the honest decomposition is **ten modules and ten jobs**: the general family has no
evaluator, no runtime state and no step relation to build an LTS over, so G2a is three commits rather than
one, and the stage is **twelve** commits rather than nine — eleven from the reslice plus the docs commit the
reslice itself owes, row 3 below.
**F66 parts 1 and 2** carry the measurement, corrected from nine modules to ten by **F67 part 5**;
**F66 part 3** is why none of the modules sits under `Relico/Semantics/`.

| # | Content | New modules | Predicted jobs |
|---|---|---|---|
| 1 | This design + the F63 doc batch (docs only, no build owed) | 0 | 511 ✅ |
| 2 | **G1** `Relico/DTR/GeneralActorSelection.lean` + `Relico/Tests/GeneralActorSelection.lean` | 2 | 513 ✅ |
| 3 | P24, F66, this revision, one stale count in `STAGE_C_DESIGN.md` (docs only, no build owed) | 0 | 513 |
| 4 | **G2a-i** `DTR/GeneralEvaluation` + `LF/GeneralEvaluation` + `Correctness/GeneralEvaluation` + `Tests/GeneralEvaluation` — expression evaluation on both sides, and that `compileGeneralExpr` preserves it | 4 | 517 |
| 5 | **G2a-ii** `DTR/GeneralRuntime` + `LF/GeneralRuntime` + `Tests/GeneralRuntime` — runtime state with continuations, the two `GeneralLabel` types with their τ classification and observable projection, and the three tag-order facts a scheduler needs. The superdense tag and `upd` are **reused, not built** — see **F69**; `isTau` is `Prop`-valued and each label owes a `project` because `Common.WeakTransition` demands it — see **F70** | 3 | 520 |
| 6 | **G2a-iii** `DTR/GeneralSemantics` + `LF/GeneralSemantics` + `Tests/GeneralSemantics` — both step relations, the τ classification, P24's split `TIME PROGRESS`, the zero-delay regression pin | 3 | 523 |
| 7 | **G2b** `Correctness/GeneralCorrespondence` + `Correctness/GeneralTimeEquivalence` — `R`, its initial case, Lemma 1 | 2 | 525 |
| 8 | **G2c** `Correctness/GeneralWeakBisimulation` — Lemmas 2 and 3 at run level, plus the derived quiescence lemma the backward condition needs, **instantiating** `Common.TauSteps` and `Common.WeakStep` rather than restating either — see **F70**. The **two transfer conditions are held back**, because §7 item 5 is refuted by **F76**; the rest of the row is sound under every candidate repair and lands without them | 1 | 526 |
| 9 | **G2d** `Correctness/WeakBisimulationTrace` — the generic finite-trace corollary, aims 8 and 9, over `Common.observableProjection`, which is already proved with its three `@[simp]` lemmas — see **F70** | 1 | 527 |
| 10 | **G3** the LF well-formedness clause `reactionPrioritiesAbsent`, its mirrored refusal sentence, and the three theorem re-attributions — the `lfc` priority-attribute probe this row listed as its own first step had already run under row 0 as F77's probe 16f, so it was **not** re-run | 0 | 527 |
| 11 | **G5** `trace` on both sides, printer, statement walk, witness model, new gate marker | 0–1 | 527–528 |
| 12 | **G6** the fragment declaration and the theorem-eligibility table (docs only) | 0 | — |

**One obligation row 11 acquired after row 7 was authored.** The general family has no initializer on either
side, so `generalCorrespondence_initial` lands scoped rather than unconditional (§7, **F75** part 2). G5 needs
the two initializers regardless — a runnable witness has to start somewhere — so the unconditional statement
is attached to row 11, following by instantiation rather than re-proof. Row 11's module and job figures are
left as they stand, because whether the initializers arrive as two new modules or as additions to the existing
`DTR/GeneralRuntime` and `LF/GeneralRuntime` pair is not yet decided, and a made-up number would be worse than
a recorded dependency.

**Resolved 2026-08-27, after the two G5 trace commits landed.** The initializers arrived as **three new
modules** — `Relico/DTR/GeneralInitialization.lean`, `Relico/LF/GeneralInitialization.lean` and
`Relico/Tests/GeneralInitialization.lean` — and the unconditional statement did **not** follow by
instantiation: constructor entry installs bodies on both sides (no step rule on either side can start a
constructor), so the scoped theorem's idle-pairing hypotheses are false at the initial states and a third
actor correspondence, `generalActorCorresponds_constructorEntry`, carries the case. The unconditional
`generalCorrespondence_initial` quantifies over a successful compilation and nothing else — the guard's
uniqueness clauses already force the model's name-distinctness for anything that compiles — and the scoped
form survives as `generalCorrespondence_initial_scoped`. **F85** records the prediction's failure and the
semantics decision it hid: constructor arguments are bound into the initial valuation, because
`GeneralActorState` has no second store for them.

**One constraint row 9 acquired after row 8 part 1 was authored.** The finite-trace corollary compares
observable projections, and the target's observable `rct` labels carry a send site the source's `ms` labels
cannot name — F79, §7 above. So the trace statement is agreement **up to `Φ`**, not equality of projected
label lists, and the corollary quantifies existentially over the target label at each observable position.
Row 9's module and job figures are unchanged: the relation is the one row 8's transfer conditions already
state, so row 9 instantiates it rather than introducing a second notion.

The stage's endpoint is therefore an estimate near **527**, and the binding prediction is the one on each
commit's own row — which is where this project's prediction discipline can actually check it, a commit at a
time, rather than at a stage boundary eight commits away. Row 4 gained a module and every row below it
gained a job after G2a-i was written; **F67 part 5** carries that correction and the reason.

Commit 8 is the largest single step in the stage and the one most likely to split; if it does, the split
runs along Lemma 2 / Lemma 3 / transfer conditions, which are three independently statable results.
Commits 4–9 are the G2 rewrite of 2026-08-23, resliced 2026-08-24, and they replace an earlier two-commit
plan built around a source step relation and a target step relation — those two modules are not restored
by the reslice, because keying a *step relation* on an explicit cohort argument is the defect §3 indicts,
and G2a-iii's relations take no cohort parameter.

**Why G2a-i comes first, and why it cannot be skipped.** The evaluators are needed under *either*
granularity: a big-step dispatch rule still has to say what a message-server body did to the valuation, or
`R`'s `ex ≡ ηr` component compares two things that never change. Statement granularity (§7) adds the
continuation, the small-step body relation and the τ classification on top of them — it does not create the
evaluator requirement.


**The precondition on commit 2 — asked, then settled the same day, and it resolved toward the harder
branch.** The question was whether `selectedActor` may be a priority minimum or must be a lexicographic
minimum on `(logicalTime, priority)`. **Measured: lexicographic.** `earliestDueArrival`
(`Relico/DTR/GeneralState.lean:142`) minimises arrival over the messages due at `now` rather than
requiring a unique arrival, and `readyActorsOf` records that arrival per actor, so a cohort with
mixed arrival times is reachable and priority must not be allowed to overtake an earlier message. §6
carries the full argument. The lexicographic form is therefore not a defensive choice but the only sound
one, and the two predicates the old layer left to its caller — `cohortSimultaneous` and `earliestReady` —
are exactly the half `selectedActor` now absorbs.

**A count that moved with G3's commit, flagged because this class of defect has cost the project four
findings.** (This paragraph said "commit 5" before the 2026-08-24 reslice, and it was wrong before it too:
the clause has always belonged to G3, which was row 7 and is now row 10. Naming the obligation rather than
the row number is the repair.) `LF.GeneralWellFormed` had **nine** clauses, and F49's whole content is that
the ninth is independent of the other eight and therefore cannot be dropped. G3's clause made it **ten**.
Every prose count of those clauses moved together, and F49's own phrasing — which speaks of "the ninth
clause" positionally — was re-read rather than renumbered, since its independence argument is about a
specific clause and not about an ordinal, and appending a tenth leaves `targetEndpointsUnique` ninth. The
historical F49 sites in `docs/STAGE_E_FINDINGS.md`, `docs/STAGE_E_DESIGN.md` and `docs/STAGE_F_DESIGN.md`
are therefore correct as written and were deliberately left alone.

Spelled-out English counts, not numerals, are the ones that go stale unnoticed; grep for the words. Row 10
found that necessary but not sufficient: two claims named the count without containing it — a leaf count
that was 2⁹, and a tactic justified as working "for the last conjunct specifically". **F84** records both
and extends the check to derived arithmetic and positional adjectives.

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
2. ~~**If `lfc` accepts a reaction priority attribute**, G3 inverts from justification to reversal (§8),
   and the "byte-identical" argument in `docs/STAGE_F_DESIGN.md` §7.4 becomes a statement about our
   printer rather than about the target.~~ **Settled negatively, 2026-08-25.** F77's probe 16f emitted
   `@priority(2)` / `@priority(1)` and `lfc 0.11.0` answered *"Unknown attribute: priority"*. No inversion:
   G3 landed as a refusal, and §7.4's argument remains a statement about the target. Kept rather than
   deleted because the prediction was the thing that made G3 a measurement instead of an assumption.
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
   **a τ step must not change any state that `R` constrains** — and the risk it was guarding moved to
   **G2a's granularity choice**, which is itself now **settled, 2026-08-24: statement-granular, and forced**
   (§7, F66 part 5). Dispatch granularity would have made both τ sets empty *and* made `R`'s third
   component `πx ≡ µr` trivially true, so it was not the cheaper option but an unsound one — it would have
   shipped the paper's relation with one of its three conjuncts doing no work. τ is therefore non-empty on
   both sides and the transfer conditions genuinely use it. What survives as a live prediction is the
   positive test above, checkable at the point `R` is defined in G2b.
4. **If the target LTS cannot be keyed on triggers alone** — because two reactions in one reactor share a
   trigger — then reaction identity needs the site keys from the F56 repair as an explicit index. F56's
   repair emits one action *and* one reaction per send **site**, so this is expected to be fine; it is
   listed because it is an assumption §7's action type rests on.

   **Outcome, 2026-08-25: right answer, wrong direction of concern.** Target reaction identity is fine, and
   for the stated reason — `generalReactionNamesOf` emits one reaction per site plus one per route, so no two
   reactions of a reactor share a trigger. What that same measurement exposes is the *cross-language* map:
   sites + routes reactions per message server is exactly why `ϕ(ms) = rct` is not a function (**F79**, §7).
   This item looked at the multiplicity from the target side, where it is harmless, and did not ask what it
   does to a bijection on actions. The lesson is the one §16's closing paragraph already draws: the item asks
   what might go wrong when this is built, not what the plan's own artefacts already say.
5. **If `generalWeakBisimulation_backward` needs `MessageServerPrioritiesDistinct` as well as the actor
   guard**, then §5's claim that selection needs only the actor guard is wrong, and the membership-indexed
   bridge propagates further than predicted. The signal is a proof that cannot close without reaching into
   a class's server list.
6. **If G5's `trace` constructor forces a change to `GeneralBody`** rather than being absorbed by the
   existing flat `List`, the widening is larger than stages C and D were, and the honest response is to
   split G5 into its own stage rather than to quietly reduce it — the observability decision is settled,
   so the variable is scheduling, not scope.
7. **If P24's split `TIME PROGRESS` breaks Lemma 1**, the repair is wrong and the alternative repairs named
   in P24 come back into play. It should not: Lemma 1 tracks logical-time *equality* between corresponding
   events, and relabelling a step that leaves logical time unchanged cannot disturb an invariant about
   logical time. The signal is a Lemma 1 case that needs to know which label the microstep advance carried.
   Stated because it is the one place the stage modifies a rule the paper's other results are proved over
   *away from* what the paper prints, and an unstated assumption there would be the F53 failure — a repair
   outliving the argument for it. (**F74** later modified a second such rule, DTR's `TIME PROGRESS`, in the
   opposite direction: it tightened our transcription back *onto* what the paper prints, after the loose
   version turned out to make Lemma 1 false on its own, independently of P24's split.)
8. **If expression evaluation cannot be made total**, G2a-i's signature is wrong and the step relations
   inherit a failure mode. An unbound variable, a type mismatch surviving well-formedness, or a partial
   operator would force evaluation into `Option` and then every rule in Tables I and II acquires a
   propagation case the paper does not have. The check is at G2a-i, before any rule is written: if the
   evaluator can be given a total signature against a well-formed program, the semantics stay shaped like
   the paper's; if it cannot, that is a finding about the well-formedness predicate's coverage rather than
   about the evaluator.

   **Outcome, recorded rather than substituted.** Evaluation is partial — all three causes this item
   anticipated are real, and `Relico/DTR/GeneralEvaluation.lean` names them: an absent binding, an operand
   type mismatch (`DTR.GeneralExpr`'s own docstring declines to enforce type-correctness), and a zero
   divisor. But the item's **second branch is wrong**, and reading it as written would mislead G2a-iii into
   work it does not owe. Partiality does *not* propagate into the rules and is *not* a finding about
   well-formedness coverage, because the rules premise `evaluate … = some v`: where evaluation fails no
   transition exists, the configuration is simply stuck, and
   `Correctness.compileGeneralExpr_evaluation_none_iff` proves the two sides fail in exactly the same cases,
   so a stuck source configuration has a stuck target counterpart. Nothing asymmetric is claimed and no rule
   acquires a case. What partiality *does* cost is a fragment restriction for the zero-divisor cause alone,
   because there the emitted C++ has undefined behaviour rather than a stuck state — **F67 part 4**, which
   G6 owes and which also asks for a guard refusing the syntactically decidable instances. The precedent for
   pairing a partial evaluator with a relative totality theorem is `DTR/StoreEvaluation.lean`, which this
   item did not consult.

**What this section got wrong, recorded because the section's whole purpose is to be checkable.** Not one
of F66's seven parts appears above, and F66 part 2 alone changed the stage from nine commits to twelve. The
reason is visible in how the items are phrased: every one of them asks *what might go wrong when this is
built*, and none asks *does what this plan names already exist, and does it say what I claim*. Those are
different questions, and the second is answerable with `ls` and `grep` in minutes. The transferable rule
now recorded in F66: **a design section that names a deliverable, a directory, an identifier or a rule
should be checked against the artefact before the stage it governs opens.**

**And the rule, once written here, was broken twice more — which says something the rule itself does not.**
**F69** and **F70** are both instances of it: §7 and §13 named the superdense tag and `upd` as G2a-ii's work
when four tag definitions already existed proved from v0, and named weak bisimulation as G2c's work when
`Relico/Common/WeakTransition.lean` already proves it generically. Neither was caught by the F66 sweep,
because that sweep checked *modules and identifiers* — things with names one can `ls` for — while what was
missed here is a **proved theorem** and a **signature**. So the rule needs a second clause: ask not only
whether the named artefact exists, but whether the *property* about to be proved is already proved
somewhere, and whether an existing generic definition's argument types already dictate the shape of what is
about to be declared. F70 is the sharper of the two, because its constraint reached **backwards** three
commits — a foundation G2c consumes forced two declarations in G2a-ii — and no check that reads a design
section in isolation can see that.

**A third instance, and it is the cheapest kind to prevent.** **F71**: this section's respelling of the two
label types settled that a `Dtr`/`Lf` infix is redundant inside `namespace DTR` and `namespace LF` — and §7
went on specifying `GeneralDtrStep` and `GeneralLfStep` for the two step relations eleven lines above the
paragraph making that argument. Unlike F69 and F70, nothing had to be measured to catch this beyond running
the grep the decision itself implies; the failure was of *scope*, applying a decision to the identifiers that
prompted it rather than to the convention it establishes. The same paragraph had also gone stale twice over —
`action` where the later paragraph says `label`, and a cohort read off a configuration type G2a-ii replaced.
That last one is the instructive part: a design sentence can be falsified by a *neighbouring obligation's*
decision, with nobody editing the sentence.


## 15. Decisions, and how each was settled

All six are settled; this section is the record, not a request. Four were put to the decision-maker on
2026-08-23, and two were resolved by measurement — one on 2026-08-23 and one on 2026-08-24.

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
   **assignments and both send forms** as τ on both sides — read off Tables I and II, *not* "assignments
   and scheduler stuttering", which was this section's wording until 2026-08-24 and which inherited a
   misnomer from Theorem 1's own proof (F66 part 4, and P24 for the defect it concealed) — plus, on the LF
   side only, the microstep-only advance that P24's split relabels, so the two τ sets are **not** in
   bijection and `τ*` has exactly one surplus step to absorb (**F75** part 1) — and derives
   finite-trace agreement from it, so aims 8 and 9 are discharged for the general family rather than
   owed. **Four** divergences are documented in §7: two were already forced by earlier findings, one is
   scope, and the fourth is P24's split `TIME PROGRESS`, without which the theorem being claimed is false
   of a zero-delay send. §7.
5. **Commit order — may G6's documents land last? → Yes, and it is now the twelfth commit.** F63 is filed
   and `docs/supported-fragment.md` carries a scope marker pointing at it, so the interval is documented
   rather than silent. §11, §13. (It was the ninth until the 2026-08-24 reslice; the position moved, the
   decision did not.)
6. **G2a's LTS granularity — dispatch or statement? → Statement, with continuations.** Not delegated and
   not asked, because it turned out not to be a judgment call: §7 had already committed `R` to the paper's
   `πx ≡ µr` component, and the paper defines both continuations as remaining-statement lists with `ε`
   premised on both `TAKE` rules, so dispatch granularity would have made that conjunct vacuous. Settled
   by measurement on 2026-08-24 — the measurement being that statement granularity is *available and
   symmetric*, which is the part that could have gone the other way. §7, F66 part 5.
7. **The label correspondence — bijection or relation? → Relation, and this one was delegated and then
   withdrawn.** F78 escalated it as a four-way choice on 2026-08-25, on the ground that it decides what the
   headline theorem observes. It is not a choice: Fig. 2a's `Controller` declares one message server and
   Fig. 2b's answers with two reactions, so the functional shape is refuted in the paper's own illustrative
   translation, and the fragment-restriction option would refuse that example. Settled the same day by
   reading the figure the claim is about, which is what should have happened before the escalation. §7,
   **F79**, **P25**. The other half of F78 — F76's selection divergence — stays delegated, because it
   decides behaviour rather than notation.

The precondition on G1 — priority minimum or lexicographic minimum — was **not** a judgment call and was
not treated as one: it was measured against `earliestDueArrival` and `readyActorsOf`, and it refuted the
simpler form. §6 and §14 item 1.




