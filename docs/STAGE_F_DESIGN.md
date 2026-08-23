# Stage F design — fan-in ordering, and the two priority sorts that realize it

Written 2026-08-23, after stage E landed at `dddf04b`/`3290ad4` and after task #80 measured the
target facts §2 rests on. The convention of `docs/STAGE_C_DESIGN.md`, `docs/STAGE_D_DESIGN.md` and
`docs/STAGE_E_DESIGN.md` is kept: every claim about the repository or the toolchain carries the file
and line a reviewer can check, projections that could turn out false are stated **as** projections in
§11 so that the design can be scored against what happens, and the boundary with the neighbouring
stages is stated at the top because all three of the previous stages had theirs misread at least once.

**Stage F's findings live in [`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md), starting at F59.** This
document owns what stage F *does* and why; that one owns what stage F *found wrong*, including two
corrections to this document made after its own commit-1 gate run.

## 1. What stage F is, and exactly where its boundary falls

Stage F makes the **order** of a receiver's reactions realize Rebeca's **priorities**. Stage E built
the fan-in *topology* and proved what order it emits; it deliberately proved nothing about whether
that order means anything. Stage G makes priority **observable end to end** and lands the S1
`switch-pair` benchmark.

That three-way split is not inferred here, it is quoted. `docs/STAGE_E_DESIGN.md:48-49`:

> *"Stage E emits the receiver's per-sender reactions in a defined order and proves what that order
> is; it does not prove that the order realises actor priority, and it does not make priority
> observable. Fan-in *topology* is stage E because it falls out of the naming rule (§4.1); fan-in
> *ordering* is stage F, and the observable trace is stage G."*

`docs/STAGE_C_DESIGN.md:17` says the same from the other end — *"stage F for the many-to-one case of
paper section III-D"* — and `docs/PAPER_CORRECTIONS.md:814` states the deliverable: *"Stage F is
where the sort and its ordering theorem land."*

### 1.1 Stage F carries TWO obligations, at two granularities, and they compose

This is the single most important structural fact in the design, and getting it wrong in either
direction would either halve the stage or duplicate stage G.

**Level 1 — §III-D, *within* one message server's group.** Order that server's **port** reactions by
the **sending actor's** priority. This is the paper's §III-D construction: multiple actors send the
same message to one target, LF forbids many-to-one connections so each sender gets its own input
port, and *"to preserve determinism when both messages arrive at the same logical time, reactions are
ordered according to DTR actor priorities"* (transcribed at `docs/STAGE_C_DESIGN.md:212-216`).

The paper's next sentence names the mechanism, and it agrees with what §2.1 measured independently:
*"Because `temp` has higher priority than `smoke` (lines 36-38), the `readingFromTemp` reaction is
**declared first**, ensuring its message is processed first."* So the paper too realizes priority by
declaration order rather than by any priority attribute, which is worth recording because it means
§2.3's inert `LF.GeneralReaction.priority` field is not a shortfall against the paper — the paper never
asked for it.

**Level 2 — Lemma 2's same-actor case, *across* message servers.** Order the whole per-server
**groups** by the receiver's own **message-server** priority. This is what
`docs/STAGE_E_FINDINGS.md`'s F57 entry routes here and what `docs/PAPER_CORRECTIONS.md:814` means by
"the sort".

They compose rather than conflict **because they act on different granularities**: message-server
priority orders the groups, actor priority orders the port reactions inside one group. Two port
reactions of the *same* message server cannot be ordered by message-server priority at all — they
share a server and therefore share a priority. Two reactions in *different* groups are never
candidates for the §III-D rule, because §III-D is about several senders of **one** message.

An earlier reading of this project's notes recorded the opposite — that §III-D's actor-level mechanism
made it stage G's, and that `prty_l` and `prty_g` "both demand an order on one reaction list and can
disagree, with no tie-break given anywhere". The first half is withdrawn: the design documents assign
§III-D ordering to stage F in as many words. The second half dissolves once the granularities are
separated; there is no tie to break, because no pair of reactions is ordered by both rules.

### 1.2 The 1 + k group structure the sorts operate on

A generated receiver's reaction list is **grouped per message server**, each group being one
action-triggered reaction followed by one port reaction per incoming send site. The routed fixture's
`Gateway` shows it, from the expected text in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`:

```
reaction(report_action)            <- the message server's own logical-action reaction
reaction(reportToHub1FromProbe)    <- one port reaction PER INCOMING SEND SITE
reaction(reportToHub2FromProbe)
reaction(reset_action)
reaction(resetToHubFromProbe)
```

`docs/STAGE_E_DESIGN.md:732-734` records that the grouping is deliberate and says why: *"Grouping by
message server rather than emitting all action reactions and then all port reactions is deliberate:
stage F's ordering argument is about the port reactions of one message server, so keeping them
contiguous makes the later statement compositional."* Stage E built the shape stage F needs.

So **level 2 permutes whole groups and level 1 permutes within a group.** Neither ever interleaves
one group's reactions into another's, which is what keeps the two statements independent.

### 1.3 What stage F does not do

- **It does not make priority observable.** A generated program has no output (§2.4), so a runnable
  witness that priority was honoured is stage G's problem and needs machinery that does not exist.
- **It does not wire `LF.GeneralReaction.priority`.** That field is inert (§2.3). Stage F realizes
  priority by list order and leaves `assembleGeneralMessageReaction_priority` green (§7.4).
- **It does not touch control flow.** A send inside an `if` or a `for` is still refused; that is
  stage H.
- **It does not repair Lemma 2's different-actor case.** That case is unsound as the paper states it
  (recorded already, see `docs/PAPER_CORRECTIONS.md` P1), and it is about *reactor* order rather than
  reaction order. Stage F's theorem is Lemma 2's **same-actor** case only, and §5 states the premise
  that scopes it.

## 2. The measured target facts this design rests on

Four facts, all measured rather than assumed, three of them by task #80 on 2026-08-23 against
`lfc` 0.11.0.

### 2.1 Declaration order decides at one tag, in all three shapes a generated receiver produces

Probe **section 15** of `tools/paper-measurements/lf_semantics_probe.sh`, six probes in three pairs,
run with `PROBE_FILTER=stageF`. Every pair is byte-identical between its members except for the order
two reactions are **declared**; all six compiled and ran clean:

```
stageF_action_declsame_AB     RELICO_DECL A 1 ; RELICO_DECL B 2
stageF_action_declswap_BA     RELICO_DECL B 2 ; RELICO_DECL A 1
stageF_onesender_twoports_AB  RELICO_PORT A 1 ; RELICO_PORT B 2
stageF_onesender_twoports_BA  RELICO_PORT B 2 ; RELICO_PORT A 1
stageF_action_port_mixed_AB   RELICO_MIX ACT 1 ; RELICO_MIX PORT 2
stageF_action_port_mixed_BA   RELICO_MIX PORT 2 ; RELICO_MIX ACT 1
```

Every pair swapped. **Declaration order decides**, and the whole design depends on it: a sort of the
generated declarations is a semantic act precisely because of this measurement.

The load-bearing member is `stageF_action_declswap_BA`, and it is worth saying what it rules out.
Both members schedule `slotA` before `slotB`; only the declarations differ. So **schedule order does
not decide.** That distinction had never been measured for action triggers before — the pre-existing
`action_two_actions_two_reactions` schedules `slotA` first *and* declares it first, so its result was
consistent with either cause. Four Lean docstrings and one entry of `docs/STAGE_E_FINDINGS.md` cited
that probe for the claim anyway; the mis-attribution is finding **F58** and the citations now point
at section 15.

Why it matters here rather than as a curiosity: **stage F is the first place the two orders diverge.**
A priority sort reorders reaction *declarations* while the `schedule()` calls stay in the sender
body's statement order. Had schedule order decided, sorting the declarations would have achieved
nothing observable, and the ordering theorem would have been true of the emitted text and false of
the execution. That contingency is now closed by measurement, and no restriction of the accepted
fragment is needed.

### 2.2 A `schedule(…, 0ms)` and a connection's `after 0 msec` land at the same microstep

Pair 3 proves this as a side effect, and no probe was designed for it. `stageF_action_port_mixed_BA`
swapped its output, which is only possible if the action delivery and the port delivery are at the
**same complete tag**. Had they differed in microstep, complete-tag order would have fixed the
outcome and swapping two declarations could not have moved it. It moved.

This is what licenses treating a receiver's action reaction and its port reactions as **mutually
orderable by declaration** — the interleaving §7.3 has to get right — rather than as two populations
separated by the microstep.

### 2.3 `LF.GeneralReaction.priority` exists and is inert

`Relico/LF/GeneralSyntax.lean` gives `structure GeneralReaction` a field `priority : Option Nat :=
none`. But `grep -n 'priority' Relico/LF/GeneralCppPrinter.lean` returns **nothing**: the printer
never reads it, so nothing in the emitted program depends on it. Setting it would be semantically
inert, and **list order is the only realizable mechanism.** §7.4 draws the consequence for the
theorem that guards the field.

### 2.4 A generated program has no observable output at all

`DTR.GeneralStmt` has exactly two constructors, `assign` and `send`; the fragment has no print
statement; the printer emits no `cout` or `printf`; and `LF.GeneralReactor` has no preamble field
through which one could be injected. The only observable of a generated program is its **exit code**.

Two consequences for this stage. `frontend/check-general-lf-target.sh` checking only exit codes is
**forced, not lazy** — do not "improve" it by diffing `run.log`. And stage F's gate **cannot** be a
generated program that prints its reaction order; the ordering argument must be a measurement of the
target language (§2.1) composed with a theorem over emitted structure (§8). The item in
`docs/STAGE_E_FINDINGS.md`'s "What is left open" that asked for the other thing was mis-specified,
and #80 corrected it rather than ticking it.

## 3. The paper questions stage F inherits, and why it opens no new P number

`docs/PAPER_CORRECTIONS.md:686` already fixes the list: *"Stage F is unaffected: its paper-side
questions are P1, P4, P5 and P23."* All four exist and none needs restating here:

- **P1** — LF's cross-reactor order comes from the dependency graph, not declaration order. This is
  the boundary that keeps every statement in this stage *within one reactor*, and it is why Lemma 2's
  different-actor case is out of scope (§1.3).
- **P4** — the paper gives no tie rule. Stage F must therefore say what happens when two priorities
  are equal, and §6 makes that a guard question rather than an ordering question.
- **P5** — priorities may be absent.
- **P23** — `prty_l : MName → ℕ` and `map_M : MName → RName` are **total** functions on message-server
  names, which the paper's own Fig. 1a, Fig. 2a and Fig. 4 refute: Fig. 4's grammar makes `@priority`
  optional, Fig. 2a line 31 exercises an unannotated server in the very example the ordering argument
  is stated over, and Fig. 2a declares `sendReading` in two different reactive classes so that one
  `MName` would carry two reactions and one priority.

The repository already implements the indexed, partial form that P23's suggested edit asks for:
`DTR.GeneralMessageServer.priority : Option Nat`, per server per class. Under the standing rule that
**where the paper and the repo conflict the repo is definitive**, stage F implements the repo's
convention and cites P23 rather than reconciling toward the paper's signature.

**No new P number is opened by this design.** That is a deliberate outcome and it was checked rather
than assumed: the two defects task #79 derived independently turned out to be exactly P23's two, in a
version with better evidence than the derivation had. Restating them as P24 and P25 would have been
the F54 failure — a record that exists being written a second time because it was not looked for.

## 4. The architecture: sort the input lists, never the emitted output

### 4.1 What the AST already provides, and what it already decided

Both priorities are **already fields of the general AST**, and stage F is not adding them:

- `DTR.GeneralMessageServer.priority : Option Nat := none` — `Relico/DTR/GeneralSyntax.lean:349`
- `DTR.GeneralActorInstance.priority : Option Nat := none` — `Relico/DTR/GeneralSyntax.lean:422`

More importantly, the AST **already fixed the absence convention**, and stage F inherits it rather
than choosing it. `GeneralSyntax.lean:335-337`:

> *"`priority` is local message-server priority. An absent priority is a priority class in its own
> right and is ordered after every explicit one, which is the convention the earlier payload family
> already fixed."*

and `:385-386` on the projection `GeneralReactiveClass.messageServerPriorities`: *"An absent priority
is retained as `none` rather than dropped, because absence is a priority class and two absences are a
tie."* This discharges **P5** at the AST level — absent priorities are representable and ordered —
and it fixes half of **P4**: two absences tie, and §4.4 says what a tie does.

The `GeneralActorInstance.priority` field is currently read by **exactly one** place in the entire
repository, `Relico/DTR/GeneralWellFormed.lean:490`, inside a predicate that nothing enforces. Level 1
therefore introduces the **first consumer of actor priority in the translation**, which is a
checkable statement and the sharpest available summary of how little precedent level 1 has.

### 4.2 Where the sort goes, and why that choice is forced

The tempting implementation is to sort the reaction list that `assembleGeneralMessageReactions`
produces. **Do not.** Sort the *input* list each assembly function walks, and leave every emission
function emitting its input's order.

The reason is that the proven blueprint already does exactly this, and its proof structure depends on
it. `Relico/Translation/MultiStoreBasic.lean:18` defines `priorityOrderedMessageServers`, and
`Relico/Correctness/PriorityOrder.lean` then proves the ordering result in two pieces:

1. `serverNamePrecedesOrEqual_compileMessageReactions` — an **order-preservation** lemma, proved by
   induction on an arbitrary `messageServers : List DTR.MessageServer`. It says compilation is
   monotone: whatever order goes in comes out. It mentions priority nowhere.
2. `priorityServerNamePrecedesOrEqual_compileMessageReactions` — the **priority** result, obtained by
   `simpa … using` piece 1 **instantiated at `DTR.MessageServerPriority.normalize messageServers`**.

So the priority theorem is piece 1 applied to a sorted list. Nothing about compilation had to be
re-proved to obtain it, because compilation never learned what priority is.

That factorization is what makes §7.1's reconciliation with task #65 cheap instead of destructive,
and it is why the architecture is a design decision rather than an implementation detail. Sorting the
output would fuse the two pieces into one theorem about a sort composed with a traversal, and both
existing proofs would have to be rebuilt.

### 4.3 One polymorphic sort, instantiated twice — not two copies

`DTR.MessageServerPriority.normalize` (`Relico/DTR/MessageServerPriority.lean:150`) is a **stable
insertion sort**, `normalize (x :: xs) = insert x (normalize xs)`, with `insert` branching on
`PrecedesOrEqual`. It is monomorphic in `DTR.MessageServer`. A second monomorphic copy already exists
for the payload family at `Relico/DTR/MultiStorePayloadPriority.lean:84`.

Stage F needs the same sort at **two different element types** — `GeneralMessageServer` for level 2
and `GeneralActorInstance` for level 1 — so following the existing precedent would mean a third and a
fourth copy. This design instead specifies **one module, `Relico/DTR/GeneralPriority.lean`, generic in
the element type and parameterized on a priority projection**:

```
variable {α : Type} (priorityOf : α → Option Nat)
def PrecedesOrEqual (left right : α) : Prop      -- explicit before none; ≤ on explicit
def insert    : α → List α → List α
def normalize : List α → List α
```

instantiated as `GeneralMessageServerPriority.normalize := GeneralPriority.normalize (·.priority)`
and `GeneralActorPriority.normalize := GeneralPriority.normalize (·.priority)`.

The reason is specific to stage F and is not a general preference for abstraction. §1.1's composition
argument — that the two levels cannot disagree because they order disjoint pairs — assumes both levels
use the **same** absence convention. Two independent copies could drift apart on exactly that point,
and the drift would be invisible: both would still compile, both would still be total orders, and the
composition claim would quietly become false. Sharing one definition makes the shared convention a
type-checked fact rather than a comment. The repository has already paid for parallel copies drifting
once, in F49's ninth clause and in the four stale `F34–F5x` ranges.

**Risk, stated because it is real:** the blueprint's proofs are written against the monomorphic
version, so they transfer by *re-derivation* rather than by rename. If the generic version costs more
than roughly one working session, fall back to two monomorphic copies plus an explicit theorem that
the two `PrecedesOrEqual` relations agree on absence, which recovers the type-checked guarantee at the
cost of duplication. §11 records this as a projection that can be falsified.

### 4.4 The tie rule, and why stability is the right answer

**P4** notes the paper gives no tie rule. Stage F's answer: the sort is **stable**, so a tie falls
back to source declaration order. It is worth stating *why* it is stable, because the mechanism is not
the obvious one and getting it backwards would invert the tie order.

`insert` places the incoming element **before** the first element of equal-or-lower priority — the test
is `PrecedesOrEqual`, which is reflexive, so an equal-priority element does stop the scan. Taken alone
that would put a later element ahead of an earlier one. What makes it stable is that `normalize`
traverses the source list **right to left**: `normalize (x :: xs) = insert x (normalize xs)`, so the
element that comes *earlier* in source is inserted *later*, and lands ahead of the equal-priority
elements already placed. Stability is a joint consequence of the non-strict test and the traversal
direction, and the blueprint's own docstring says so (`Relico/DTR/MessageServerPriority.lean:115-118`):
*"Insertion occurs before the first declaration of equal or lower priority. Because `normalize`
processes the original list from right to left, this preserves source declaration order among
equal-priority servers."*

The generic version must keep **both** halves of that, and a test made strict "for clarity" would
silently reverse ties. §11's F-1 covers the risk.

This is not merely convenient; it **agrees with decision `0041`**, which resolves equal LF microsteps
by deferring to generated reaction declaration order. A stable sort is the unique choice that makes
the two conventions the same convention: ties in priority defer to declaration order, and ties in
microstep defer to declaration order, so a tie in both defers to declaration order once rather than
ambiguously twice.

### 4.5 Sortedness, and the two different things it and a value pin each catch

Measured on 2026-08-23, before any of §10's theorems were written: `List.Sorted`, `List.Pairwise` and
`Chain'` occur **nowhere** under `Relico/` — 144 files, no match. Both pre-existing sorts
(`Relico/DTR/MessageServerPriority.lean`, `Relico/DTR/MultiStorePayloadPriority.lean`) prove only
*structural* facts about `normalize` — that it permutes its input and preserves membership, length and
uniqueness — together with facts about the *relation* in isolation
(`explicit_precedes_unannotated`, `lower_numeric_precedes`). Nothing in either file connects a priority
comparison between two elements to their relative position in the output. So **no sort in this
repository had been proved to sort**, and §6's guard-relative statement cannot even be *stated* without
that step.

`Relico/Correctness/PriorityOrder.lean` does not supply it, by construction, and it is worth being exact
about why, because §9 takes that file as the blueprint. Its headline
`priorityServerNamePrecedesOrEqual_compileMessageReactions` is an iff whose source side is
`DTR.PriorityServerNamePrecedesOrEqual`, and `Relico/DTR/MultiStorePriorityScheduling.lean:64` *defines*
that as a name scan over `MessageServerPriority.normalize`'s **own output**. So the theorem says: emitted
reaction order equals normalized declaration order. That is order **preservation through compilation** —
the harder half of the two, and true — but it says nothing about whether normalized order is priority
order. This is not a false claim anywhere: `docs/STAGE_E_DESIGN.md:1025-1027` describes it as *"a
two-way correspondence between source priority order and reaction declaration order"*, and for that
family position in the normalized list **is** the definition of source priority order, so no `F` number
is opened. What it does mean is that the theorem is unable to detect a sort that sorts wrongly.

Stage F therefore adds `Sorted` and `normalize_sorted` to `Relico/DTR/GeneralPriority.lean`. `Sorted` is
defined locally rather than taken from core: the development has zero dependencies and no prior use of
that API, so an unverifiable core-lemma name is avoidable risk, and the proof needs only
`priorityPrecedesOrEqual_trans` and `priorityPrecedesOrEqual_total`, both already proved in the same
file. The results are then stated as **append splits** rather than as name orders, per §9.2, because that
is the shape `assembleGeneralPortReactions_instanceDeclarationOrder` and `routesOf_split` already have.

A value pin is *still* required alongside it, for two reasons sortedness is structurally unable to cover.

**Sortedness cannot see tie order.** `Sorted` is stated against `PrecedesOrEqual`, which is reflexive on
equal priorities, so for two tied elements *both* orders are sorted. A `normalize` that reversed ties
would satisfy `normalize_sorted` and the permutation lemma simultaneously and still contradict §4.4 and
decision `0041`. Only a concrete input distinguishes the two.

**Sortedness cannot see the direction of the absence convention.** It is proved relative to
`PriorityPrecedesOrEqual`; if that relation placed absent priorities *first*, the sort would place them
first and `normalize_sorted` would prove the result sorted just the same.

Hence the third new file in §10, `Relico/Tests/GeneralPriority.lean`. The same measurement explains why
it is owed at all: the restricted family's single four-element `rfl`
(`Relico/Tests/MessageServerPriority.lean:104`) was, when measured, the only thing pinning any priority
sort's behaviour anywhere in the repository, and before this file `Relico/Tests/` held 172 modules and
not one of them mentioned a general-family declaration. A wrong sort that agrees with the right one on
that one fixture stays fully green.

## 5. The premise that scopes the ordering theorem

Stage F's theorem is not "the generated program executes DTR's chosen message next". It cannot be,
for a reason that is the paper's and not this translation's: DTR selects by minimum **metric** arrival
time and then applies message-server priority among everything pending at that time, whereas LF
selects by minimum **complete tag**, which is metric time *plus microstep*. Two messages that DTR
considers simultaneous can land at different microsteps in LF, and then LF's tag order decides before
any declaration order is consulted.

Decision `0041` (`PAPER DRIFT APPROVED`) states the condition under which the two agree, and stage F
takes it as an **explicit premise** rather than proving it:

> equal LF microsteps defer to generated reaction declaration order; and if one LF occurrence has a
> strictly earlier microstep than another, then its DTR message server strictly precedes the other
> under normalized DTR priority.

Two consequences for what gets written. First, the theorem statement is about **emitted declaration
order**, a structural property of the LF program, composed with §2.1's measurement that declaration
order decides at one tag — not about a trace. Second, the premise is discharged for the concrete
fixture, not in general: §2.2 measured that a self-`schedule(…, 0ms)` and a connection's
`after 0 msec` deliver at the *same* microstep, which is what makes the premise's equal-microstep
branch the one that actually applies to generated receivers.

`P1` bounds this further. LF's order *between* reactors comes from the dependency graph, not from
declaration order, so every statement in stage F is scoped to a single reactor. Lemma 2's
different-actor case is therefore out of scope, and stage F proves its **same-actor** case only.

## 6. The guard question, settled against adding a clause

`Relico/DTR/GeneralWellFormed.lean` already contains both distinctness predicates, each with a
`Decidable` instance: `GeneralMessageServers.PrioritiesDistinct` at `:454`,
`GeneralActorInstances.PrioritiesDistinct` at `:484`, wrapped as `MessageServerPrioritiesDistinct`
(`:514`) and `ActorPrioritiesDistinct` (`:538`). They are defined *after* `wellFormed` (`:359`) and
conjoined into nothing: `wellFormed` is exactly five clauses —
`bindingsMatchDeclarations && argumentsMatchConstructor && sendTargetsDeclared &&
sendsResolveToMessageServers && namesUniqueAndValid` — and none of them is about priority.

So the obvious move is to add a sixth clause and get a strict total order for free. **This design
rejects that, on evidence.**

`PrioritiesDistinct` is `(map priority).Nodup` over `List (Option Nat)`. Because `none` is one of the
values, `Nodup` forbids **two absences**, which the predicate's own docstring states plainly
(`:447-449`): *"Because an absent priority is itself a priority class, this condition also permits at
most one unannotated message server per class."*

Measured against the corpus, that would reject most of what the pipeline currently accepts:

| fixture | message servers in one class | annotations | priority list | `Nodup` |
| --- | --- | --- | --- | --- |
| `expressions.rebeca` (`Calculator`) | 3 | 0 | `[none, none, none]` | **false** |
| `control-flow.rebeca` | 2 | 0 | `[none, none]` | **false** |
| `send-sites.rebeca` | 2 across 2 classes | 0 | `[none]`, `[none]` | true |
| `two-classes.rebeca` | 2 | 1 | `[some _, none]` | true |
| `priorities.rebeca` | 3 | 3 | all explicit | true |

Adding the clause would make `expressions.rebeca` and `control-flow.rebeca` ill-formed, break both
gates, and shrink the accepted fragment — for no gain, since neither fixture has a fan-in at all. It
would also contradict **P23**, whose whole complaint is that the paper's totality assumption is
refuted by Fig. 2a line 31 exercising an *unannotated* message server in the very example the
ordering argument is stated over. Enforcing distinctness would make this pipeline reject the paper's
own figure.

**The decision:** `wellFormed` is unchanged, and the strict-order theorem takes `PrioritiesDistinct`
as a **hypothesis**. Concretely there are two statements at each level:

- **unconditional** — the sort is deterministic and stable, and emitted order equals sorted order.
  True of every accepted model, no guard.
- **guard-relative** — emitted order *realizes priority strictly*, hypothesis
  `ActorPrioritiesDistinct` (level 1) or `MessageServerPrioritiesDistinct` (level 2).

Neither statement can be made without the sortedness step of §4.5, which no sort in this repository had
taken: the unconditional one names *"sorted order"*, and the guard-relative one asserts a relation
between two elements' priorities and their emitted positions, which is precisely what a permutation
lemma cannot express.

This is the pattern the repository has now used twice deliberately, at #60 (`docs/STAGE_E_DESIGN.md`
§10.2's setPort `Nodup`, proved guard-relative after the unconditional form was refuted) and #58
(endpoint uniqueness, proved routing-indexed). It is also what the predicate's docstring anticipates in
as many words (`:450-452`):
the ordering it strengthens is *"a total preorder in which every explicit priority precedes `none`"*
which *"becomes a strict total order exactly when it holds."* The predicate was written for a
hypothesis, not for a clause.

The user's standing instruction on the analogous case was **"Record it, prove the scoped version"**,
and this is the same shape: do not strengthen the guard, scope the theorem.

## 7. Reconciling with task #65, which is less destructive than it first looks

### 7.1 The theorem stage F was expected to falsify is a conjunction, and only half of it is at risk

`assembleGeneralPortReactions_instanceDeclarationOrder` (`Relico/Translation/GeneralBasic.lean:6861`
at the time of writing — throughout this document the **declaration name is the anchor and the line
number is a hint**, because editing a docstring moves every line below it and eight numerals in an
earlier revision of this file were falsified by exactly that)
looked like the central casualty of this stage. Its docstring says *"A receiver's port reactions for one
message server appear in main-block instance-declaration order"* and, presciently, *"This is not a
priority result, and stage F owns that claim."* Stage F changes that order, so the theorem seemed to
require restatement.

Reading the statement rather than the docstring shows it is a **conjunction of two facts of different
kinds**, and they have different fates:

- **Conjunct 1** — `routesOf model = .ok (earlierRoutes ++ laterRoutes)`. This one mentions `model`,
  and it is the one that describes what the pipeline emits.
- **Conjunct 2** — `assembleGeneralPortReactions … (earlierRoutes ++ laterRoutes) =
  assembleGeneralPortReactions … earlierRoutes ++ assembleGeneralPortReactions … laterRoutes`. No
  `model`, no instances, no declaration order. It says only that port-reaction assembly **distributes
  over append**, i.e. that it is order-preserving.

Conjunct 2 is precisely the level-1 analogue of the blueprint's order-preservation lemma, and it
already exists, already proved, already green. It is reusable **verbatim** — it is `simp`-derivable from
`assembleGeneralPortReactions_append`, which in turn rests on
`generalRoutesIntoMessageServer_append` (`Relico/Translation/GeneralRouting.lean`) and
`List.map_append`. Stage F's level-1 theorem is that lemma composed with the sort, exactly as
`priorityServerNamePrecedesOrEqual_compileMessageReactions` is its lemma composed with `normalize`.

So the honest statement is: **conjunct 2 survives verbatim, and conjunct 1 needs one hypothesis
re-keyed, not a rebuilt proof.** Under §7.2 the sort moves inside `routesOf`, so `routesOf` remains
exactly what the receiver's port reactions are built from — the theorem stays about the pipeline. What
stops being true is the *link* the hypothesis asserts: `hInstances : model.instances = earlier ++ later`
no longer implies that the table splits as `earlierRoutes ++ laterRoutes`, because the table is now
built from the ordered list and a sort does not distribute over an arbitrary append. Re-keying the
hypothesis to `priorityOrderedInstances model = earlier ++ later` restores it, and the existing proof
goes through unchanged because it reaches the body only through `routesOf_split`, whose own `show` is
re-keyed the same way.

The docstring is a separate repair and a larger one. *"A receiver's port reactions for one message
server appear in main-block instance-declaration order"* was true and becomes false — after stage F they
appear in **actor-priority order, ties broken by main-block declaration order**. Its second sentence,
*"This is not a priority result, and stage F owns that claim,"* was accurate when written and stops
being accurate at the moment this stage lands, because the statement then carries part of the priority
claim itself. Both sentences are in the diff.

### 7.2 `routesOf` routes the ordered list; a sorted twin beside it would orphan six theorems

Two ways to make emission follow priority: teach `routesOf` to route a sorted instance list, or leave
`routesOf` alone and give the reactor assembly a sorted twin to walk instead. **This design takes the
first.** An earlier draft of this section took the second, on a containment argument that turns out to
be arithmetically backwards; the count that settled it is below, because the reasoning generalises to
every future change of this shape.

```
def priorityOrderedInstances (model : DTR.GeneralModel) : List DTR.GeneralActorInstance :=
  GeneralActorPriority.normalize model.instances

def routesOf (model : DTR.GeneralModel) : Except String (List GeneralRoute) :=
  routesOfInstances model (priorityOrderedInstances model)
```

**Why the twin loses.** `routesOf` is mentioned in nine load-bearing places and exactly **one** of them
is executable code: the `match routesOf model with` inside `compileGeneralModel`. The other eight are
statements, and **six** of those take
`routesOf model = .ok routes` or `= .error message` as a **hypothesis about what the pipeline
computed**: `compileGeneralModel_ok`, `compileGeneralModel_error_routes`,
`compileGeneralModel_error_classes`, `compileGeneralModel_connections`,
`compileGeneralModel_ports` and `compileGeneralModel_ok_iff`. Introducing a sorted
twin and pointing the `match` at it would leave all six **green and simultaneously vacuous** — still true,
still built, still counted by the gate, and no longer about the route list the translator actually
produces. That is precisely the defect class F45 and F47 recorded: a true claim whose subject silently
moved. Nothing in the gate can detect it, because a theorem does not stop compiling when it stops
mattering. The remaining two statements are the structural ones in the table below.

**Why redefining wins, measured rather than argued.** No proof in the repository unfolds `routesOf` —
there is no `unfold routesOf`, no `simp [routesOf]`, no `rw [routesOf]` anywhere under `Relico/`. Its
body is reached in exactly one proof, `routesOf_split` (`Relico/Translation/GeneralRouting.lean`),
and there through a definitional `show`. So redefining the body costs:

| Site | What changes |
| --- | --- |
| `routesOf` (`GeneralRouting.lean`) | body plus the "nothing sorts" paragraph of its docstring |
| `routesOf_split` | the `show` line, and `hInstances` re-keyed to `priorityOrderedInstances model` |
| `assembleGeneralPortReactions_instanceDeclarationOrder` | `hInstances` re-keyed the same way (§7.1) |

Three declarations, against six silently emptied. The two re-keyed hypotheses also get *stronger*
rather than weaker: an append split on `priorityOrderedInstances model` is a split of the list the
translator really walks, whereas a split of `model.instances` was only interesting while the two
coincided.

**What deliberately does *not* move.** `assembleGeneralProgram` in
`Relico/Translation/GeneralBasic.lean` builds the emitted
LF instance declarations from `model.instances`, and it keeps doing so. Instance declaration order has
no semantic role in Lingua Franca — §2.1 measured that *reaction* declaration order is the mechanism —
so sorting it would churn the emitted text and the printer's expected output to buy nothing, and would
cost `assembleGeneralProgram_instances` and `compileGeneralModel_instances`. The emitted program
therefore declares instances in source
order and connections in priority order, which is intentional and is why the ordering theorems are
stated about reactions rather than about the main block.

### 7.3 Why most existing route theorems transfer by permutation rather than re-proof

`priorityOrderedInstances model` is a **permutation** of `model.instances` — that is what a sort is —
and `routesOfInstances` maps each instance to its routes and concatenates. So the *multiset* of routes
is unchanged by the sort, and every property that depends only on the route **set** rather than its
order transfers through one permutation lemma instead of being re-proved. That covers the expensive
ones: endpoint uniqueness, site totality, port-name distinctness, and the setPort `Nodup`.

**The one real risk lives in the error case, and it is not hand-waveable.** `routesOfInstances` returns
`Except`, and if it short-circuits on the first failing instance then a permutation of its input can
change *which* instance fails first, and therefore which refusal cause the pipeline reports. A
translator whose refusal *reason* depends on a priority annotation would be a genuine defect, and it
would be exactly the class of silent behaviour change this project has been bitten by before.

Two mitigations, and measurement reverses the order an earlier revision of this section put them in.
The attractive one is **outcome-permutation-invariance**: for any permutation, `routesOfInstances`
returns `.ok` on one iff it returns `.ok` on the other. That revision called it "plausibly within reach"
on the strength of #47, but #47 established totality of the **self-send site machinery**, which is a
different subject, and the routing walk is not close to single-exit. `Relico/Translation/GeneralRouting.lean`
has **eight** `.error` origin sites — one in `routesOfInstances` itself, the unknown-class check; three
in `generalOutputPortEntryFor`; three in `generalRouteFor`; one in `generalPortPayloadFor` — and the walk
reaches all eight, through `outputPortEnvOf` and `routesOfEntries`. Invariance would therefore need
eight per-instance-independence arguments, not one.

So the realistic mitigation is the second: scope the ordering theorems to models where routing already
returns `.ok`, which every accepted model does by §8's acceptance chain. This is the same guard-relative
shape §6 chose for `PrioritiesDistinct`, and choosing it here for the same reason keeps the stage
consistent rather than opportunistic. §11 records permutation-invariance as an open question rather than
a planned lemma.

### 7.4 The three inert-priority theorems all stay green, and must not be "fixed"

`LF.GeneralReaction.priority` is never read by the printer (§2.3), so stage F realizes priority by list
order and never sets the field. Three landed theorems record that the field is unset, and all three
remain true and must be left alone:

- `assembleGeneralMessageReaction_priority` — `GeneralBasic.lean:1177`
- `assembleGeneralPortReaction_priority` — `GeneralBasic.lean:1280`
- `assembleGeneralStartupReaction_priority` — `GeneralBasic.lean:1592`

They are worth understanding as **alarms against a mechanism that would not have worked**, not as
debt. Wiring `priority := some n` would produce a program whose emitted text is byte-identical, so a
proof that the field is set would be a proof about nothing observable. `GeneralBasic.lean:1167`'s
docstring — *"Stage G cannot wire `DTR.GeneralMessageServer.priority` into the generated reaction
without…"* — is about that dead end and does not conflict with this stage, because stage F does not
use the field at all.

The corresponding docstrings say that this stage *"sorts nothing, emits source order, and drops
`DTR.GeneralMessageServer.priority` outright."* Those become false at the moment level 1 lands and are
part of the landing diff, not a follow-up. Enumerating them by hand found four — the module header,
`assembleGeneralMessageReaction`, `assembleGeneralMessageReactionAtSite`, and
`assembleGeneralPortReactions_instanceDeclarationOrder`; grepping for the *claim* rather than for the
stage found two more that assert route order is main-block order — `assembleGeneralPortReactions` and
`compileGeneralModel_connections` — which is the same lesson `docs/STAGE_E_FINDINGS.md` F46 records
about counts: search for the
proposition, not for the word.

Two neighbours are deliberately *not* in level 1's diff. `compileGeneralMessageServerReactions`
(*"Explicit recursion and no sort"*) is still true at level 1 and becomes false at level 2, so
it belongs to that commit. `routesOfInstances_append` (`Relico/Translation/GeneralRouting.lean`, *"no
interleaving, no sorting"*) stays true permanently, because the sort is in `routesOf` and not in the
recursion — it gains one clarifying clause rather than a correction.

A third group is a stage *attribution* rather than a false claim: six docstring lines written during
stage D say stage G permutes `messageReactions`. They sit in three different kinds of place, which is
why enumerating them by declaration alone missed some — one in `assembleGeneralReactor`'s docstring, two
in `compileGeneralReactiveClass_reactionNames`'s docstring, and three in the free-standing
`## Order preservation` section block that introduces the name theorems and belongs to no declaration at
all. §1.1 claims that work for stage F's level 2 instead. The two docstring homes are declarations level
2 has to re-key anyway, so the correction travels with commit 2.

## 8. The fixture stage F needs, and why the existing one cannot serve

### 8.1 `fan-in.rebeca` proves nothing about priority, by construction

The existing fan-in fixture has the right topology and the wrong ordering. Its main block:

```
@priority(1)  Sensor sensorFirst(gateway0):(10);
@priority(2)  Sensor sensorSecond(gateway0):(20);
@priority(3)  Sensor sensorThird(gateway0):(30);
              Gateway gateway0():();
```

Declaration order and priority order **coincide**, so the emitted reaction order is the same whether
stage F's sort runs or not, and a green gate would be evidence of nothing.
`docs/STAGE_E_DESIGN.md:740-745` predicted this in advance and said what to do about it:

> *"If the fixture declared them in any other order the emitted reaction order would change and no
> theorem in stage E would notice. Making the order follow priority is stage F's entire content; a
> fixture whose declaration order disagrees with its priority order is the fixture stage F needs and
> stage E should not pretend to satisfy."*

Incidentally the fixture does satisfy `ActorPrioritiesDistinct` — its priority list is
`[some 1, some 2, some 3, none]`, which is `Nodup` because only `gateway0` is unannotated — so it
would qualify for the guard-relative theorem if its order disagreed. It is the order, not the guard,
that disqualifies it.

### 8.2 The disagreeing fan-in (task #86)

A fan-in whose **declaration order is the reverse of its priority order**, so that the sort is the only
thing that could produce the expected output:

```
@priority(3)  Sensor sensorThird(gateway0):(30);
@priority(1)  Sensor sensorFirst(gateway0):(10);
@priority(2)  Sensor sensorSecond(gateway0):(20);
              Gateway gateway0():();
```

Expected emitted order for `Gateway.collect` is `collect_action`, then the port reactions for
`sensorFirst`, `sensorSecond`, `sensorThird` — **priority order, not the declared order**. Because the
declared order is a derangement of the priority order, the two orders differ in every position that
matters, and a sort that silently did nothing would fail the assertion rather than pass it.

It must also satisfy `ActorPrioritiesDistinct` so that it exercises the guard-relative theorem and not
only the unconditional one.

**And it must disagree at level 2 as well, or it tests only half the stage.** The same trap that
disqualifies `fan-in.rebeca` for level 1 disqualifies `priorities.rebeca` for level 2: its `Arbiter`
declares `urgent` (`@priority(1)`), then `routine` (`@priority(2)`), then `unranked` (unannotated), which
is *already* in priority order under the absence-last convention, so level 2's sort is a no-op on it.
Its main block has the same property — `@priority(3) arbiterHigh` then unannotated `arbiterPlain`.

So the new fixture's reactive class must also declare its message servers in an order that disagrees
with their priorities, for example `@priority(2)` before `@priority(1)` with the unannotated server
declared **first** rather than last. One fixture can carry both disagreements, and should, because a
single fixture that exercises both levels also witnesses §1.1's composition claim — that the two sorts
act on disjoint pairs and do not interfere.

**Task #86 is therefore two artefacts, not one, and F59 is why.** They carry different claims and
either can land without the other:

**(A) The hand-built model in the printer test main — the only artefact that witnesses the sort.** A
fourteenth `DTR.GeneralModel` literal in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`, carrying
the derangement above, asserting the emitted reaction order as text through `compileGeneralModel`
(precedent at `:1857`) or `routesOf` (`:2716`), and bumping `EXPECTED_PRINTER_ASSERTIONS` at
`frontend/check-general-lean.sh:245` with a twelfth entry added to the block-by-block provenance
comment above it. This needs no Java, no `artifact.zip` and no exporter run — Lean and a `lake build`.
It is also the first priority annotation of any kind in that file.

**(A) as landed, which differs from the sketch above in its names and in one forced design decision.**
The model is `priorityFanInModel`: a `Probe` class sending `ping(1)` to its known rebec `hub`, and a
`Collector` class with two message servers, `ping` (`@priority(2)`, one `int` parameter) and `drain`
(`@priority(1)`, parameterless). Its instances are declared `collector, alpha, beta, gamma` carrying
priorities `4, 3, 1, 2` and emit as `beta, gamma, alpha, collector` — a derangement with no fixed
point, so the expected text fails under declaration order *and* under any single transposition of it.
The expected reaction order is the literal

```
sample_reaction|ping_reaction,pingToHubFromBeta_reaction,pingToHubFromGamma_reaction,pingToHubFromAlpha_reaction,drain_reaction
```

and it is asserted **twice** — once against `compileGeneralModel`'s emitted reactors and once against
`generalReactionNamesOf` over `routesOf` — because comparing those two to *each other* is finding
**F60**, an assertion no permutation the sort can produce could fail. Comparing each to one shared
literal makes them independent, so either can fail alone and say which side moved. Four assertions in
all, the other two being source well-formedness and `ActorPrioritiesDistinct`, which §8.2 above
requires so that the guard-relative theorem is exercised and not only the unconditional one. The
receiver's two servers do carry the level-2 disagreement §8.2 asks for, but that is a **negative
control** rather than a second claim: `DTR.GeneralMessageServerPriority` has zero references under
`Relico/Translation/` and `Relico/Correctness/`, so level 2 is inert and `drain_reaction` is emitted
last, where its *declaration* puts it. Task #87 must move it to the front, which makes the literal
above a **prediction written before the behaviour exists** rather than text fitted to behaviour
afterwards.

Why the sketch's `Sensor`/`Gateway` names were not used: `ping` carries an `int` payload because a
port must carry one — `generalPortPayloadFor` (`Relico/Translation/GeneralRouting.lean:871`) refuses
arity zero, and that is the one refusal a well-formed model reaches. `sample` and `drain` stay
parameterless because nothing sends to them across a port, with `pollMessageServer` as the
already-asserted precedent for a parameterless server.

**(B) The `.rebeca` plus `.parser.json` pair — strictly weaker, and about the frontend.** It pins that
the exporter and the Lean decoder carry disagreeing priority annotations across the bridge intact. It
does **not** move any emitted text, because nothing translates it. Everything that travels with a new
general fixture travels with it: the list has been paid for twice already (#37 and #51), and
`relico-doc-count-invariants` records why it is easy to get wrong — the fixture file, its
`.parser.json`, the exporter run, the bridge assertions, `POSITIVE_COUNT` 10 → 11 and so the frontend
assertion total 24 → 25, and the **spelled-out English counts** in
`frontend/fixtures/general/README.md`, which is read by a Python test, so a missed count fails a gate
rather than merely reading wrong.

(A) landed first and **is not a transcription of (B)**, which is a change from what this section
originally said. (B) does not exist, and (A) was written against the Lean constructors directly with
its own class and instance names, so if (B) is ever added the two will be *independent* witnesses —
one that the frontend carries disagreeing annotations across the bridge, one that the translator sorts
by them — rather than one checking the other. That is the better arrangement, because nothing would
check a transcription anyway; see §8.3.

### 8.3 What the gates can and cannot show

`frontend/check-general-lean.sh` carries the structural evidence: the emitted reaction order, asserted
as text. **But it asserts it for a hand-built Lean model, never for a fixture** — and the difference is
finding **F59**, which had to be written because this section originally claimed the latter. The
printer runner is invoked at `:248-252` with **no arguments**; its models are thirteen hand-built
`DTR.GeneralModel` literals inside `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`. No committed
`.parser.json` is ever translated by any gate, and the general family has no expected LF text at all
(every `expected/lf-source` in the tree belongs to `tests/benchmarks/`).

So the model that witnesses the ordering is a **hand transcription** of the fixture, and *nothing
checks that the transcription is faithful*. That is a real gap and it is stated rather than closed: the
alternative would be a runner that decodes a `.parser.json` and prints it, which is a harness change
stage F does not need and should not smuggle in. What stage F must not do is describe the fixture as
the thing being asserted.

`frontend/check-general-lf-target.sh` can only show that the emitted program still **compiles and runs
under `lfc` 0.11.0**, because a generated program has no observable output (§2.4). It cannot witness the
order. Do not attempt to strengthen it; §2.4 explains why the exit-code-only check is forced, and the
mis-specified findings item that asked for the stronger thing was corrected by #80 rather than ticked.

The ordering claim is therefore carried by three independent things, and it is worth being explicit
that no one of them suffices: §2.1's measurement that declaration order decides in the target,
§8.2's assertion that the emitted declarations are in priority order, and §5's premise connecting DTR's
selection to LF's. The measurement is of hand-written LF, which is the correct instrument for a
target-language property, and the F58 lesson is that the instrument must be able to separate the causes
it is credited with separating. **F59 is that same lesson landing on this very section**: the instrument
named here could not have separated a priority-ordering sort from the identity, because it contains no
priority annotation anywhere. So the second of the three is **owed, not delivered** — it is task #86,
and until that lands the ordering claim rests on two legs rather than three.

## 9. Level 2 in detail: the blueprint ports, but not the way it is written

Level 2 orders whole per-server groups by message-server priority, and it has a proven blueprint —
`Relico/Correctness/PriorityOrder.lean`, 215 lines, four declarations. The temptation is to port it by
renaming `DTR.MessageServer` to `DTR.GeneralMessageServer`. That will not work, and the reason is
specific enough to be worth recording before anyone tries.

### 9.1 Why the blueprint's key does not exist in the general family

The blueprint's order relation is keyed on **action names**:

```
DTR.ServerNamePrecedesOrEqual left right messageServers ↔
  LF.ReactionActionPrecedesOrEqual (Translation.actionNameFor left) (Translation.actionNameFor right)
    (messageServers.map Translation.compileMessageReaction)
```

and its proof leans on `Translation.actionNameFor_injective` — one action per message server, name
determines server, order on names transports to order on servers.

In the general family that correspondence is gone, in two independent ways. First, after F56's repair
(#71) the action name is **site-keyed**: `generalActionNameFor (messageName : MsgName) (siteSuffix :
String)` (`Relico/Translation/NameGeneration.lean:71`), so one message server owns *several* action
names and there is no function from server to name to invert. Second, and more sharply, that function's
own docstring says the injectivity the blueprint depends on is **not available**: *"No injectivity in
both components is claimed, and none is proved… uniqueness of generated identifiers is decided on the
assembled program, by requiring `LF.GeneralReactor.declaredNames` to be `Nodup`"* (`:63-67`).

The obvious repair — key on `messageReactionNameFor` (`:83`), which *is* one per message server — fails
for a third reason that is documented at the definition site (`:96-99`): that name **can collide with a
port reaction's name, and this is explicitly not a defect**, because `messageReactionNameFor
⟨"reportToHubFromWorkerAlpha"⟩` and the port reaction for the input port `reportToHubFromWorkerAlpha`
are the same string and the latter is a legal Rebeca message name. *"Reaction names are not checked for
uniqueness anywhere."* An order statement keyed on a name that two different reactions can share is not
a statement about reaction order at all.

### 9.2 So level 2 is stated as an append split, not as a name order

Level 2 uses the **name-free, append-split** formulation that #65 already established for level 1 and
that `assembleGeneralPortReactions_append` already proves for the inner list: for every cut of
the sorted message-server list into `earlier ++ later`, the reactor's reaction list is the reactions
owed to `earlier` followed by the reactions owed to `later`. Quantifying over every cut is what "in this
order" means without a list-index API, and it is immune to name collisions because it never mentions a
name.

The walk site is the fifth argument, `reactiveClass.messageServers`, of the
`compileGeneralMessageServerReactions` call inside `compileGeneralReactiveClass`; it becomes
`GeneralMessageServerPriority.normalize reactiveClass.messageServers`. The grouping
that makes the split well defined is stage E's, deliberately: the module header's *"The replacements are
stated per group"* and the `## Order preservation` block's *"`messageServers.map messageReactionNameFor` —
one reaction per message server"*.

**The neighbouring walk is deliberately left alone,** and it is easy to mistake for this one.
`assembleGeneralReactor` also walks `reactiveClass.messageServers`, but to build
`logicalActions` via `compileGeneralMessageServerActionsOf` — action *declarations*, not
reactions. §2.1 measured that reaction declaration order is the mechanism that decides at one tag;
action declaration order decides nothing. Sorting that walk would therefore buy no semantics and would
cost `assembleGeneralReactor_logicalActions`, whose conclusion is keyed to
`reactiveClass.messageServers` directly. The emitted reactor consequently lists its logical actions in
source order and its message reactions in priority order, which is intended.

Level 2 does carry the same re-keying cost §7.2 measured for level 1, at six declarations rather than
three: `compileGeneralReactiveClass_ok`, `compileGeneralReactiveClass_error_messageServers`,
`compileGeneralModel_error_classes` (which reaches the walk through its own class recursion),
`compileGeneralReactiveClass_actionNames`, `compileGeneralReactiveClass_reactionNames`
and `exists_compileGeneralReactiveClass`. Each is the same mechanical substitution of
`reactiveClass.messageServers` by the normalized list, and the two `…Names` results conclude in `Nodup`,
which transfers through `GeneralPriority.map_normalize_nodup` rather than needing a new induction. This
cost is the reason §10 lands level 1 and level 2 as **separate commits**: it keeps a blind diff small
enough that a build failure localises.

Two things are inherited rather than rebuilt: the sort and its lemmas (§4.3), and the shape of the
statement (§7.1). What is *not* inherited is the blueprint's proof text. Budget level 2 as a
re-derivation of a 215-line file, not as a rename of it — and note that `GeneralBasic.lean:2024` records
that a theorem in this exact area was already restated once before (*"The previous form of this theorem
said `reactiveClass.messageServers.map…`"*), which is mild evidence that the area tolerates restatement.

## 10. The work plan, file by file

Level 1 and level 2 land as **separate commits**, in that order, for the reason §9.2 gives: each carries
a re-keying cost across several declarations, and a combined diff would make a build failure ambiguous
between them.

**New file, commit 1.** `Relico/DTR/GeneralPriority.lean` — the generic stable insertion sort of §4.3:
`PrecedesOrEqual`, `insert`, `normalize`, the `mem_insert_iff`/`mem_normalize_iff` pair, a permutation
lemma (`normalize xs ~ xs`), stability, and the two instantiations. Mirror
`Relico/DTR/MessageServerPriority.lean`'s declaration order so the two files read as siblings. Then, past
what the blueprint has, §4.5's sortedness development: the local `Sorted` predicate, `insert_sorted`,
`normalize_sorted`, and the three append-split consumers the correctness file spends
(`sorted_append_precedes`, `normalize_append_precedes`, `normalize_append_strict`, with
`nodup_append_ne` proved from first principles beside them). `normalize_sorted` is instantiated at
**both** element types even though only level 1 consumes the split form in commit 1, so that neither
level can land relying on an unproved sort.

**Modified, commit 1 (level 1).** `Relico/Translation/GeneralRouting.lean` — the
`Relico.DTR.GeneralPriority` import; `priorityOrderedInstances` and its permutation lemmas beside
`routesOf`; `routesOf`'s body and the *"Nothing sorts, here or anywhere below"* paragraph of its
docstring, which stage F falsifies; and `routesOf_split`, whose `show` and
`hInstances` are re-keyed (§7.2). Also `Relico/Translation/GeneralBasic.lean` for
`assembleGeneralPortReactions_instanceDeclarationOrder`'s hypothesis
and both sentences of its docstring (§7.1), plus the six docstrings §7.4 enumerates that assert this
stage sorts nothing or that route order is main-block order.

**Modified, commit 2 (level 2).** `Relico/Translation/GeneralBasic.lean` — the
`compileGeneralMessageServerReactions` call inside `compileGeneralReactiveClass` switched
to the normalized server list, and the six re-keyed declarations §9.2 enumerates. The
`compileGeneralMessageServerActionsOf` walk in `assembleGeneralReactor` is left alone,
deliberately and for a measured reason. Also the six stage-G attribution lines §7.4 locates.

**New file, commit 1.** `Relico/Correctness/GeneralPriorityOrder.lean` — level 1 in both of §6's forms
(`walkedInstances_precedes_of_split` unconditional, `walkedInstances_strict_of_split` guard-relative),
the one lemma that bridges `GeneralWellFormed`'s named guard to the sort's raw `Nodup` premise, and the
composition of the guard-relative form with
`assembleGeneralPortReactions_instanceDeclarationOrder` that states the emitted-reaction claim §III-D
actually asks for. Level 2's two forms are added to the same file in commit 2, deliberately not written
in commit 1 so that a build failure is localizable to one level.

**New file, commit 1.** `Relico/Tests/GeneralPriority.lean` — §4.5's value pins, at both element types:
the four-element normalization regression mirroring
`Relico/Tests/MessageServerPriority.lean:104`, a two-element tie-stability regression that swaps the tied
inputs, an all-unannotated identity regression for `P23`, and the two relation facts restated on fixtures
so that a rename of the `priority` field which missed `priorityOf` fails here.

**Unchanged, deliberately.** `Relico/DTR/GeneralWellFormed.lean` (§6), `Relico/LF/GeneralSyntax.lean` and
`Relico/LF/GeneralCppPrinter.lean` (§2.3 — the priority field is inert and stays unset),
`GeneralBasic.lean:2467`'s emitted instance list (§7.2), and `frontend/check-general-lf-target.sh`
(§8.3).

**The disagreeing fan-in.** Task #86's artefact (A): a twelfth assertion block in the printer test
main carrying four assertions, `EXPECTED_PRINTER_ASSERTIONS` 92 → **96**, and a twelfth entry in the
block-by-block provenance comment above that literal. Artefact (B), the `.rebeca` pair and the convoy
of counts in §8.2's list, is optional, strictly weaker, and unbuilt.

`Relico.lean` gains three imports, and the job total moves from 508 to **511**. All three new files land
in commit 1, so the total is already 511 there; commit 2 adds theorems to existing modules and does not
move it. An earlier revision of this section said 510 and named only two new files — §4.5 records the
measurement that added the third.

## 11. Falsifiable projections

Stage E's §11 recorded projections and seven were later falsified, which made it the most useful section
in that document. The same is attempted here. Each of these is stated so that a specific observation
refutes it.

**Outcomes as of the commit-1 gate run, 2026-08-23.** **Six** of the nine below have measured results
and all six held: F-1 (the generic sort's lemmas went through with the same `by_cases`/`simp` shape, so
§4.3's monomorphic fallback was never taken), F-2 (shipped with the routing-succeeded hypothesis as
projected), F-3 (`assembleGeneralPortReactions_instanceDeclarationOrder` needed no restatement — re-keying
its walk dated its docstring and nothing more), F-4 (no `.priority` obligation appeared, all three
`_priority` theorems green with no edit), F-5, and F-7 (`wellFormed` still five clauses; the distinctness
premise stayed a hypothesis). F-6 is unresolved because level 2 has not been written, and F-8 is
untestable until it is.

**F-9 is the ninth and it is scored separately, because the run could not bear on it.** Its claim is
true and was pre-checked by inspection, but it was written naming an artefact that does not exist — "the
fixture whose expected LF text changes" — and no gate translates a fixture at all. Finding **F59**
measured that, quotes the original wording so the score stays auditable, and explains why the green
92 printer assertions are a witness for *stability* rather than for ordering. **The headline and
refutation condition of F-9 below were rewritten after the run, and that is the only projection text in
this document ever altered post-hoc.** It is recorded here rather than done quietly because the rule is
that projections are never adjusted to fit results: what changed is a category error in what F-9 named
as its instrument, not the claim it makes or whether the claim held. No figure was touched — the
numbers below are as written before the run.

**F-1. The generic sort costs less than two monomorphic copies.** Refuted if `GeneralPriority.lean`'s
lemmas do not go through with the same `by_cases`/`simp` shape as
`MessageServerPriority.lean`, and the fallback of §4.3 has to be taken.

**F-2. Stage F ships the ordering theorems with a routing-succeeded hypothesis, not a
permutation-invariance lemma.** An earlier revision projected the opposite — that `routesOfInstances`
would be proved outcome-permutation-invariant — but §7.3's eight-origin measurement makes that a
multi-argument obligation rather than a corollary of #47, so the projection is inverted here to the
outcome now expected. Refuted if invariance turns out cheap enough to prove inside stage F after all, or
if a permutation is found that changes `.ok` into `.error` and thereby makes the hypothesis
non-vacuous in a way the guard does not already cover.

**F-3. `assembleGeneralPortReactions_instanceDeclarationOrder` needs no restatement.** Refuted if
switching the walk to `priorityOrderedInstances` breaks the theorem rather than merely dating its
docstring — for instance if `routesOf` turns out to be used in the reaction path in a way §7.2 has not
found.

**F-4. All three `_priority` theorems stay green with no edit.** Refuted by any `.priority` obligation
appearing in the new proofs.

**F-5. The job total lands at exactly 511.** Revised from 510 while the plan was still unbuilt, and the
reason is recorded rather than quietly absorbed: §4.5's measurement added a third new file
(`Relico/Tests/GeneralPriority.lean`) to §10. The revision was a plan change made before any run, not an
adjusted prediction. Refuted by any other number; if it is 510, the value pins were folded into an
existing test module and the plan drifted; if it is 509, one of the two Lean modules was folded away as
well. **MEASURED 2026-08-23: `Build completed successfully (511 jobs)`, exactly the revised figure.** The
three new modules built as jobs 505, 506 and 509, and the general family shows `Built` while the
multi-store family shows `Replayed`, so nothing outside the general pipeline was disturbed.

**F-6. No new `P` number is owed.** Refuted if implementing the sort surfaces a paper claim not already
covered by P1, P4, P5 or P23.

**F-7. `wellFormed` stays at five clauses.** Refuted if the guard-relative theorems turn out to need a
hypothesis that is not expressible as `PrioritiesDistinct`, forcing a sixth clause after all — which
would also shrink the accepted fragment and owe a fragment-restriction note.

**F-8. Level 2 is a re-derivation, not a rename.** Refuted — happily — if `PriorityOrder.lean` ports by
substitution after all, which would mean §9.1's three obstacles are avoidable.

**F-9. No existing positive fixture's declared order disagrees with its priority order, at either
level.** **Pre-checked by inspection on 2026-08-23, and it held**, which is why it is stated as a
projection rather than left to gate time. Every positive general fixture carrying priority annotations
was read: `fan-in.rebeca`'s instances are declared `1, 2, 3` then unannotated (§8.1);
`priorities.rebeca`'s message servers are declared `1, 2, none` and its instances `3, none`;
`two-classes.rebeca` annotates one server of two. All are already in priority order under the
absence-last convention, so both sorts are no-ops on the entire existing corpus.

**Refuted by reading a fixture whose annotations disagree** — not by a gate. Finding **F59** measured
why: no gate carries a `.parser.json` through translation, so no fixture *has* an emitted order for a
run to move. The residual risk noted when this projection was written — that reading a `.rebeca` file
is not the same as reading what the exporter produced into its `.parser.json` — is therefore **still
open**, and no gate result can close it. What would close it is reading the priority fields of the
committed `.parser.json` documents directly.

**MEASURED at gate time, 2026-08-23, and what the run does and does not show.** With `routesOf`
walking `priorityOrderedInstances`, all **92** printer assertions passed unchanged, the **24**
frontend assertions passed, and `GENERAL_LF_TARGET_OK` held with real `lfc` 0.11.0 accepting the
routed two-class program and running it to a clean exit. **This is not confirmation of an ordering
claim, and F59 is the entry that establishes why.** `grep -c priority` over the 5124 lines of
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean` returns **zero**: every hand-built instance takes
the default `priority := none`, every pair is tied under the reflexive `PriorityPrecedesOrEqual`, and
`normalize` is the identity on all-tied input for *any* stable sort. The 92 assertions could not have
moved. The 24 frontend assertions decode fixtures and never translate them, so they carry no ordering
information either.

**What the run does establish is worth stating positively:** all-tied input is exactly the case §4.5
argues sortedness cannot see, so 92 unchanged assertions are an independent witness that `normalize`
is **stable**. That is the property the theorems structurally cannot pin, and it is a real result —
just not the one the projection was about.

**Consequence, and it is the reason task #86 is not optional but had to be re-scoped.** The level-1
sort is observationally **inert** on every fixture the repository has, established by the inspection
above rather than by the run. Nothing in the corpus distinguishes it from the identity function. The
only artefacts that do are the seven `rfl` pins in `Relico/Tests/GeneralPriority.lean` and the
sortedness theorems of §4.5 — and the pins are `theorem`s closed by `rfl`, so they are discharged at
elaboration and never appear in the 24 or 92 counts at all. It follows that **the 92 printer
assertions must not be described anywhere as covering stage F's ordering claim**, and that the
corpus-level evidence for level 1 is currently zero. This is §4.5's measurement restated at corpus
scale, and it is the same shape as the earlier finding that `normalize := id` would break one
regression test and no theorems.
