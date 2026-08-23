# Stage F findings — F59 onward

**Why this file exists.**
Stage F orders the emitted reactions by priority: level 1 orders the port reactions inside one
message server's group by the priority of the *sending actor*, level 2 orders the groups by the
priority of the *receiving message server*. Its findings start at **F59**, continuing the single `F`
series that [`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md) opened at F1–F20,
[`STAGE_D_FINDINGS.md`](STAGE_D_FINDINGS.md) carried to F21–F33, and
[`STAGE_E_FINDINGS.md`](STAGE_E_FINDINGS.md) carried to F34–F58.

This file exists rather than an eleventh section of [`STAGE_E_FINDINGS.md`](STAGE_E_FINDINGS.md)
because **F54** was the cost of an entry that existed but was invisible from where a reader looks. A
stage F finding filed under a heading that says "Stage E" is that defect by construction. The counts in
the stage E file say **F34–F58** and they stay true; nothing here renumbers them, and
[`STAGE_D_DESIGN.md`](STAGE_D_DESIGN.md) §10.1 carries the list of all four homes of the `F` series.

**The provenance rule, unchanged from stage D.** Every entry carries one of four grades, and where a
single entry mixes them the sub-claims are graded separately rather than the whole taking the
weakest label:

* **measured** — a named run produced the result, identified well enough to repeat.
* **read** — a reading of source at a cited `path:line`, including absence established by a
  described search.
* **decided** — a choice between recorded alternatives, with the alternative stated.
* **inferred** — argued, not run. No soundness claim rests on one, and an inferred finding either
  names the experiment that would settle it or does not belong here.

`docs/STAGE_F_DESIGN.md` owns what stage F *does* and why. This file owns only what stage F *found
wrong*.

---

## F59 — the ordering evidence is credited to an instrument that cannot produce it, and the instrument that could has no priority in it

**Grade: measured** for the three instrument facts below, each a grep or an invocation site;
**read** for the consequence that the assertions could not have moved, which follows from the
definitions rather than from a run, and whose settling experiment is named at the end.

**Method.** The three Lean mains named by `frontend/check-general-lean.sh` were located at `:37`,
`:38` and `:39` and their invocation sites read; `grep -c priority` was run over
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean`; every `expected/lf-source` directory in the
tree was enumerated with `find`, and `find frontend -name '*.lf'` was run separately.

### The three measured facts

**1. `PRINTER_TEST_MAIN` is invoked with no arguments.** At `frontend/check-general-lean.sh:248-252`
it is run as `lake env lean --run "$PRINTER_TEST_MAIN"` and nothing follows. The other two mains do
receive fixture paths — `BRIDGE_MAIN` is called once per document in the loop at `:67-80`, and
`TEST_MAIN` is handed `"$FIXTURE_DIRECTORY"` at `:90-95`. So the fixture corpus reaches the
**decoder** and the accept/reject expectations, and stops there.

This does not make the printer main a weak instrument. It *is* the translator's instrument: it calls
`Translation.compileGeneralModel` at `:1857` and `Translation.routesOf` at `:2716`, over **thirteen**
hand-built `DTR.GeneralModel` literals, at `:1476`, `:1512`, `:1575`, `:1703`, `:2378`, `:2445`,
`:2470`, `:2508`, `:2534`, `:2566`, `:2591`, `:3041` and `:4258`. What it is not is *fixture-driven*. A model in that file is a
**hand transcription** of a fixture, and nothing mechanically ties the transcription to the
`.rebeca`/`.parser.json` pair it was copied from. `frontend/check-general-lf-target.sh` is the same
shape: four hand-built programs, named at `:103-106`.

**2. The general family has no expected LF text at all.** Every `expected/lf-source` directory in
the repository belongs to `tests/benchmarks/` — the multi-store families `core--`,
`finite-store--`, `bound-payload--` and `global-multi-actor-payload--`. `find frontend -name '*.lf'`
returns nothing. There is no artefact of the form "the LF text expected for fixture *N*".

**3. `grep -c priority` over `GeneralLfPrinterTestMain.lean` returns `0`,** across all 5124 lines.
Both `DTR.GeneralActorInstance` (`Relico/DTR/GeneralSyntax.lean:409`) and `DTR.GeneralMessageServer`
(`:339`) default `priority := none`, so **every instance and every message server in every
hand-built model is unannotated.**

### The two defects

**Every `docs/STAGE_F_DESIGN.md` line number below refers to commit `f5d108a`**, the commit in which the
defective text was live. The commit that records this finding corrected that text in the same landing, so
these numbers do not resolve in the working file and were never meant to. Each quotation was checked
character-for-character against `git show f5d108a:docs/STAGE_F_DESIGN.md` — necessary because two of them
wrap across a line break and so cannot be located by grepping the quoted phrase.

**Defect one — attribution to an instrument that cannot reach the code.** `docs/STAGE_F_DESIGN.md`
§8.3 at `:683-684` reads:

> *"`frontend/check-general-lean.sh` carries the structural evidence: the emitted reaction order for
> the new fixture, asserted as text. That is the real gate for this stage."*

No fixture has an emitted reaction order that any gate can assert, by fact 1. What the gate can
assert is the emitted order of a hand-built Lean model, and the faithfulness of that model to the
fixture is unchecked. §11's projection **F-9** at `:888` carries the same presupposition in its
headline — *"the new fixture is the only fixture whose **expected LF text** changes"* — which by fact
2 names an artefact that does not exist. §8.2's travelling-costs list at `:676` is the one place that
gets it right, listing "the printer test main's expected LF text" as a *separate* item from the
fixture and its `.parser.json`; it is right without saying why, which is why the two sentences above
could contradict it unnoticed.

**This is F47 read from the other side.** F47 established that a `lean-reject` document can never
exercise a translation diagnostic, because such a document is one the frontend *refuses* and so never
reaches a translation function. That is the negative-fixture version. The positive-fixture version —
that an **accepted** document never reaches the translator either, because no runner wires that path
— was never recorded, and it is the one stage F depends on.

**Defect two — a green gate credited with confirming an ordering projection it could not fail.**
§11's measured paragraph at `:898-901` reads the unchanged 92 printer assertions as confirming F-9,
and the consequence paragraph at `:903-911` reads them as showing the level-1 sort is inert *"on
every fixture the repository has"*. Both over-read the run, for two independent reasons:

- By fact 1 no fixture is translated, so the run carries **no information about fixtures**, inert or
  otherwise.
- By fact 3 every hand-built instance is unannotated, so every pair is **tied** under
  `PriorityPrecedesOrEqual`, which is reflexive (`Relico/DTR/GeneralPriority.lean:55`, with
  `priorityPrecedesOrEqual_total` at `:171`). `insert` (`:266`) tests that reflexive relation, so on
  all-tied input it never displaces an element and `normalize` (`:299`) is the identity. **The 92
  assertions could not have moved, for any stable sort.** A green gate is therefore not evidence
  about ordering.

The inertness claim is nonetheless **true** — but it is established by F-9's *first* paragraph,
which read every positive `.rebeca` by inspection and found `fan-in` declaring `1, 2, 3` then
unannotated, `priorities` declaring `1, 2, none` and `3, none`, and `two-classes` annotating one
server of two, all already sorted under the absence-last convention. Inspection is the instrument
that supports the claim; the gate run is not. Crediting it to the run is precisely the **F58**
defect, and the section that commits it is the section that states the lesson: §8.3 at `:695-696`
reads *"the instrument must be able to separate the causes it is credited with separating"*, eleven
lines below the defective sentence quoted above.

### What the green run does establish, which is worth keeping rather than deleting

All-tied input is exactly the case §4.5 argues sortedness cannot see. `Sorted` is stated against the
**reflexive** `PrecedesOrEqual`, so for a tied pair *both* orders satisfy it, and a `normalize` that
reversed ties would satisfy `normalize_sorted` and `normalize_perm` together while contradicting
decision `0041`. That is the gap §4.5 gives as the reason the `rfl` pins are owed alongside the
theorems.

So the 92 unchanged assertions are a real, independent witness — over thirteen hand-built model
literals, and four programs a C++ toolchain compiles and runs — that `normalize` is **stable**: the
identity on all-tied input. That is the one property the sortedness development structurally cannot
pin. The correct sentence is *"the printer gate pins stability on all-tied input"*, and never *"the
printer gate confirms priority ordering"*.

### Why it is load-bearing rather than cosmetic

It changes what stage F must build. Task **#86** was scoped as "the fan-in fixture whose declaration
order disagrees with priority order", and by facts 1 and 2 a `.rebeca` plus `.parser.json` pair
**cannot** deliver that: it adds one decoder assertion and moves no emitted text, because nothing
translates it. The gate-visible ordering evidence has to come from a hand-built model in the printer
test main carrying disagreeing priorities — which needs no Java, no `artifact.zip` and no exporter
run, and which is why the corrected task is cheaper as well as sound.

It also protects a claim the paper would otherwise inherit. "Ninety-two printer assertions pin the
emitted reaction order under actor priority" is a sentence this repository's own gate output invites
and that fact 3 refutes.

### The experiment that settles the read sub-claim

Substitute `normalize := id` in the general actor namespace and re-run
`frontend/check-general-lean.sh`. The prediction is **92 printer assertions still pass and
`GENERAL_LEAN_GATE_OK` still holds**, with only `Relico/Tests/GeneralPriority.lean`'s seven `rfl`
pins failing — and those fail at *elaboration*, so the observable form is a red `lake build` rather
than a failed assertion count. If instead a printer assertion fails, fact 3 is wrong and this entry
is refuted. The multi-store family's equivalent substitution has already been run, breaking one
regression test and no theorems, so the shape of the answer is known.

---

## F60 — the one assertion that names reaction order compares two values that both move with the sort, and its own docstring called that a virtue

**Grade: read** for the two quotations and for the shape of the code they describe, each at a cited
`path:line`; **inferred** for the consequence that no permutation the sort can produce could fail
the assertion, which follows from that shape rather than from a run, and whose settling experiment is
named at the end.

**Method.** `Translation.routesOf` was read at its declaration; the two values
`routedEmittedReactionOrder` and `routedSpecifiedReactionOrder` in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean` were read together with the assertion that
compares them and with the comment and docstring attached to each; the priority-annotation count
over that file is F59's fact 3.

**Line numbers and quotations below refer to commit `38bfc9f`**, the last commit in which the
defective text was live. The commit that records this finding rewrites both passages in the same
landing, so the quoted strings do not appear in the working file and are not meant to. Both were
checked character-for-character against `git show 38bfc9f:frontend/lean-bridge/GeneralLfPrinterTestMain.lean` —
necessary because a grep for either phrase fails on the line breaks inside it, which is the trap F51
recorded.

Re-checking this entry has a second trap on top of that one. Site two's rewrite kept the sentence's
opening and replaced only its ending, so a prefix short enough to survive the line wrapping is also
short enough to survive the rewrite, and grepping one finds live text that looks like the defect. The
check has to reach the clause that was actually cut — `correctly, because it is about *order*` — and
not merely the words in front of it.

### The mechanism, read

`Translation.routesOf` (`Relico/Translation/GeneralRouting.lean:1582`) is exactly

```
routesOfInstances model (priorityOrderedInstances model)
```

so **level 1's sort is inside `routesOf`**, applied before any caller sees a route. That is the
design working as intended — one entry point, `priorityOrderedInstances` at `:1496` — and it is also
what makes the assertion below unfalsifiable. `routedEmittedReactionOrder` reads the reaction names
out of `Translation.compileGeneralModel routedModel`, which calls `routesOf` internally;
`routedSpecifiedReactionOrder` calls `Translation.routesOf routedModel` itself and maps
`generalReactionNamesOf` over the classes. **Neither side is a literal, and both are downstream of
the sort.** Any permutation the sort produces moves the two together, and
`ROUTED_REACTION_ORDER_MATCHES_SPECIFICATION` stays green. It is an *agreement* claim between two
pieces of code, not an *ordering* claim about either.

### Site one — a comment that promotes the agreement claim to the ordering claim

The comment on the assertion, at `:4016-4020` with the quoted sentence occupying `:4018-4020`,
read:

> *"Reaction declaration order decides same-tag order in `lfc`, so these two agreeing is the
> executable half of the ordering claim the theorems make."*

Both halves of the sentence are true in isolation and the inference between them is not. Declaration
order does decide same-tag order in `lfc` — that is #80's measurement, and it is why reaction order
is worth asserting at all. But "these two agreeing" is not the executable half of anything about
order, because the two cannot disagree about order. The sentence reads as though the assertion were
the gate-visible counterpart of `portReactions_realizeActorPriority`, and stage F's design leaned on
exactly that reading.

### Site two — a docstring that states the same false claim as a deliberate economy, which is worse

`routedSpecifiedReactionOrder`'s docstring — `/--` at `:2696`, `-/` at `:2711`, the declaration
itself at `:2712` — read, at `:2704-2705`:

> *"Nothing here is spelled as a literal, so a rename in `NameGeneration.lean` moves both sides at
> once and this assertion stays silent — correctly, because it is about *order*."*

This is the more instructive of the two. It notices the exact property that defeats the assertion —
both sides move together, nothing is pinned to a literal — and then files it under the wrong
consequence. Order is precisely what the comparison cannot see; a rename is one of the few things it
*can* see going wrong, and only when a rename hits one side and not the other. The clause "correctly,
because it is about order" inverts the reason. A false claim defended as a design choice survives
review better than a bare false claim, which is why this site is recorded ahead of the first.

### What the assertion genuinely pins, which is why it is repaired rather than deleted

`generalReactionNamesOf` is the function §7.3's two replacement theorems are stated against;
`compileGeneralMessageServerReactionGroup` is what actually builds the reactions. Nothing else in the
repository holds those two together, and they are edited for different reasons — the first when a
theorem's statement changes, the second when emission changes. The assertion catches them **drifting
apart**. That is a real obligation, and the comment that replaces the sentence quoted above says so
in those terms instead: an agreement claim, named as one, with a pointer to where the ordering claim
is actually made.

It is also not permanently blind to priority. Level 2's sort entered on the constructor side only,
inside `compileGeneralReactiveClass`, and this assertion still hands `generalReactionNamesOf`
`reactiveClass.messageServers` unsorted (`frontend/lean-bridge/GeneralLfPrinterTestMain.lean:2737`)
— so a model with message-server priorities put through *this* assertion would make the two sides
disagree. `routedModel` carries no priority annotation of any kind, so that sensitivity is
unreachable there, and the model is deliberately left unannotated: its job is the drift check, and
the fan-in block below it is the ordering instrument.

One consequence of task **#87** that this paragraph did not anticipate, recorded here because it
weakens the sentence above rather than confirming it: re-keying
`compileGeneralReactiveClass_reactionNames` moved the *theorem's* right-hand side onto
`generalPriorityOrderedMessageServers reactiveClass`, so this assertion is no longer the runnable
form of it. The fan-in assertion below was updated to match and this one was not, which means the
drift check now pins a value **no theorem mentions** — precisely the option
`priorityFanInSpecifiedReactionOrder`'s docstring records as considered and rejected. It is harmless
at `routedModel`, because with no annotations the sort is the identity and both arguments are the
same list. But the reason it is harmless is the same reason this finding was filed, so the promised
sensitivity now costs an annotation *and* a decision about which value the assertion should mirror.

### Why it is load-bearing rather than cosmetic

F59 established that the ninety-two printer assertions could not have moved for any stable sort,
because nothing in the file carries a priority. F60 is the reason that gap could not be closed by
reaching for the assertion that already had "reaction order" in its name: the one instrument that
looked like it measured ordering does not, and would not have measured it even after priorities were
added to its model. Together they say that **stage F had no gate-visible ordering evidence at all**,
and they fix the shape of the instrument that supplies it — the expected order must be a **literal**,
and the constructor's answer and the specification function's answer must each be compared against
that literal independently, so that the two assertions can fail alone rather than only together.
That is why `PRIORITY_FAN_IN_EMITTED_REACTION_ORDER` and
`PRIORITY_FAN_IN_SPECIFIED_REACTION_ORDER` are two assertions against one string rather than one
assertion comparing two values.

**This is the third member of a defect class this repository now has a name for.** F47: a
`lean-reject` document can never exercise a translation diagnostic, because the frontend refuses it
first. F59: an accepted document never reaches the translator either, because no runner wires that
path. F60: an assertion whose two sides share the code under test. In each case a green run was
credited with excluding a failure it could not have observed, and in each case the defect was found
by reading the instrument rather than by any run failing.

### The experiment that settles the inferred sub-claim

Add disagreeing actor priorities to `routedModel` — leaving its two order values and their assertion
untouched — and re-run `frontend/check-general-lean.sh`. The prediction is that
`ROUTED_REACTION_ORDER_MATCHES_SPECIFICATION` **still passes**, while the emitted port-reaction
order visible in the other routed assertions changes. If instead it fails, the two sides are not both
downstream of the sort and this entry is refuted. The experiment is named rather than run because
running it means annotating a model whose purpose is to be the unannotated drift check; the fan-in
block gets the annotations instead, and its `PRIORITY_FAN_IN_EMITTED_REACTION_ORDER` is the same
observation made against a literal, where it can fail.

---

## F61 — a documented fail-fast policy silently voided a diagnostic promise made elsewhere, at the exact assertion pair built to carry stage F's evidence

**Grade: measured** for the run and its three counts, which are repeatable by the command named
below; **read** for the mechanism, at four cited `path:line`s.

**Method.** `frontend/check-general-lean.sh` was run on a working tree with level 2 wired (task
**#94**) and the expected literal **deliberately left unedited**, so that the first exercise of the
new sort would be a prediction test rather than a confirmation of text already fitted to it. The log
was then searched for `^PASS_` and for every occurrence of the string `SPECIFIED`. `testFailure`,
`expectString`, `expectRendered` and `runGeneralLfPrinterTests` were read afterwards, to explain
what the search found.

### The run

`EXIT=1`, and **118** `PASS_` lines where green is 120 — 24 frontend plus 96 printer — so **94 of
the 96 printer assertions**. Exactly one diagnostic, reproduced here in full:

```
PRIORITY_FAN_IN_EMITTED_REACTION_ORDER: expected
sample_reaction|ping_reaction,pingToHubFromBeta_reaction,pingToHubFromGamma_reaction,pingToHubFromAlpha_reaction,drain_reaction
but got
sample_reaction|drain_reaction,ping_reaction,pingToHubFromBeta_reaction,pingToHubFromGamma_reaction,pingToHubFromAlpha_reaction
```

`grep -n SPECIFIED` over all **4380** log lines returns **nothing**.
`PRIORITY_FAN_IN_SPECIFIED_REACTION_ORDER` printed neither a `PASS_` line nor a failure of its own.
Two assertions are missing from the count and the diagnostic accounts for only one of them.

The `but got` string above is also the finding this run was for, and it is recorded here because the
two arrived together: it is the repository's first gate-visible evidence of level 2 ordering, it
matches the permutation predicted in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean` before the
behaviour existed, and level 1's within-group 3-cycle `Beta, Gamma, Alpha` is visibly untouched
beside it. **The instrument produced its intended measurement and a defect in itself on the same
run, at the first moment it was used.**

### The mechanism, read

`testFailure` (`:237-243`) is `throw (IO.userError message)`. `expectString` (`:253-265`) calls it
on mismatch, and `expectRendered` (`:294-310`) delegates to `expectString`. `runGeneralLfPrinterTests`
(`:5490`) is a **single** `try` over all twelve assertion blocks with a **single** `catch` (`:5523`)
that prints the exception and returns 1. So the first throw anywhere in the suite abandons every
assertion after it — not merely the rest of its own block.

The fan-in block is the twelfth and last, and its four calls are sequenced
`SOURCE_WELLFORMED`, `ACTOR_PRIORITIES_DISTINCT`, `EMITTED_REACTION_ORDER`,
`SPECIFIED_REACTION_ORDER`. The first two passed — they are the last two `PASS_` lines in the log —
the third threw, and the fourth never ran. 96 − 2 = 94, which is the measured count exactly.

### The promise this refutes

**The quotation below refers to commit `6ebcd11`**, the last commit in which the defective sentence
was live. The commit that records this finding rewrites that docstring in the same landing, so the
quoted text does not appear in the working file and is not meant to. It was transcribed from the
working tree at `:5247-5250` immediately before the edit that replaced it, and re-checked against
`git show 6ebcd11:frontend/lean-bridge/GeneralLfPrinterTestMain.lean` piped through
`tr '\n' ' ' | tr -s ' '`, which returns the sentence — the flattening is necessary because it wraps
across a line break, which is the trap **F51** recorded. The cites in the section above are to the
**working** file, where the mechanism they describe is unchanged by this landing.

`priorityFanInSpecifiedReactionOrder`'s docstring, written under task #86 in anticipation of #87,
read:

> *"level 2's sort enters at the reaction-group walk on the *constructor* side, while this function
> still receives `reactiveClass.messageServers` unsorted, so if #87 moves only one of them these two
> assertions will disagree and say which one moved."*

The two **values** really would have disagreed in that run — that half of the sentence is right, and
the experiment named below says exactly how. What cannot happen is the *reporting*. The pair cannot
both be observed in one run, so the run cannot "say which one moved", and the promise holds in
exactly **one** of its two directions. The asymmetry is fixed by the order of the two calls:

* A move in the **specification function** alone is fully diagnosed. `EMITTED` is asserted first and
  passes, `SPECIFIED` then runs and fails, and the pair reads as one `PASS_` line and one failure —
  which is the two-sided reading the docstring promises.
* A move in the **constructor** alone is only half diagnosed. `EMITTED` throws, and its label does
  name the side that moved, so the run is not silent. But `SPECIFIED` never executes, so the log
  cannot distinguish *the constructor alone moved* from *both sides moved*: those two situations
  produce byte-identical output. The pair collapses to one bit, and the bit that goes missing is
  exactly the one that says whether the specification function still needs changing too.

The second is the direction task #87 moves in, and it is the direction the docstring was written
for. The ambiguity was not hypothetical. Mid-task, with `EMITTED` failing and `SPECIFIED` absent,
the gate could not answer the one question the pair exists to answer — whether
`priorityFanInSpecifiedReactionOrder` had to be re-pointed at the sorted list as well. That question
was settled by reading the code, which is the instrument the pair was built to replace.

### The reporting policy is not the defect, and this is the part worth keeping

`testFailure`'s own docstring at `:231-235` states the policy deliberately and gives its reason:

> *"The runner catches this once and returns a nonzero status, so the first failing assertion is the
> one reported. A later assertion cannot mask an earlier one."*

That is a defensible trade and it is honestly documented at the site that implements it. Converting
eight assertion helpers and 96 call sites to fail-slow, so that one diagnostic becomes available in
one direction it currently is not, would spend a global architecture change on a local convenience —
and it would give up the property the docstring names, which is the property that makes a single
reported failure trustworthy. **So the repair is to the claim, not to the runner.** The docstring
that over-promised now states the asymmetry, and no code changed on account of this finding.

This distinguishes F61 from its three siblings. F47, F59 and F60 each found an instrument that
**could not observe** what it was credited with observing, and each was repaired by changing the
instrument. F61 found an instrument that observes correctly and a *second document* that described
its reporting behaviour wrongly. The defect is entirely in the description, which is why it is the
cheapest of the four to fix and the easiest of the four to have missed: nothing was broken, and a
green run would never have revealed it. **It took a failing run at a predicted failure to expose a
false sentence about what failing runs report.**

### The trap in reading the log, which cost a wrong first reading

In the log the diagnostic sits at line 4281, *ahead of* all 94 `PASS_` lines, which invites the
reading that the block reports failures before successes. It does not, and the ordering is not a
stdio buffering accident either — it is forced by the gate script.
`frontend/check-general-lean.sh:277-281` captures the printer run's **stdout** into
`PRINTER_OUTPUT="$( … )"` and re-prints it afterwards at `:285`, while **stderr** is never
redirected and so reaches the log the instant it is written. `IO.println` writes the `PASS_` lines
to stdout; the `catch` at `:5523` uses `IO.eprintln`. **A printer failure diagnostic therefore
always precedes every `PASS_` line in a gate log, by construction.** Line order in that log is not
execution order across the two streams, and any finding that reasons from it must say which stream
each line came from.

### Why it is load-bearing rather than cosmetic

F60 prescribed the shape of stage F's ordering instrument: two assertions against one literal, so
that they "can fail alone rather than only together". F61 measures the limit of what that shape
delivers under this suite's reporting policy — each can fail alone, but only one failure per run is
ever *seen*, and which one is decided by call order rather than by which side is wrong. A reader who
takes the pair as a two-bit diagnostic will over-read a single reported failure as a statement about
both sides. That is the same mistake F59 recorded against the ninety-two unchanged assertions,
committed against a failing run instead of a passing one.

### What the repair run added, and the one question that stays open

The landing that records this finding was re-gated: `EXIT=0`, **120** `PASS_` lines, and
`grep -n SPECIFIED` over the log now returns exactly one line,
`PASS_PRIORITY_FAN_IN_SPECIFIED_REACTION_ORDER`. Both order assertions run, and both agree with the
drain-first literal. That is an addition rather than bookkeeping: it measures that
`generalReactionNamesOf` applied to `generalPriorityOrderedMessageServers reactiveClass` yields the
same five names in the same order that `compileGeneralModel` emits, which is the agreement the
re-keyed `compileGeneralReactiveClass_reactionNames` asserts — now checked on a concrete model
rather than only proved.

What neither run establishes is what `SPECIFIED` would have *reported* in the failing run, while it
still walked the **unsorted** list. It is not in the log, and it is not recoverable by re-running,
because the same landing that moves the literal also points the specification value at the sorted
list; after that the assertion passes, and the question becomes unobservable for a second and
different reason. To answer it: revert only the expected literal to declaration order, revert only
the argument back to `reactiveClass.messageServers`, and comment out the `EMITTED` call so that
`SPECIFIED` runs first.

**The prediction is that it passes**, and the reason is worth stating because it is the sharpest form
of the whole finding. An unsorted server walk reproduces *declaration* order at the group level,
while the port reactions inside `ping`'s group still come from `routes` and so are already level-1
sorted — which is precisely the old literal, token for token. So in the failing run the two values
did disagree, the disagreement was exactly the one #86 anticipated, and the pair still could not
report it: the side that would have passed was the side that never ran. A two-bit diagnostic whose
bits are read in a fixed order can only ever return the first bit.


