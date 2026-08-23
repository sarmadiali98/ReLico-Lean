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

It is also not permanently blind to priority. Level 2's sort will enter on the constructor side only,
inside `compileGeneralReactiveClass`, while `generalReactionNamesOf` still receives
`reactiveClass.messageServers` unsorted — so after task **#87** a model with message-server
priorities *would* make the two sides disagree. `routedModel` carries no priority annotation of any
kind, so that sensitivity is unreachable there, and the model is deliberately left unannotated: its
job is the drift check, and the fan-in block below it is the ordering instrument.

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

