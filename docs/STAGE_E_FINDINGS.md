# Stage E findings — F34 through F56

**Why this file exists.**
Stage E added external sends, ports and connections to the general translator, and in doing so it
produced twenty-three findings about *this repository* — its own code, its own design document, and its
own test harness — and, in **F56**, about what the code this translator emits actually does when it is
compiled and run. They are numbered F34 through F56, continuing the single `F` series that
`docs/STAGE_B_FINDINGS.md` opened at F1–F20 and `docs/STAGE_D_FINDINGS.md` carried to F21–F33.

The `F` series and the `P` series answer different questions, and keeping them apart is the whole
point of having two. A **P** number is a correction to the canonical paper, and every one of them
lives in `docs/PAPER_CORRECTIONS.md`. An **F** number is a gap, weakening or outright error in *this
development*, which the paper is not responsible for. When a finding turns out to be both, it gets a
number in each series and each entry says so; F35 is the live candidate for that treatment and has
not earned its `P` number yet, for the reason its own section gives.

**What is restated and what is not.**
Every finding below is stated here in full, so that this file can be read on its own. Where the same
fact is also recorded on the declaration it concerns — and most of them are, because a finding that
lives only in a document does not survive a refactor — the docstring is cited by `path:line` rather
than quoted at length. The citations are as of `7f23186`, which is the commit that landed the stage E
code layer; line numbers drift and the declaration names do not, so both are given.

**The provenance rule.**
Stage D introduced four grades and they are used unchanged here, because the distinction between
"we ran it" and "we reasoned about it" is the one this project most often loses under time pressure:

* **measured** — a named run produced the result. The run is identified well enough to repeat: a gate
  name and its markers, or a probe section.
* **read** — the claim is a reading of source at a cited `path:line`. Includes absence established by
  a search over the tracked tree, in which case the search is described.
* **decided** — a choice was made between recorded alternatives. The alternative is stated, so that a
  later stage can reopen the decision instead of rediscovering that there was one.
* **inferred** — argued, not run. **No soundness claim rests on an inferred finding.** An inferred
  finding either names the experiment that would settle it or it does not belong in this file.

**What is deliberately not here.**
The `D` series is a different thing entirely and is not touched: `docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`
numbers the restrictions that define the DTR fragment this translator claims to accept, those numbers
are cited from Lean, and nothing in this file renumbers or reinterprets them. Stage D's findings file
records that the letter `D` had been overloaded four ways; the resolution was that `D` means a
fragment restriction and nothing else. Findings are never labelled with a bare letter again.

Also not here: the design decisions themselves. `docs/STAGE_E_DESIGN.md` owns what stage E *does* and
why, including the four decisions put to the user and their answers. This file owns only what stage E
*found wrong*.

---

## Numbering history, in full

Provisional numbers that later move are worse than no numbers, so the history is written out rather
than assumed.

F34 through F40 were first written in `docs/STAGE_E_DESIGN.md` §11.1, under an explicit warning that
they were *"provisional until the findings file lands"* and *"do not cite these elsewhere yet"*. That
warning was earned: stage D's design had numbered its own findings D1 through D9, they became F21
through F29 when the stage D findings file landed, and the D-numbers became uncitable. **This file is
what makes F34–F56 citable.** Nothing below is provisional any more. (This range is one of the places that
move whenever an entry is added, and it is the one that went stale when F50 landed. How many places there
are depends on how finely they are counted, which is not a quibble: this file answers it three times and
three ways. **F51** lists four, **F54** lists a different four, and the paragraph below at *"The three
places that have to move together"* lists three. **F55** item 5 reconciles all three and gives the total as
six counted finely, five at F54's granularity.)

F41 and F42 were never in the design document, and **until this file landed** they were recorded only
on the declarations they concern — F41 across `Relico/Translation/GeneralRouting.lean:47`, `:1127` and
`Relico/LF/GeneralCppPrinter.lean:1526`, F42 across `Relico/Translation/NameGeneration.lean:114`,
`:208` and `Relico/Translation/GeneralRouting.lean:68`. **Both have full entries below.**

F43 was claimed on 2026-08-21 in **committed** code — `frontend/lean-bridge/GeneralLfPrinterTestMain.lean:3235`,
`:3269`, `:3450` and `frontend/check-general-lean.sh:197` — while this file did not yet exist. That
is the rule being bent: for the interval between `7f23186` and this commit, four tracked files cited
a finding number with nothing to cite. It is recorded rather than tidied away, because the pressure
that caused it (a green gate is a strong incentive to land) will recur.

F44 is stated here first and nowhere else yet, which is the intended order.

F45, F46 and F47 were added after this file first landed, each in its own task (#53, #54, #55), and F48 in
task #57. **All four were added without updating this file's title, its "fifteen findings" count, or the
range on the line above** — which were left reading *"F34 through F44"* and *"eleven findings"* for three
findings running, until F48's commit corrected all three. That is not a footnote: it is the failure family
F44–F48 are *about*, occurring in the file that documents it, and it happened because the numbers live in
prose at the top of a long document while the work happens at the bottom. The three places that have to move
together are line 1, the "Why this file exists" paragraph, and the numbering-history line above; a fourth
finding added without touching all three should be treated as a defect in the commit, not a tidy-up owed
later. No gate checks this, which is the standing reason to prefer a `grep`-able label over a written count
wherever the choice exists.

F49 was added in task #59, and its commit moved all four places in the same edit rather than leaving them
owed — the first time in this file's history that a finding arrived without dragging a stale count behind
it. Recorded because a convention that has held once is not yet a convention: the next finding is the test.

F50 missed one of the four when it landed at `f9f241e`, and **F51** records which and repairs it. F54's
commit moved all four and said so. F55, added in task #67, moves a place no earlier entry had to: F54's own
closing paragraph counts the entries sitting below the stranded *What is left open* section, so appending an
entry falsifies it. F55 also measured something the three tallies above hide — this file states the
move-together rule three times, at *"The three places that have to move together"* below, in **F51** and in
**F54**, and no two of the three name the same set. Item 5 of that entry reconciles them, which is why the
parenthetical above now gives the total at two granularities instead of asserting one number.

One further echo of F43, at the shortest possible interval. Two tracked files cited **F55** by number in
commit `c6ce367` — `frontend/java-bridge/check-general.sh` and `frontend/test_validate_general_v1.py` — one
commit before this entry existed. F43's paragraph above predicted the recurrence and named the cause, and
the cause was the same one: the commit carrying the code was green, and the entry was documentation that
could follow.

F56, added in task #69, is the first entry in this file whose subject is not this repository but the
behaviour of the target code the translator emits — measured by compiling and running it. It was written
despite a decision taken one commit earlier to stop adding entries here, and that decision is not being
quietly abandoned: it was a decision to stop writing findings about *this file's own bookkeeping*, three of
which had landed in a row. The test it set was whether an entry records a defect in something that runs,
and F56 is the first since then to pass it. Its commit moves all six places, F55's closing paragraph among
them, and repairs `docs/STAGE_E_DESIGN.md` §6.3 and §11.2 item 7 in the same edit, because both carried
claims the measurement refuted.

**One trap.** The number F34 was considered once before, in stage D, for a different thing entirely,
and rejected — `docs/STAGE_D_FINDINGS.md:289` records that it would have duplicated an obligation F32
already carried. F34 below is not that finding and has no relation to it.

---

## F34 — the readable port-naming rule is not injective

**Grade: read.** `Relico/Translation/NameGeneration.lean:107–121`, the docstring on
`outputPortNameFor`, which states the same two witnesses on the declaration itself.

Port names are built by concatenation: `outputPortNameFor message knownRebec siteSuffix` is
`message ++ "To" ++ capitalizeName knownRebec ++ siteSuffix`, and `inputPortNameFor` wraps that with
`++ "From" ++ capitalizeName senderInstance`. The result reads as English in the direction the arrow
points — `reportToHub`, `reportToHubFromWorkerAlpha` — which is the property ledger correction P20
asks for. It is not injective, and two independent witnesses show why:

* **The separator is not escaped.** Message `reportTo` with known rebec `hub`, and message `report`
  with known rebec `toHub`, both produce `reportToToHub`. Both are legal Rebeca identifiers.
* **The boundary before the site suffix is unmarked.** Message `report` to rebec `hub` at send site 2
  produces `reportToHub2`, and so does message `report` to rebec `hub2` at a class's only send site,
  because the sole-site suffix is empty.

The general statement is stronger than either witness: *every* readable separator has this property,
underscores included, so this is not a defect of the particular spelling chosen. Any implementation
that claims unique port names from a concatenation rule, without either escaping the separator or
checking the result, is wrong.

**What follows, and what does not.** This is not a soundness defect, because uniqueness is not
claimed of the rule. It is decided **on the program the translation builds**:
`LF.GeneralReactor.declaredNames` must be `Nodup`, and `guardGeneralProgram` refuses the program with
a diagnostic when it is not. That check is strictly stronger than injectivity of the naming rule would
be, since it also covers collisions against state-variable, action and parameter names — which no
port-naming rule can rule out from its own side, because those names come from the source.

The cost of doing it that way is recorded separately as **F39** (models stage D accepted are now
refused) and **F43** (the refusal is a partiality no type records). P20 stands independently of all of
this: the paper's two figures disagree about port names and neither offers a rule that survives the
witnesses above.

**Distinct from F42.** F42 is a *third* collision channel, case folding, and the standard fix for
F34 — escaping the separator — does nothing about it. The declaration's docstring at `:110–115`
assigns the unmarked-boundary witness to F34, while the section note at `:204–207` reuses that same
witness for F42. Both readings are defensible because the two findings are about different
statements, but the overlap is real and is flagged here rather than smoothed: F34 is about the naming
function, F42 is about a lemma the design document asked for.

---

## F35 — DTR delays a statement, LF delays a connection, and that is a naming problem rather than an expressiveness one

**Grade: read, after a decided weakening.** `Relico/Translation/GeneralBasic.lean:529` carries the
one-line form on the declaration; `docs/STAGE_E_DESIGN.md` §11.1 carries the weakening.

In DTR the delay belongs to the *send statement*: `hub.report() after(2)`. In LF the delay belongs to
the *connection*: `probe.reportToHub -> station.reportToHubFromProbe after 2 msec`. A statement is not
a connection, so the two do not correspond one-to-one, and a class with two sends to one (known
rebec, message) pair carrying different delays has two statement-level delays and — under the obvious
reading of the paper's figures, which key a port on the pair — one connection to put them on.

**This finding was weakened on 2026-08-20 and the original form was wrong.** As first stated, the
claim was that such a pair is **unrepresentable**. It is not. Giving each *send site* its own port and
its own connection represents it exactly, which is what §6.2 of the design now does, and the target
model was never short of expressiveness.

What survives is a finding about the figures rather than about the target: the paper places the delay
on the arrow and never shows two sends to one pair, so it never confronts the choice, and an
implementation that follows the figures literally is forced either to lose messages or to refuse legal
models. Both horns are written up as **F40**, which is the same discovery seen from the design
document's side.

**Why this has no `P` number yet.** Turning F35 into a paper correction requires reading what the
paper actually says about the send rule and where the delay goes, and that reading has not been done.
It is owed in §11.2 item 3 of the design and is carried forward in this file's closing section. The
paper is a PDF **outside** the repository at
`~/Desktop/LFStructuringNonDeterminism/DTR_LF__After_FMCAD_.pdf`, and it is never edited as a side
effect of anything. Until that reading happens F35 stays an `F`.

---

## F36 — the type erasure stage D removed from actions had propagated to the port layer

**Grade: read.** `Relico/LF/GeneralSyntax.lean:399–432`, the docstring on `GeneralPortPayload`, which
states the finding and then closes it in the same place.

Stage C and stage D gave a port declaration a `declaredType : LF.GeneralType`, and `GeneralType` is
`int | boolean`, so that field names the type of exactly one value. This is the same erasure stage D
found and removed at the action layer — where `initialValue : Int` could not hold a boolean and
`msgsrv logic(boolean, boolean)` had nowhere to put its second parameter — surviving one layer further
along. A message server such as `msgsrv report(int identifier, boolean urgent)`, reached by an external
send, needs a port carrying two values of two types.

**As landed, this finding is closed by construction, and the design document has not caught up.**
`docs/STAGE_E_DESIGN.md` §11.1 still describes F36 as a live gap, because it was written before the
implementation. The landed type is:

```lean
inductive GeneralPortPayload where
  | scalar : LF.GeneralType → GeneralPortPayload
  | struct : ReactorName → ActionName → List LF.GeneralTypedParameter → GeneralPortPayload
```

The two constructors are one mechanism with a printed special case: `scalar t` prints as
`input p: int`, and `struct` prints as `input p: <Reactor>_<message>_Args`, referring to a
program-level `public preamble` struct whose fields are the parameter list. The struct's name comes
from `generalPayloadStructName`, the same function the action layer already used, which is what lets
one struct declaration serve a message server that is both self-sent and externally received. Naming
it from the **receiving** reactor is what makes both ends of a connection agree without either end
consulting the other — and that is a weakening in its own right, recorded as **F37**.

`GeneralTypedParameter` had to move ahead of the port declaration for this to typecheck, since a port's
payload is now a parameter list. Stage D had placed it after, when no port could reference it.

**The residue, which is genuinely open.** There is no `void` constructor, so a port carrying nothing
is unrepresentable and an arity-zero external send is *refused* by the translation rather than
mistranslated. That refusal is provisional and the declaration says so: whether `lfc 0.11.0` accepts
`input p: void` is **unmeasured**. The probe and its prediction are written down in §11.2 item 1 of
the design and carried forward below. The day it runs, either this type gains a constructor or the
refusal becomes permanent.

---

## F37 — a derived name became a stored one, so a guarantee by construction became a guarantee by predicate

**Grade: read.** `Relico/LF/GeneralSyntax.lean:421–425` states it; `Relico/LF/GeneralWellFormed.lean:326`
and `Relico/Translation/GeneralBasic.lean:136` are the two sites where the consequence shows up.

Stage D derived the payload struct's name — `<Reactor>_<message>_Args` — at exactly one site, so no two
sites could disagree about it. Stage E's ports carry the same struct, and a connection has two ends,
so the name is now **stored** at both ends and their agreement is *checked* by a well-formedness
clause instead of being unavailable to fail.

"Cannot disagree" became "is checked". That is strictly weaker, and it is recorded rather than allowed
to pass for two reasons. First, the printer's own stated principle is to derive names rather than store
them, so this is the codebase departing from a rule it wrote down. Second, a checked property has a
failure branch, and every failure branch is a diagnostic somebody has to read and a partiality
somebody has to handle — which is exactly the cost **F43** measures.

`GeneralBasic.lean:136` names the shape of it plainly: the property is *"true, but **checked** rather
than earned by construction"*. `Relico/Translation/GeneralRouting.lean:53` records the mitigation that
keeps the weakening from spreading — one builder constructs both ends of a route, so no call site is
in a position to store two different names — and is careful to say that this is a *different*
guarantee from F37 rather than a repair of it. The check remains necessary because the type still
permits disagreement even though no current caller can produce it.

---

## F38 — hypothesis: the `_action` suffix is unreserved, and that is reachable from a `.rebeca` file

**Grade: inferred.** Stated as a hypothesis on purpose, with the experiment named. No soundness claim
rests on it.

`actionNameFor` builds a logical action's name by appending `_action` to the message-server name, and
nothing reserves that suffix on the DTR side. So a class of this shape:

```
reactiveclass Ticker(3) {
  statevars { int tick_action; }
  msgsrv tick() { }
}
```

appears to be accepted by the Java exporter, by the elaborator and by `DTR.GeneralModel.wellFormed`,
and to translate to a reactor declaring `tick_action` as both a state variable and a logical action.

**Why this matters more than F32's witness does.** F32's counterexample has to be built by hand in
Lean, because the elaborator rejects the source that would produce it. This one starts from a
`.rebeca` file, which means it is reachable by a user rather than only by a test. Stage E's own port
names inherit exactly the same exposure — nothing reserves `To`, `From` or a trailing digit either —
and §9's guard is what contains both.

**It is stated as a hypothesis, and that is the standing lesson from F32.** F32 was concluded across
an unchecked layer: a toolchain measurement was turned into a pipeline claim without reading the
elaborator in between, and the elaborator refuted it. The same mistake is available here, since the
claim spans the exporter, the elaborator and DTR well-formedness, and only one of those three has been
read.

**The experiment.** Add the class above as a fixture and run `frontend/java-bridge/check-general.sh`,
which needs the Java exporter and therefore Maven on the Mac. It shares that requirement with pending
task #36 — the `reject/` fixture for a constructor formal shadowing a state variable — so the two
should travel together in one Maven round trip.

---

## F39 — stage E is not conservative over stage D

**Grade: decided.** The alternative was considered and rejected; §11.1 of `docs/STAGE_E_DESIGN.md`
records the rejection in its *"F39 — stage E is not conservative over stage D"* bullet.

`Translation.compileGeneralModel` now ends in `guardGeneralProgram`, which refuses any program that
fails `LF.GeneralProgram.wellFormed`. Some models that stage D translated successfully are therefore
refused by stage E. A stage that *removes* accepted inputs while adding capability should say so out
loud rather than let a shrinking input set pass as an improvement.

**The mitigating fact, which does not make the finding go away.** Every model that loses acceptance
this way had ill-formed LF output before — output that either would not have been accepted by `lfc` or
would not have compiled as C++, as the `param_state_name_collision` probe showed for one such case. So
this is a bug fix in substance. The reason it is still a finding is that "we refuse more than we used
to" and "we refuse exactly the broken ones" are different claims, and only the first has been
established; the second would need the preservation theorem that **F32** says is false as stated.

**The alternative that was rejected.** Keeping every stage D input working, by emitting the ill-formed
program and leaving well-formedness as a separate query the caller may or may not run. That was
rejected because a translator whose output may be ill-formed pushes the obligation onto every consumer,
and the gate that runs `lfc` is not the only consumer. The cost of the choice is **F43**.

---

## F40 — a design document's own defect: one port per (rebec, message) silently drops messages, and the refusal that seems to fix it cannot

**Grade: read, then decided.** Recorded against §6 of `docs/STAGE_E_DESIGN.md` **as committed at
`6298284`** — revision 1 — not against the paper. A design that was reviewed and landed is exactly the
kind of artifact whose errors are worth keeping visible, so revision 1's text was not quietly
overwritten: `docs/STAGE_E_DESIGN.md:19–20` and §6's opening paragraph point at this finding from the
document that replaced it.

Three parts, each independently reusable.

**1. The blessed case was the broken one.** Revision 1 keyed one port on each (known rebec, message)
pair, and said of two sends to one pair with the *same* delay: *"fine. They deduplicate to one
connection, and the second statement is a second `set()` on the same port."* An LF port carries **one
value per tag**. So `hub.report(1); hub.report(2);` — two Rebeca messages, two runs of `report` — became
one reaction firing. A message is lost, with no error anywhere. For a translator that carries a
preservation theorem this is the worst available failure mode, and it was sitting in the case the
document had explicitly declared safe. The differing-delay case, which the document worried about, was
the one that happened to work.

**2. A sound syntactic refusal refuses the wrong thing.** The obvious repair is to refuse models where
two sends can arrive at one tag. But "two sends arrive at one tag" is a property of *executions*, not of
syntax: `report after(2)` in one message server and `report after(5)` in another coincide whenever the
first fires three time units after the second. Any *sound* static rule must therefore refuse **every**
class with two sends to one pair, delay-independent — which refuses the differing-delay case that has to
work. There is no refusal satisfying both requirements. Discovering that is what forced a redesign
rather than a patch, and it is the part of this finding most likely to recur elsewhere: a dynamic
property admits no exact syntactic proxy, and the sound approximation may be useless.

**3. The key was the error.** Keying on (rebec, message) is the natural reading of the paper's figures,
and it is what makes the hazard exist at all. Keyed on the **send site** — an address, not a counter —
the invariant becomes structural (§10.2), the delay question dissolves (§6.2), and two Rebeca messages
become two ports. The target model was never short of expressiveness; the design had imported a
limitation from the figures.

**The requirement that drove the redesign**, on the record in the user's own terms: two `set()`s on one
output port at one time must not be allowed in LF; two invocations of the same action are acceptable;
and DTR source that would produce the first must be rejected with the reason stated clearly, mechanism
delegated. Making the situation **structurally unreachable** satisfies that requirement more strongly
than rejecting it would, because there is no source program left to reject.

---

## F41 — the preamble deduplicates struct declarations on the name alone, and nothing compares an action's parameters against a port payload's fields

**Grade: read, with one measured detail.** `Relico/LF/GeneralCppPrinter.lean:1505–1527` on
`generalDedupStructDecls`, `Relico/Translation/GeneralRouting.lean:47–55` and `:1120–1127`. The measured
part is identified below.

A payload struct is named by a message server's logical action *and* by every port that carries it. The
printer emits one `public preamble` and deduplicates those declarations **by name**, not by rendered
text, and both halves of that choice are deliberate:

* Identical declarations must collapse, because a message server that is both self-sent and externally
  received is named by one action and by two or more ports, and `lfc` must see one
  `struct Collector_report_Args` rather than three copies.
* Declarations that share a name and *differ* must also collapse, because C++ rejects a file declaring
  one struct twice with different fields. Keeping the first is the only behaviour that leaves a legal
  file at all.

**The gap is the second bullet's cost.** When two declarations share a name and differ in their fields,
the printer silently keeps the first and nothing notices. Half the generated program would then be
compiled against fields the other half never declared.

**What it is not.** It is not reachable from the translation. The struct's name is a function of the
receiving reactor and the message, its fields are a function of that same message server's formals, and
DTR well-formedness makes message-server names unique within a class — so one builder produces both and
disagreement is unsayable. `Relico/Translation/GeneralRouting.lean:47` records that this is the sharpest
reason the type map moved into the routing layer rather than being copied: two builders that disagreed
on a type would produce exactly this defect.

**Why it is still open.** It *is* reachable from a hand-built `LF.GeneralProgram`, and no LF-side
predicate rules it out. `connectionWellFormed` compares the two ends of one **connection**, which is not
the same as comparing two declarations of one struct name across a whole program — and **F37**'s check
is likewise about a sender and a receiver, saying nothing about an action and a port on the same reactor.
The right fix is a well-formedness clause quantifying over every declaration of a name; a printer is the
wrong layer to discover a program-wide inconsistency in, which is why it was not closed where it was
found.

**The measured detail.** In the routed program the `GENERAL_LF_TARGET_OK` gate emits, compiles and runs,
`struct Gateway_report_action_Args { int level; bool urgent; };` appears once though **five**
declarations claim it — `Gateway`'s own `report_action`, both of `Sensor`'s `reportTo…` output ports, and
both of `Gateway`'s matching input ports. The survivor comes from `Sensor`'s first output port, not from
`Gateway`'s action. They agree here, so nothing is lost; the point is that which one survives is
determined by emission order rather than by anything checked.

**Deliberately not mirrored elsewhere.** `GeneralRouting.lean:1120–1127` records that the three
projections — output ports, input ports, connections — deduplicate **nothing**, on purpose. Two
declarations of one port name are caught by the `Nodup` guard with the offending name in the diagnostic,
whereas a `dedup` there would collapse two ports carrying *different payloads* into whichever came first
and emit a program that compiles and drops messages. The distinction being relied on is that a struct
declaration is not a name a `set()` call can miss, and a port is.

---

## F42 — the design's second one-sided injectivity lemma is false, and the honest lemma cancels only down to the infix

**Grade: read.** `Relico/Translation/NameGeneration.lean:193–218` is the section note that states it;
`:246–276` is the weaker lemma that was proved instead; `Relico/Translation/GeneralRouting.lean:68`
records from the routing side that the stronger lemma *"is false and is not stated"*.

`docs/STAGE_E_DESIGN.md` §4.3 asked for **two** one-sided injectivity lemmas about `outputPortNameFor` —
*"with the message fixed the name determines the rebec, and with the rebec fixed the name determines the
message"* — on the stated ground that *"both reduce to suffix or prefix cancellation"*. Only one of the
two is true, and the design's own material refutes the other.

**The one that holds.** With the known rebec and the site suffix fixed, the name determines the message.
That is suffix cancellation, and it is `outputPortNameFor_message_injective`, a one-line proof of the same
shape as `actionNameFor_injective`. Making it that shape is the *only* reason `outputPortInfixFor` exists
as a separate definition: it puts the varying component at one end of a single `++` against one opaque
string, instead of leaving a reassociation argument about three appends.

**The one that fails.** With the message fixed, the name determines the **infix** and no more, and the
infix does not determine the rebec. Two reasons, both of which §4.3 states in the same section without
noticing that they close the direction off:

* `capitalizeName` folds case, so `hub` and `Hub` give one infix. This is F42's own channel, and it is
  **not F34**: escaping the separator, the standard fix for F34, does nothing about it.
* The boundary between the capitalized rebec and the site suffix is unmarked, so `hub` at site 2 and
  `hub2` at a sole site give one infix. This witness is shared with F34, which the previous section
  flags.

So the lemma is stated in the strongest form that holds — `outputPortInfixFor_eq_of_outputPortNameFor_eq`,
cancellation down to the infix — and the gap is this finding. `capitalizeName`'s own docstring at `:63–65`
says the non-injectivity *"is a fact about the names rather than an accident of the definition"*, since
`hub` and `Hub` are both legal Rebeca identifiers.

**No Lean refutation is attempted, and the reason is recorded rather than left as an omission.** A
concrete witness needs `capitalizeName "hub"` to reduce in the kernel, which means reducing
`String.front` and `String.drop` through the UTF-8 model; a parametric witness needs idempotence of
`Char.toUpper`, which core does not supply. The declaration therefore delegates the witness to the
printer test main, which evaluates these functions at run time — **and that delegation is currently
unfulfilled, which is F44.**

---

## F43 — `compileGeneralModel` is partial on models DTR well-formedness accepts, and no type records it

**Grade: measured.** The `GENERAL_LEAN_GATE_OK` run at `7f23186`: 67 printer assertions, of which the
F32 group's five are `PASS_DTR_ACCEPTS_PARAMETER_STATE_COLLISION`,
`PASS_COLLISION_MODEL_REFUSED_BY_THE_GUARD`, `PASS_TRANSLATED_COLLISION_PROGRAM_ILL_FORMED`,
`PASS_COLLISION_PROGRAM_INSTANCE_ARGUMENTS_STILL_MATCH` and
`PASS_COLLISION_PROGRAM_HAS_NO_CONNECTIONS`. Stated on the code at
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean:3269` and `frontend/check-general-lean.sh:197`.

`Translation.compileGeneralModel` now ends in `guardGeneralProgram`
(`Relico/Translation/GeneralBasic.lean:2343`), which returns `.ok program` **only when**
`program.wellFormed` and otherwise `.error ("the translated LF program is not well-formed: " ++ …)`.
There exist models that `DTR.GeneralModel.wellFormed` accepts and `compileGeneralModel` refuses. One is
committed as `collisionModel`, and the refusal is now asserted **by its exact text**, because a routing
failure or a class that stopped compiling would satisfy a bare `.error` check while quietly meaning the
model no longer reaches the guard at all.

**Three claims, and conflating them is the trap.**

1. **The guard is sound on output.** No ill-formed LF text can be emitted by this function. That is a
   real improvement and it is why the guard was added.
2. **It does not repair F32.** The preservation theorem says a well-formed DTR model translates to a
   well-formed LF program. A refusal is a *witness* that this one does not — it changes where the
   counterexample is observed, not whether it exists.
3. **The partiality is recorded by no type.** `Except String LF.GeneralProgram` cannot distinguish "this
   model is untranslatable" from "this translation produced something ill-formed", so a caller has to
   read the diagnostic string to tell them apart. That is the cost of **F39**'s decision, and it is
   unpaid.

**Where the F32 witness lives now, since this is the part a future session will search for and not
find.** The counterexample is no longer reachable through `compileGeneralModel`. `assembledCollisionProgram`
in the printer test main replays that function's own three public steps — `Translation.routesOf`, then
`Translation.compileGeneralReactiveClasses`, then `Translation.assembleGeneralProgram` — and stops before
the guard. The three original F32 assertions run against *that* program.

**The process lesson, which is the reusable part.** Task #44's own docstring at
`Relico/Translation/GeneralBasic.lean:2446` predicted this exact breakage — *"every consumer of it that
assumed the assembled program **is** the result has to be re-read"* — and `collisionAssertions` was the
unread consumer. The prediction was written and then not acted on, and the cost was two blocked runs in a
later task. **A docstring that says "every consumer has to be re-read" is a task, not a note.**

---

## F44 — a docstring delegates a witness to a test that does not exist

**Grade: read**, by absence. Method: `grep -rn` over every tracked `.lean` file at `7f23186` for
`capitalizeName`, `outputPortNameFor`, `outputPortInfixFor` and `inputPortNameFor`. Outside their own
declaring module the only hits are five in `Relico/Translation/GeneralRouting.lean` — three of them
prose, two of them call sites at `:754` and `:908`. There is no hit in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean`. Every `COLLISION` label in that runner belongs to
F32's parameter/state-variable group.

`Relico/Translation/NameGeneration.lean:210–217` explains that F42 is not refuted in Lean, for good
reasons, and then says:

> The right instrument for a concrete string witness is
> `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`, which evaluates these functions at run time and
> compares the results — so the collision is asserted there, where it costs nothing, rather than argued
> here.

**No such assertion exists.** The sentence is written in the present tense about a test that was never
added, so a reader who takes the docstring at face value concludes that F34's and F42's collisions are
demonstrated by a running gate when nothing anywhere evaluates a port name at two arguments and compares.

**Why this is worse than a missing test.** A gap with no test is visible in the coverage counts; a gap
whose documentation claims a test **removes the signal that would have found it**. The same paragraph is
also the justification for not attempting a Lean refutation, so the missing assertion is load-bearing for
a decision, not merely absent.

**It was found by reading the source in order to write this file down**, which is worth recording as
evidence for the practice: F34 and F42 had been carried in three code comments for a day without anyone
noticing that the discharge they pointed at was empty.

**The fix is cheap and is owed.** Two `expectString` assertions in the printer runner — one comparing
`outputPortNameFor ⟨"reportTo"⟩ ⟨"hub"⟩ ""` with `outputPortNameFor ⟨"report"⟩ ⟨"toHub"⟩ ""` for F34, one
comparing `⟨"report"⟩ ⟨"hub"⟩ "2"` with `⟨"report"⟩ ⟨"hub2"⟩ ""` for F42's shared witness, and a third for
the case-folding channel — plus the docstring rewritten to name them. Because it moves
`EXPECTED_PRINTER_ASSERTIONS` and the `runGeneralLfPrinterTests` docstring, it must travel with the other
count moves rather than on its own; it is assigned below.

> **Discharged the same day, in task #45.** The three assertions exist and run, under the labels
> `PORT_NAME_UNESCAPED_SEPARATOR_COLLIDES`, `PORT_NAME_SITE_SUFFIX_BOUNDARY_COLLIDES` and
> `PORT_NAME_CASE_FOLDING_COLLIDES`, in a `portNameCollisionAssertions` block between the translation
> group and F32's counterexample group. `EXPECTED_PRINTER_ASSERTIONS` moved 67 → 70 and both docstrings
> that state the breakdown moved with it. `NameGeneration.lean` now names the three labels instead of
> promising them, so the claim is checkable by grepping for a label — which is the property the original
> sentence lacked, and the reason it could be false for a day.
>
> Two details of the fix differ from the plan written above, and both are deliberate. First, each
> assertion pins **both** generated names against one literal — `"reportToToHub = reportToToHub"` rather
> than asserting only that the two calls agree. Asserting mutual equality alone would still pass if the
> naming rule changed in a way that collided on a *different* string, which is exactly the regression a
> collision witness is for. Second, the boundary witness is labelled for the boundary rather than for
> F42, because the source assigns that witness to F34 at `NameGeneration.lean:110–115` and to F42 at
> `:204–207`; the label names the mechanism, so it stays correct under either reading, and the
> inconsistency itself is recorded under **F34** rather than resolved here.

---

## F45 — a findings file denies a test that exists, which is F44 pointing the other way

**Grade: measured.** Method: `ls` of `frontend/fixtures/general/lean-reject/`, which contains
`invalid-parameter-shadows-state.json`, and `grep -n` of
`frontend/lean-bridge/GeneralFrontendTestMain.lean`, which asserts `.parameterShadowsStateVariable` at
`:300` under the label `PARAMETER_SHADOWS_STATE_VARIABLE` printed at `:298`.

`docs/STAGE_D_FINDINGS.md:401` says:

> One consequence worth its own line: nothing in the twelve lean-reject fixtures exercises
> `.parameterShadowsStateVariable`. The guarantee this correction leans on is **untested**, which is the
> shape of the `PrioritiesDistinct` defect from stage B — a predicate that exists and is never reached.
> A fixture for it is now the cheapest thing on this list.

Task **#35** added exactly that fixture and exactly that assertion. The sentence has been false since, and
as of task #50 it is false twice over: the corpus is fourteen documents, not twelve.

**Why this costs something.** The paragraph it closes is the argument that F32 is **not** a soundness gap —
the elaborator rejects a shadowing formal, so a `.rebeca` file cannot deliver the collision to the
translator. That argument leans on the elaborator's guarantee, and this line is the flag saying the
guarantee is unchecked. With the flag stale, a reader either re-does work that is done, or discounts an
argument that is in fact now backed by a running assertion. The flag also nominates itself as "the cheapest
thing on this list", so it actively solicits the duplicated effort.

**The mechanism, and how it differs from F44.** F44 promised a test that did not exist; this denies a test
that does. The root is the same and is the reusable part: **coverage stated in prose is unfalsifiable by
the gate, and coverage stated as a label is checkable by `grep`.** The costs differ in shape rather than in
size. A false claim of coverage removes the signal that would have found the gap; a false denial of
coverage manufactures phantom work and quietly undermines a correct argument. Neither is visible to any
count the gate maintains, because the gate counts assertions, not sentences about assertions.

**Fixed by addendum, not by rewriting.** The original paragraph stays as written, with a `>` block beneath
it recording that #35 discharged it — the convention F40 relies on, and for the same reason: the stale
sentence is the argument that produced the fixture, so deleting it would erase the reason the fixture
exists.

---

## F46 — a count that was false the moment it was written, which is not drift

**Grade: measured.** Method: `git show` of `frontend/fixtures/general/lean-reject/README.md` at two
revisions, counting the list entries at each, rather than reading the sentence and believing it.

Before task #50, that file said the corpus covers a set of reasons "ahead of the **nineteen** still listed"
while the list beneath it held **twenty** entries.

**The history is the finding.** At `dddf04b` the list held twenty-one entries and the surrounding prose said
twenty-four and twenty-three; those three numbers agreed with each other and with the list. `b14809b` then
removed one entry, leaving twenty, and **correctly** decremented both inherited aggregates. In the same
commit it wrote a *new* sentence naming the list's length, and got it wrong by subtracting one from a list
it had itself already shortened — arithmetic on the pre-edit value, applied to a post-edit list.

**So this is not the failure the doc-count rule guards against.** That rule exists because a count in file A
goes stale when file B changes, and it says: grep the spelled-out words rather than the numerals, and move
every occurrence in one commit. `b14809b` obeyed that rule and the rule worked — the two aggregates it
inherited are right. What the rule cannot catch is a number that never matched anything, because there is no
earlier revision in which it was true and therefore no diff in which it became false. **Drift is
true-then-stale; this was born stale.**

**What would actually catch it.** Only adjacency: a count stated in its own sentence, immediately beside the
thing it counts, so that verifying it is reading one screen rather than reconciling two. #50's replacement
does that — the aggregate and the list length are now separate sentences, each naming which set it measures,
because the two genuinely differ: twenty-one reasons are unexercised, and the enumerated subset of those
that are *reachable* now has eighteen names in it. Conflating a subset's length with its superset's is the
second way this sentence could have gone wrong, and stating both is what makes the difference visible
instead of arguable.

**Fixed textually in task #50**, in the same commit as this file.

---

## F47 — two built-module docstrings credit coverage to fixtures that cannot reach the code

**Grade: measured.** Method: every originating `.error` site in `Relico/Translation/GeneralRouting.lean`
located by `grep -n`, each one attributed to its enclosing `def` by the `def` line above it, and each
diagnostic string searched for in both Lean test runners.

`compileGeneralReactiveClass_error_env` and `compileGeneralModel_error_routes` in
`Relico/Translation/GeneralBasic.lean` each ended with a clause of the form "— the three diagnostics the two
new `lean-reject` fixtures of #45 exercise". **No `lean-reject` fixture can exercise any of them.** Such a
fixture is a document the *frontend* refuses; it never reaches a translation function at all. What those two
fixtures establish is the opposite and complementary fact: that `sendTargetsDeclared` and
`sendsResolveToMessageServers` stop such a document upstream, which is precisely why two of these branches
are unreachable from frontend output — evidence that they are defensive, not evidence that they run.

**Three defects, of increasing seriousness.**

1. *Attribution to an impossible instrument*, above.
2. *Miscounts.* The first said three where there are four; the second said three where the function reaches
   eight.
3. *Misclassification.* The second grouped the arity-zero payload refusal with two bindings failures as
   things "refused upstream". It is not a malformedness at all — it is this translation's own limit, so a
   model carrying it is well formed, the frontend **accepts** it, and the refusal happens *later*. The two
   groups are unreachable from a `lean-reject` document for opposite reasons, and collapsing them hides that
   the second group is a restriction on the accepted fragment.

**Why it is load-bearing rather than cosmetic.** The first docstring's enumeration is the stated
justification for splitting `compileGeneralReactiveClass_error_env` out as its own theorem — *"§10's
inversion lemma has to be able to say which one it ruled out"*. Task **#47** owns that inversion. It would
have inherited a three-way case analysis of a four-way branch: either a proof that fails late, or worse, a
proof of a weaker statement that looks complete.

**The measurement worth keeping, since it is the real content.** Eight refusal causes are reachable through
`routesOf`, all sharing one `Except String`, so the message text is the only thing that distinguishes them:

| reached via | deciding branch | `.error` | cause |
|---|---|---|---|
| `generalOutputPortEntryFor` | `:686` | `:689` | send names a known rebec the sending class never declared |
| `generalOutputPortEntryFor` | `:699` | `:702` | declared known rebec's class is not a declared class |
| `generalOutputPortEntryFor` | `:712` | `:715` | receiving class has no message server of that name |
| `generalPortPayloadFor` | `:730` (call) | `:507` | receiving message server admits no port payload |
| `generalRouteFor` | `:931` | `:934` | instance binds no known rebec of a declared, sent-to name |
| `generalRouteFor` | `:944` | `:947` | binding names an instance the model does not instantiate |
| `generalRouteFor` | `:957` | `:991` | binding names an instance of the wrong class |
| `routesOfInstances` | `:1058` | `:1058` | instance instantiates a class the model does not declare |

**Exactly two of the eight have their text asserted anywhere**, both in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean` and both against hand-built models — the only
instrument that can reach a translation refusal — under `PARAMETERLESS_EXTERNAL_SEND_REFUSED` (`:3077`) and
`UNDECLARED_MESSAGE_SERVER_SEND_REFUSED` (`:3083`). The other six are asserted nowhere.

**A probe trap that nearly became a fourth false claim in this entry.** Grepping that runner for the
sentence built at `:507` returns nothing, which reads as "zero of the eight are asserted". The runner
asserts it through named `String` terms — `parameterlessPortDiagnostic` and
`undeclaredMessageServerDiagnostic` — that split the same concatenation at different points, so the
sentence never appears contiguously. **Grep the named term, not the message.** The same trap applies to any
future audit of this table.

**The family, which is now four findings with one root.** F44 promised a test that did not exist; F45 denied
a test that did; F46 wrote a count that was false on arrival; F47 credited coverage to an instrument that
cannot provide it. In every case a claim about the test suite was written as **prose** rather than as a
label a gate could check. Prose coverage claims are unfalsifiable by any gate this repository runs, and all
four were found by reading source in order to write documentation — not by any check. That is the argument
for the convention the fixes adopt: **name the label, and let `grep` be the witness.**

> **"Four" is false from F48's commit onward, and is kept because it is the count that was true when the
> root was identified.** The family is **five**: F48 added a prose claim about what is *provable*, and
> raising the literal for F48 exposed a fifth in `frontend/check-general-lean.sh` itself. Both are set out
> at the end of F48's entry, which is the one place this document states the family's size as a live number.

**Both docstrings are rewritten in task #50**, which is what puts this entry's citations inside the build
closure that `frontend/check-general-lean.sh` compiles. What is *not* done is the six unasserted causes;
that is carried below rather than smuggled into #50, because assertions move
`EXPECTED_PRINTER_ASSERTIONS` and every docstring that states the breakdown.

> **The six are asserted as of task #56 — the sentence above about "the other six" is therefore false
> from this commit onward, and is kept because it is the measurement that produced the work.** All eight
> texts in the table now have a label. The six added, in the table's row order, are
> `PASS_KNOWN_REBEC_UNDECLARED_REFUSED`, `PASS_KNOWN_REBEC_CLASS_UNDECLARED_REFUSED`,
> `PASS_KNOWN_REBEC_UNBOUND_REFUSED`, `PASS_BINDING_TARGET_NOT_INSTANTIATED_REFUSED`,
> `PASS_BINDING_TARGET_CLASS_MISMATCH_REFUSED` and `PASS_INSTANCE_CLASS_UNDECLARED_REFUSED`, in a new
> `routedRefusalAssertions` block. Gate evidence: `GENERAL_LEAN_GATE_OK`, `gate_exit=0`, 508 jobs,
> `printer assertions the run reported: 76` against 70, `pass_lines_total=99`.
>
> **Three things the writing measured that the table did not say.** First, the assertions are against
> `Translation.routesOf` rather than `compileGeneralModel`: `routesOf` is the function all eight causes
> reach, and asserting through the outer function would silently add the claim that no arm of *its* own
> fires first. Second, the conjunct that closes each cause, read off `wellFormed`'s five at
> `Relico/DTR/GeneralWellFormed.lean:359` — `sendTargetsDeclared` closes row one,
> `sendsResolveToMessageServers` closes row two (and `bindingsMatchDeclarations` does **not**, because a
> class nobody instantiates has no bindings to check), and `bindingsMatchDeclarations` closes rows five
> through eight, three of them through `bindingsMatchClass` at `:162`, `:168` and `:172` and the last
> through its own `none` arm at `:189`. Third, two facts that had to be derived rather than observed and
> then held under the gate: `generalOutputPortEntriesOf` recurses left to right and returns the first
> `.error`, so a class with three offending sends reports the first one — statement index 1, not 2 — and
> the port named in row seven's message is `reportToHub1`, which makes that assertion the only place the
> naming rule and a refusal are checked against each other.

---

## F48 — a docstring defers a proof that cannot exist, and the module that owns the naming rule already said so

**Grade: measured.** Method: a self-contained witness elaborated against the built package with `lake env
lean`, from a file deliberately *outside* the repository so that no untracked Lean lands in the tree. Exit 0.
Seven `#eval`s: source well-formedness and each of its five conjuncts; the sending class's output port
environment; the target endpoints of the derived connections; all nine `LF.GeneralProgram.wellFormed` clauses
evaluated **separately on the pre-guard program**, rebuilt through `assembleGeneralProgram` because the guard
collapses nine clauses into one `String`; every reactor's `declaredNames`; and `compileGeneralModel`'s
verdict. The model is described in full below, so the run is repeatable from this entry alone.

**The claim under test.** `compileGeneralModel_targetEndpointsUnique`
(`Relico/Translation/GeneralBasic.lean:4366`) carried this docstring paragraph:

> Stated as a consequence of the guard rather than proved by construction, which is the weaker of the two
> available statements and is deliberate at this point in the development. A construction proof would say the
> routing *cannot* produce a repeated target and would therefore let the guard's clause be retired as dead;
> that proof needs the same site-totality induction the sufficient condition needs, and is deferred with it.

That is three claims, and they fail in three different ways.

1. **"The routing *cannot* produce a repeated target" is false.** The witness below is a source model that
   `DTR.GeneralModel.wellFormed` accepts and whose routing produces two connections with the same
   `(targetInstance, targetPort)`.
2. **"Needs the same site-totality induction" is false, and not merely unnecessary.** Site totality is about
   the *sending* side — send sites, output ports, and the reachability of `compileGeneralStmt:587`. A repeated
   target endpoint is about the *receiving* side's input ports. The two share no lemma, so the deferral was
   parked behind work that would never have discharged it: site totality landed in task #47 commit 1 and
   brought this no closer.
3. **"Would therefore let the guard's clause be retired as dead" is the load-bearing harm.** It is an
   instruction to a later stage to delete `targetEndpointsUnique` from `LF.GeneralProgram.wellFormed`. That
   clause is the only thing standing between this collision and emitted LF that `lfc 0.11.0` rejects as a
   many-to-one connection. A finding that only corrected the first two claims and left this one would have
   left the dangerous sentence in place.

**The witness.** Class `Hub` declares state variable `seen` and two message servers `report` and `reportTo`,
each taking one `int`. Class `Probe` declares two known rebecs of class `Hub`, named `hub` and `toHub`, and a
constructor that sends `hub.reportTo(1)` and `toHub.report(2)`. Instances are `probe : Probe` with **both**
known rebecs bound to the same actor, and `hubActor : Hub`. Three separately measured facts compose to make
this collide, which is why no single earlier finding predicted it: `outputPortNameFor` does not escape its
separator, so `reportTo`+`hub` and `report`+`toHub` both spell `reportToToHub` (**F34**);
`generalSiteSuffixFor` returns the empty suffix when a (rebec, message) pair has exactly one site, so neither
send is disambiguated by an ordinal; and `bindingsMatchClass` constrains only that binding keys match declared
names and that each bound actor exists with the declared class, so **aliasing two known rebecs onto one actor
is well-formed source**. Both message servers take one parameter because an arity-zero external send is a
refusal cause in its own right (**F36**) and would have masked the effect.

**What ran.** The block below is a **superseded scratch run**, not current output. The witness was a
self-contained file elaborated against the built package with `lake env lean`, kept deliberately *outside*
the repository so that no untracked Lean landed in the tree, and its `F48_*` labels were renamed when the
assertions were carried into the suite. Grepping `F48_` therefore returns nothing anywhere in the code,
which is why the mapping is spelled out here instead of left implicit: this block once introduced itself as
*"verbatim from the `#eval` output"*, and that provenance claim is finding **F51**.

Four of its lines have landed instruments in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`, whose
expected literals match the values below character for character: `F48_SOURCE_WELLFORMED` is now
`ALIASED_ENDPOINT_SOURCE_WELLFORMED` (`:4142`), `F48_OUTPUT_PORTS` is
`ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE` (`:4147`), `F48_TARGET_ENDPOINTS` is
`ALIASED_ENDPOINT_TARGETS_COLLIDE` (`:4152`), and `F48_TRANSLATION_REFUSED` is
`ALIASED_ENDPOINT_COLLISION_REFUSED` (`:4160`). Two of the nine values the scratch run reported inside
`F48_PROGRAM_CLAUSES` are now pinned individually rather than as a string:
`targetEndpointsUnique=false` by `ALIASED_ENDPOINT_TARGET_UNIQUENESS_FALSE` (`:4180`) and
`connectionsWellFormed=true` by `ALIASED_ENDPOINT_CONNECTIONS_WELLFORMED` (`:4185`).

Three lines were **not** carried into the suite and survive only here, so they are the reason this block is
kept rather than replaced: `F48_SOURCE_CONJUNCTS`, the other seven clauses of `F48_PROGRAM_CLAUSES`, and
`F48_DECLARED_NAMES`. Of those, the five conjunct names are corroborated independently by the comment at
`:4139-4140`, which states that all five conjuncts of `DTR.GeneralModel.wellFormed` hold, aliasing
included; `reactorsWellFormed=false` is corroborated by the landed refusal text, which names a reactor
cause; and `F48_DECLARED_NAMES` is corroborated by nothing and should be treated as the weakest line in
this entry.

```
F48_SOURCE_WELLFORMED true
F48_SOURCE_CONJUNCTS bindings=true arguments=true sendTargets=true sendsResolve=true names=true
F48_OUTPUT_PORTS reportToToHub | reportToToHub
F48_TARGET_ENDPOINTS hubActor.reportToToHubFromProbe | hubActor.reportToToHubFromProbe
F48_PROGRAM_CLAUSES reactorsNonEmpty=true instancesNonEmpty=true reactorsWellFormed=false
  reactorNamesUnique=true instanceNamesUnique=true instancesResolve=true
  instanceArgumentsMatch=true connectionsWellFormed=true targetEndpointsUnique=false
F48_DECLARED_NAMES Probe: reportToToHub reportToToHub tick_action
                ;; Hub: reportToToHubFromProbe reportToToHubFromProbe seen report_action reportTo_action
F48_TRANSLATION_REFUSED the translated LF program is not well-formed: some reactor is not well-formed,
  which for stage E most often means a generated name collided with another name in the same reactor, or
  a port was set that the reactor does not declare; two connections target the same input port of the
  same instance, which the LF compiler rejects as a many-to-one connection
```

**What the gate pins today**, verbatim from a green `frontend/check-general-lean.sh`:

```
PASS_ALIASED_ENDPOINT_SOURCE_WELLFORMED
PASS_ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE
PASS_ALIASED_ENDPOINT_TARGETS_COLLIDE
PASS_ALIASED_ENDPOINT_COLLISION_REFUSED
PASS_ALIASED_ENDPOINT_TARGET_UNIQUENESS_FALSE
PASS_ALIASED_ENDPOINT_CONNECTIONS_WELLFORMED
```

Those six lines are the whole of what the suite prints for this finding: the runner emits one bare label per
assertion and no values at all. So the two blocks are not redundant and neither replaces the other — the
`PASS_` lines prove the assertions exist and passed, while the values they compared against are auditable
only by reading the `expectString` and `expectBool` literals at the lines cited above. Anything the scratch
run scored clause by clause is not asserted anywhere, which is a coverage gap this entry states rather than
hides.

**Three things the scratch run measured that were predicted wrongly or not at all**, recorded because each one would
have become a false sentence in this entry had it been written from the argument instead of the run.

* **The collision is over-determined across both reactors.** It was predicted on the receiver only. In fact
  `generalOutputPortsOf` maps over the sending class's own environment, whose two entries share a name, so
  `Probe` duplicates an *output* port at the same time as `Hub` duplicates an *input* port. Two independent
  causes for one `reactorsWellFormed=false`, which matters for any later proof that tries to attribute it.
* **`generalProgramExplanation` enumerates every failing clause, not the first.** It was predicted that the
  guard's single `String` would hide the endpoint collision behind the reactor one, and that this was the
  reason the pre-guard program had to be rebuilt. The text names both. The rebuild is still what makes the
  clauses individually scoreable, but the stated justification for it was wrong.
* **`connectionsWellFormed=true`.** It requires each connection's ports to be *declared*, not declared once,
  so it does not catch this and was never going to.

**The strongest part of this finding is not the counterexample.**
`Relico/Translation/NameGeneration.lean:107` already says, on `outputPortNameFor` itself, *"This function is
not injective and no theorem below claims that it is"*, lists F34 and F42 as two independent collision
channels, and concludes at `:117` that *"uniqueness of generated names is therefore **decided on the program
the translation builds** — `LF.GeneralReactor.declaredNames` must be `Nodup` — and refused with a diagnostic
when it fails. That is strictly stronger than injectivity of this function would be."* So two docstrings in
the same build closure gave opposite answers to the same question, and the one that was right sat on the
function while the one that was wrong sat on the theorem that would have consumed it. Neither gate can
compare two prose paragraphs, which puts F48 in the same family as F44 through F47 — a claim about this
development written as prose rather than as something a check could falsify — with one difference worth
naming: F44–F47 were claims about the *test suite*, and this is a claim about *what is provable*. That is the
more expensive kind, because it schedules work.

**What changes.** `targetEndpointsUnique` **stays** a guard clause and the guard-corollary form at
`:4337`/`:4366` is the correct shape, not a placeholder; only the docstring is rewritten, and the sentence
inviting the clause's retirement is removed rather than softened. The achievable statement is not the
construction proof but a *relative* one — `reactorsWellFormed` together with `instancesResolve` should imply
`targetEndpointsUnique`, since two connections sharing a target endpoint come from two distinct routes into
that class and `generalInputPortsOf` maps over exactly those routes, so the shared name must duplicate in the
receiver's `declaredNames`. That is carried below as its own item rather than folded in here, because it is a
proof and this is a documentation fix.

> **That relative statement is FALSE as written, and F49 measured it.** Read as an implication over an
> arbitrary `LF.GeneralProgram` it fails: F49's witness satisfies all eight other clauses and fails only the
> ninth. The reasoning quoted above is sound but every step of it is about a program the translation
> *assembled* — "come from two distinct routes" is not a property programs have, it is a property of programs
> built from a routing table. The sentence is kept unedited because it is what the proof attempt was aimed at,
> and because the way it reads as general while arguing from assembly is the whole mechanism of the mistake.
> The correctly scoped statement is in F49.

**The instrument, following the convention F47's fixes adopted: name the label and let `grep` be the
witness.** The witness model and its refusal are asserted in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean` under `PASS_ALIASED_ENDPOINT_COLLISION_REFUSED`, which
is why this entry's central claim is checked by `frontend/check-general-lean.sh` on every run rather than
resting on a run recorded in prose here. Six labels in all —
`PASS_ALIASED_ENDPOINT_SOURCE_WELLFORMED`, `PASS_ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE`,
`PASS_ALIASED_ENDPOINT_TARGETS_COLLIDE`, `PASS_ALIASED_ENDPOINT_COLLISION_REFUSED`,
`PASS_ALIASED_ENDPOINT_TARGET_UNIQUENESS_FALSE` and `PASS_ALIASED_ENDPOINT_CONNECTIONS_WELLFORMED` — taking
`EXPECTED_PRINTER_ASSERTIONS` from 76 to 82. The fifth is the first assertion anywhere in this repository
that a named clause of `LF.GeneralProgram.wellFormed` is **false**; every earlier assertion either accepts a
program, rejects one as a whole, or reads a refusal's text, and none of those can say which clause failed.

**Why an assertion already in this suite did not catch it, which is the reusable part.**
`PASS_PORT_NAME_UNESCAPED_SEPARATOR_COLLIDES` has asserted `reportToToHub = reportToToHub` since F34 was
first measured. It is a **name-level** assertion: it calls `outputPortNameFor` twice with hand-written
arguments and says the two calls agree. F48's `PASS_ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE` reads the same
pair of names out of `outputPortEnvOf`, so it is a **route-level** assertion: it says one program the
translator accepts reaches both calls. The gap between those two statements is exactly where the wrong
docstring lived for as long as it did — a name-level collision is consistent with no program ever exhibiting
it, which is what "the routing cannot produce a repeated target" was implicitly claiming. Whenever a finding
records that two generated names can coincide, the follow-on question is whether one accepted model reaches
both, and that question needs its own label.

**A fifth instance of the family, found while raising the literal for this entry — in the gate script
itself.** `frontend/check-general-lean.sh` explains `EXPECTED_PRINTER_ASSERTIONS` twice: an enumeration of
the assertion blocks, then a paragraph narrating every move the literal has made. Raising the literal to 82
meant reading both, and the enumeration turned out to list six blocks summing to **70** while the literal
beneath it read 82 — F47's six routed refusals and this entry's six had each been appended to the narrating
paragraph and to no list. So the file whose entire purpose is to catch a count that stopped matching its
description was carrying a description that did not match its count, and had been for two findings running.
Fixed in the same commit as this entry: the enumeration is now eight blocks, `34 / 10 / 11 / 3 / 5 / 7 / 6 /
6`, identical to the breakdown in `runGeneralLfPrinterTests`'s docstring, with a note that nothing
executable reads the list so the only way to find a drift is to read it against the literal whenever the
literal moves.

That makes the count of this family five, and the shape of the fifth is worth separating from the other
four. F44 through F47 were prose claims about the *test suite* and F48 is a prose claim about *what is
provable*; this one is a prose claim about *the gate's own invariant*, which is the cheapest of the five to
have caught and the most embarrassing to have written, since the gate exists precisely because a literal
maintained by addition rather than by reading goes stale. The general rule the five now support: **any number
stated in more than one place needs one of the statements to be the one a check reads, and the others to be
short enough that reading them is not optional.**

---

## F49 — the ninth clause is independent of the other eight, and two more docstrings argue it away

**Grade: measured.** Method: the same shape as F48 — a self-contained witness elaborated against the built
package with `lake env lean`, from a file deliberately *outside* the repository so no untracked Lean lands in
the tree. Exit 0. Seven `#eval`s: the nine clauses of `LF.GeneralProgram.wellFormed` in two groups of five and
four, the program's own `wellFormed`, each reactor's `wellFormed` separately, the receiver's `declaredNames`
with its `Nodup` verdict, the mapped list of target endpoints, and `guardGeneralProgram`'s refusal.

**The claim under test**, taken from F48's own entry, is that `reactorsWellFormed` together with
`instancesResolve` implies `targetEndpointsUnique`. If that holds as an implication over programs, no program
can satisfy the first two and fail the third.

**The witness, in full.** Two reactors. `Sender` declares two output ports `outOne` and `outTwo`, both
`scalar int`, no inputs, and a startup reaction with an empty body. `Receiver` declares **one** input port
`incoming`, also `scalar int`, and a startup reaction with an empty body. Neither has parameters, state
variables, logical actions or message reactions — an empty body makes `reactionWellFormed` reduce to
`triggerWellFormed`, which `.startup` satisfies outright, so the reactors are minimal rather than contrived.
One instance of each, `senderActor` and `receiverActor`, with no arguments. Two connections, both with delay
zero: `senderActor.outOne → receiverActor.incoming` and `senderActor.outTwo → receiverActor.incoming`.

The point of two *different* source ports is that `connectionWellFormed` resolves each source against the
sender's output list, so both connections resolve, in the right direction, with agreeing payloads. Nothing
about the program is degenerate except the one thing under test.

```
F49_CLAUSES_ONE reactorsNonEmpty=true instancesNonEmpty=true reactorsWellFormed=true
                reactorNamesUnique=true instanceNamesUnique=true
F49_CLAUSES_TWO instancesResolve=true instanceArgumentsMatch=true connectionsWellFormed=true
                targetEndpointsUnique=false
F49_PROGRAM_WELLFORMED false
F49_REACTORS sender=true receiver=true
F49_RECEIVER_DECLARED_NAMES incoming  nodup=true
F49_TARGET_ENDPOINTS receiverActor.incoming | receiverActor.incoming
F49_GUARD_REFUSED the translated LF program is not well-formed: two connections target the same
  input port of the same instance, which the LF compiler rejects as a many-to-one connection
```

Those labels are the scratch run's own and not the suite's. As with F48 the witness lived outside the
repository and the labels were renamed when four of these seven measurements were carried in, so grepping
`F49_` returns nothing in the code; unlike F48 the paragraph above never called the block verbatim, which is
the difference between a stale label and the provenance defect recorded as **F51**. The mapping, all in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean`: the eight clauses that hold — `F49_CLAUSES_ONE`
together with the first three values of `F49_CLAUSES_TWO` — are pinned as one string by
`SHARED_TARGET_EIGHT_CLAUSES_HOLD` (`:4376`); the ninth, `targetEndpointsUnique=false`, by
`SHARED_TARGET_UNIQUENESS_FALSE` (`:4391`); the `nodup=true` verdict inside `F49_RECEIVER_DECLARED_NAMES` by
`SHARED_TARGET_RECEIVER_NAMES_NODUP` (`:4385`); and `F49_GUARD_REFUSED` by
`SHARED_TARGET_ISOLATED_REFUSAL` (`:4398`).

Three lines did not land and survive only here: `F49_PROGRAM_WELLFORMED`, `F49_REACTORS`, and
`F49_TARGET_ENDPOINTS`. The last is the asymmetry worth naming, because F48's endpoint list *is* asserted
(`ALIASED_ENDPOINT_TARGETS_COLLIDE`) while this one is not, so the doubled endpoint that gives this finding
its name is visible in the suite only through the clause that fails on it.

**What the gate pins today**, verbatim from a green `frontend/check-general-lean.sh`:

```
PASS_SHARED_TARGET_EIGHT_CLAUSES_HOLD
PASS_SHARED_TARGET_RECEIVER_NAMES_NODUP
PASS_SHARED_TARGET_UNIQUENESS_FALSE
PASS_SHARED_TARGET_ISOLATED_REFUSAL
```

**What that establishes, in order of usefulness.**

1. **`targetEndpointsUnique` is independent of the other eight clauses.** Eight hold and it fails, so it is
   not derivable from their conjunction and cannot be dropped from `wellFormed`. This is a *better* argument
   for keeping the clause than the one F48's entry offers, which was that a construction proof does not exist:
   absence of a proof is an absence, whereas independence is a fact.
2. **The relative theorem, as F48 recorded it, is false.** Not too weak, not unproved — false. Its
   justification is sound and its scope is not: "two connections sharing a target endpoint come from two
   distinct routes into that class" is true of programs the translation assembles and of no others. Written as
   an implication about `LF.GeneralProgram`, it quantifies over programs nobody built.
3. **The receiver being well-formed is the load-bearing half.** `declaredNames` is `[incoming]`, `Nodup` holds,
   and that is precisely what F48's counterexample did *not* exhibit: there the receiver duplicated its input
   port, so both clauses failed together. Two connections can share a target endpoint while the receiver
   declares that port exactly once, and there is no way to see that from a name-level fact.

**The correctly scoped statement**, which is what task #58 will prove: for a program whose `connections` are
`generalConnectionsOf routes` and whose reactor input ports are `generalInputPortsOf className routes` for the
*same* `routes`, `reactorsWellFormed` implies `targetEndpointsUnique`. The argument is the one F48 gave, now
with its hypothesis stated: `generalConnectionsOf` is a `map` over routes, so one connection per route and two
connections sharing a target endpoint are two distinct rows; `generalRoutesIntoClass` filters by receiver class
and two routes to one instance are two routes to one class, so both rows survive the filter; and
`generalInputPortsOf` maps over the filtered list with no dedup, so the shared input port name appears twice in
`declaredNames` and that reactor's `Nodup` conjunct fails. This is a theorem about `compileGeneralModel` rather
than about `assembleGeneralProgram`, because `assembleGeneralProgram` receives `compiledReactors` as an opaque
argument and nothing in its own body ties those reactors to the routes it builds connections from.

The pair of results is the honest account of why the clause exists: **independent in general, redundant on
translation output.** It cannot be removed from `wellFormed`, and it should never fire alone for a program the
translator produced — which is exactly what F48's witness showed, where it failed together with
`reactorsWellFormed` rather than alone.

**The third docstring, which is the part that could have cost a soundness property.**
`Relico/Translation/GeneralRouting.lean:1253` argues that `generalInputPortsOf` needs no deduplication, and
writes the argument out deliberately, *"as an argument rather than leaving as a silence"*. It has two premises
and F48's measurement refutes both. The first — *"a sender instance's output port names are distinct within its
class by step 4 of the environment"* — is what `ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE`
(`reportToToHub | reportToToHub`) disproved: two entries with one name in a single class's port
environment. The second — *"one instance binds one known rebec to one instance, so one (sender
instance, output port) pair contributes exactly one arrow"* — is true of a single
binding and false of the pair, because `bindingsMatchClass` permits two *different* known rebecs to bind to the
same actor, which is exactly the aliasing F48 used. So the conclusion *"two rows with equal input port names on
one class would therefore have to be one row"* does not follow.

What saved it is its last sentence: *"if that argument is ever wrong, the `Nodup` guard says so by name at the
point of failure — which is the reason to rely on the guard rather than on the argument."* That hedge is
correct, and it is why no soundness property was ever at risk. But an argument that deduplication is
unnecessary is precisely the licence a later reader would need to delete the guard clause, and F48's entry
already named that as the load-bearing harm. **Fixed here**: the premises are replaced by F48's counterexample
and the conclusion is restated as resting on the guard alone, so the file no longer contains a refuted
argument for a conclusion it reaches by other means.

**A fourth site, found by fixing the third.** The paragraph above was written saying "the third docstring",
because three was the count when the search that found F48 stopped. Editing `generalInputPortsOf`'s docstring
put `generalConnectionsOf`'s on the screen sixty lines below it, and it says the thing the other three only
imply: *"`targetEndpointsUnique` holds by construction rather than by check"* — flatly, as a fact about the
function, citing `Relico/Translation/NameGeneration.lean:294`'s `inputPortNameFor_outputPort_injective` as the
step that makes it a theorem. This is the most directly refuted of the four, because F48's witness *is*
translation output and its two target endpoints are equal, so a claim about what this function constructs is
contradicted by a measurement of what it constructed.

The cited theorem is true, and the interesting part is how it fails to help. It says one sender's two
*different* output **ports** cannot produce one input port name — injectivity with the sender instance fixed.
The gap is that two routes can share one output port **name**, which is what non-injectivity of
`outputPortNameFor` permits and what `ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE`
(`reportToToHub | reportToToHub`) is. So both wrong sites in this module rest on the same unstated premise,
that a (sender instance, output port name) pair identifies at most one route, and both were written as
though a theorem about names supplied it. **Fixed here too**, on the
same terms: the false claim is replaced by the refutation, the relative statement is written out with its
hypothesis, and the docstring says which module owns it.

That makes **four** mentions across three modules, three of them wrong and all three on *consumers* of the
naming rule, while the module that owns the rule states it correctly. `GeneralBasic.lean:4366` said the routing
cannot produce a repeated target and called the proof deferred; `GeneralRouting.lean:1253` argued the input
ports cannot repeat; `GeneralRouting.lean:1303` said the clause holds by construction. Against them,
`NameGeneration.lean:107` says plainly that the naming rule is not injective, lists both collision channels by
finding number, and concludes that uniqueness is *decided on the program the translation builds*. And two
places in `GeneralBasic.lean` get it right as well — `:135` calls the corollary *"true, but checked rather than
earned by construction"* and names it an instance of the F37 weakening, and `:2416` routes the many-to-one
property through `guardGeneralProgram_wellFormed`. So the repository held both answers at once, in one build,
five documented mentions apart, with nothing comparing them.

The lesson is narrower than "docstrings drift" and worth stating precisely: **the correct statement was on the
definition, and the wrong ones were on its callers.** A reader of `outputPortNameFor` could not have gone
wrong. A reader of `generalInputPortsOf` or `generalConnectionsOf` had no reason to look one module over.
Whatever the fix for this family turns out to be, it has to work in the direction callers actually read.

**The instrument.** Following the convention F47 and F48 adopted, the witness is asserted rather than left in
prose: `frontend/lean-bridge/GeneralLfPrinterTestMain.lean` gains a `sharedTargetAssertions` block with four
labels — `PASS_SHARED_TARGET_EIGHT_CLAUSES_HOLD`, `PASS_SHARED_TARGET_RECEIVER_NAMES_NODUP`,
`PASS_SHARED_TARGET_UNIQUENESS_FALSE` and `PASS_SHARED_TARGET_ISOLATED_REFUSAL` — taking
`EXPECTED_PRINTER_ASSERTIONS` from 82 to 86 and the gate's block enumeration from eight to nine. The fourth is
the reason the block cannot be folded into F48's: it pins the refusal text for the case where **one** clause
fails, and F48's pins it for the case where two do. Together they establish that
`generalProgramExplanation` enumerates exactly the failing clauses, at both ends of its range — which was
measured for the multiple case and, until this run, merely assumed for the singleton.

> **A fifth site, and it is in the first site's own docstring — found in task #58 by landing the theorem.**
> The count above is five mentions, four of them wrong. The new one is the closing paragraph of the very
> comment block whose earlier paragraph F48 repaired: about twenty lines below `:4366` it said *"what
> remains achievable is a strictly weaker relative statement — `reactorsWellFormed` together with
> `instancesResolve` implies this clause"*, which is precisely what F49 then refuted, and it named item 15
> of the list below as its owner. So after F48's fix that one docstring asserted a construction proof was
> deferred in one paragraph and offered a false substitute in another, and after F49's fix it still offered
> the false substitute.
>
> **Two lessons, both narrower and more useful than the count.** First, F48's repair was scoped to the
> paragraph it was reading rather than to the block it was inside; a docstring is the unit that has to be
> re-read after an edit, because a comment cannot be internally inconsistent in the way two comments in
> different modules can. Second, F49's remote verification grepped for `holds by construction rather than
> by check` — the phrasing of the fourth site — and this paragraph makes the same claim in entirely
> different words, so the search was structurally incapable of finding it. **A verification grep anchored
> on one phrasing measures that phrasing, not the claim.** Where the claim cannot be reduced to a label,
> the check is reading the whole block, and that has to be planned for rather than hoped for.
>
> **The lesson paid inside the hour: two more sites, in the design document, found by the search it
> recommends.** Listing every mention of `targetEndpointsUnique` in the repository instead of grepping a
> sentence turned up `docs/STAGE_E_DESIGN.md:633`, which says the clause *"then follows from the routes
> being distinct in `(senderInstance, site)`"*, and `:891`, which owes §10.2 that clause *"from route-key
> distinctness (§7.2)"*. This is a **third** phrasing, and it is the load-bearing one, because route keys
> are precisely what stage E's per-send-site naming makes distinct — while distinct keys do not give
> distinct port *names*, which is what `ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE`
> (`reportToToHub | reportToToHub`) measures. So the family reaches five mentions in code and two in the
> design document as of this addendum — a sixth code site is recorded immediately below. Per closing item 13
> these two are corrected the next time that document is touched rather than rewritten as a side effect of
> a proof commit; the addendum under item 13 names them so the ownership is explicit.
>
> **A sixth site, in a fifth file, and this one is a true theorem with a false gloss.** The same
> whole-repository listing also reached `Relico/Translation/NameGeneration.lean:289`, whose docstring for
> `inputPortNameFor_outputPort_injective` closed by calling that lemma *"the sender-side half of
> `targetEndpointsUnique` being a property of the construction rather than of a check"*. The lemma is true
> and proved on the next line; only the gloss is wrong, and it is wrong in F48's own way. Injectivity is in
> the **output port name**, and F48 measured that uniqueness is already lost one step earlier: `report` with
> `toHub` and `reportTo` with `hub` both spell `reportToToHub`, so two distinct send sites reach this
> function as the *same* argument and injectivity excludes nothing. The composite a construction argument
> would need, `(message, known rebec, site)` to input port name, is the non-injective one. Repaired in task
> #58 by scoping the gloss and pointing at the theorem that does earn the clause — a repair the previous
> five did not need, because there was no true statement in them to keep.
>
> **This is the count's fourth revision, and the revisions are the finding.** Four mentions at F49, five
> when the fifth turned up in an already-repaired block, seven with the design document, eight now. Each
> correction was produced by widening the instrument, never by a check: sentence grep found one phrasing,
> claim-level grep found a second and third, and only listing **every** occurrence of the identifier found
> the sixth — which no phrase-based search could have reached, since it shares no phrase with any other
> site. The durable rule is therefore stronger than F49 stated it: for a claim that can be paraphrased,
> enumerate the identifier and read every hit. A phrase search measures the phrase.
>
> **Fixed in task #58**, which is also what makes the fix checkable: the paragraph now states F49's
> independence result and points at `assembleGeneralProgram_targetEndpointsUnique`, a theorem in the build
> closure, so the docstring's claim is now falsifiable by the compiler rather than by a reader.

---

## F50 — the design document owes a theorem that is false, and the counterexample was already in the test suite

**The claim.** `docs/STAGE_E_DESIGN.md` §10.2 lists among stage E's owed theorems that **"no reaction of
an emitted reactor sets one output port twice."** Its stated argument is short enough to quote whole: *"It
follows from the site being an address (§7.1): two `setPort`s in one compiled body come from two statements
at two indices of one body, so their sites differ, so `outputPortEnvOf` gave them different port names **or
refused**."*

**The premise is true and the conclusion does not follow.** Sites do differ — that part of §7.1 holds, and
it is worth saying because the first refutation drafted here attacked the wrong step. What fails is
*"so `outputPortEnvOf` gave them different port names"*. Distinct sites are distinct *arguments*, and
`outputPortNameFor` is not injective on its arguments: it concatenates message, `To`, capitalized known
rebec and site suffix without escaping the separator, so `reportTo` with `hub` and `report` with `toHub`
both spell `reportToToHub` (F34), and the suffix is empty for a once-sent pair so neither send carries an
ordinal. Two distinct sites therefore receive two distinct arguments and are handed **one** port name.

**The `or refused` hedge does not rescue it.** The refusal is a check on the assembled program, and the
model below *reaches assembly* — it has to route and compile to be a witness at all. What the guard
refuses is the whole program, after the reaction bodies have already been built with the repetition in
them; a refused program is not a program in which no reaction sets a port twice.

**The counterexample needed no new model.** It is F48's, at
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean`'s `aliasedProbeClass`, whose *constructor* body holds
both colliding sends. A constructor that sends externally is compiled into `reaction(startup)`, so one
emitted startup reaction sets `reportToToHub` twice, and
`ALIASED_SETPORT_TWICE_IN_ONE_REACTION` pins that reaction's set-port list as
`"reportToToHub | reportToToHub"`. This is F48's collision seen one level deeper: the same unescaped
separator produces the shared *target endpoint* F48 measured and the doubled *set port* measured here, and
the tenth assertion block reuses F48's model rather than building a second so that a future repair cannot
fix one and silently leave the other.

**Which reaction it is carries the finding.** The colliding sends are in the constructor, not in a message
server, so the reaction that doubles is `startup`. Any restatement of §10.2 scoped to message-server
reactions would be true of this model and would miss the counterexample entirely — which is why the
assertion looks the reaction up by name instead of taking the reactor's first.

**Nothing in `LF.GeneralWellFormed` catches the repetition, and that is the structural half.**
`LF.GeneralReactor.stmtWellFormed`'s `.setPort` arm asks that the port be *declared* on the reactor with a
matching payload arity — not that it be set once. So the doubled body is accepted by every clause that
inspects a reaction, and `ALIASED_SETPORT_REACTION_STILL_WELLFORMED` asserts exactly that, expecting
`true`. This is the same shape as F48's `ALIASED_ENDPOINT_CONNECTIONS_WELLFORMED`: `connectionsWellFormed`
asks that an endpoint be declared, not declared once. Both are the neighbouring clause that still holds,
and both exist to keep the attribution narrow — F48's model is refused, but it is refused by
`declaredNames` and by the connection list, never by the body that does the doubling.

**What replaces the owed theorem.** `Translation.compileGeneralBody_setPortNames_nodup` in
`Relico/Translation/GeneralBasic.lean` proves the guard-relative version: **if** the routing table gives
distinct sites of one body distinct output port names, **then** the compiled body's set-port list is
`Nodup`. The hypothesis is stated over sites of one `bodyKey` rather than as `Nodup` of the whole
environment, because that is all the induction consumes and it is the form a caller holding a per-class
guard can supply. `LF.setPortNamesOfBody` is the list the statement is about, and it preserves repeats on
purpose — a `filterMap` composed with a dedup could not express the property at all.

So this property joins `targetEndpointsUnique` in the category F48 and F49 established: **earned by a
check on generated names, never by the naming rule.** That is now three of stage E's port-level guarantees
with the same provenance, and the pattern is worth stating as a design fact rather than rediscovering it a
fourth time.

**Why this instance is not F44's or F47's root cause.** Those were docstrings claiming that coverage
existed. F48 was a docstring claiming a *theorem* was deferred when it was false. This one is a **design
document** listing an obligation that cannot be discharged — and the difference matters operationally,
because a docstring is read by whoever edits the function while a design document's owed-theorem list is
read by whoever plans the next commit. An impossible entry on that list does not merely mislead; it
schedules work that will fail, and it did: §10.2 is where task #60 came from.

**Disposition, and what is deliberately not done.** The guard is *not* strengthened and the port-naming
rule of P20 is *not* reopened; P20 is settled and `lfc`-accepted, and the collision is refused rather than
prevented by design. §10.2's own text carried the false argument when this entry was written; it and §7.2
were both corrected in the commit that added F53, which closing item 13 records as the touch it was waiting
for. This entry is the pointer that convention relied on, and the convention paid out. §10.2's
reachability obligation for a class that sends one message twice to one rebec is unaffected by any of this
and remains task #51's.

---

## F51 — a findings file called a transcript verbatim after its labels were renamed, and three citations then treated them as instruments

**Grade: measured**, by enumeration rather than by a run: every `F<number>_<LABEL>` string in `docs/` was
listed and read against the code, and every value in the two evidence blocks was compared against the
expected literal it corresponds to in `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`.

**The defect.** F48's entry introduced its evidence block as *"**What ran**, verbatim from the `#eval`
output"*. The block is real output, but not of anything that still exists: the witness was a scratch file
kept outside the repository, and its seven `F48_*` labels were renamed to `ALIASED_ENDPOINT_*` when four of
the measurements were carried into the suite. So *verbatim* asserted a provenance the block did not have, in
the one file whose worth depends on provenance being checkable.

**What the defect is not, recorded because the first diagnosis was wrong.** Task #61 initially concluded the
block was fabricated — that three of its lines were invented and that it claimed more assertions than exist.
That was a mis-diagnosis, and the reasoning behind it is worth writing down because it is this file's own
error running in the opposite direction. The argument was *"no `F48_` label exists in any `.lean`, `.sh` or
`.py`, therefore the labels are invented"*. But both entries state that their witness lived **outside** the
repository precisely so no untracked Lean would land in the tree, so absence from the repository is exactly
what the stated method predicts. Absence is evidence of fabrication only where the method claims presence.

The values are corroborated line by line. `reportToToHub | reportToToHub` is the expected literal at
`GeneralLfPrinterTestMain.lean:4148`; the doubled target endpoint is the literal at `:4153`; the two-clause
refusal text is the literal at `:4161-4165`; `targetEndpointsUnique=false` is asserted at `:4179-4182` and
`connectionsWellFormed=true` at `:4184-4187`. The five conjunct names in `F48_SOURCE_CONJUNCTS`, which land
nowhere, are corroborated by the comment at `:4139-4140` stating that all five conjuncts of
`DTR.GeneralModel.wellFormed` hold, aliasing included. F49's block corroborates itself internally: its prose
promises seven `#eval`s and enumerates them, and the block carries exactly seven labels matching that
enumeration one to one. **So the measurements stand and the findings resting on them are safe; what was false
was the sentence introducing them.**

**How it propagated, which is the part that cost a reader something.** Three passages in F49's entry cite
`F48_OUTPUT_PORTS` in the present tense — *"is what … disproved"*, *"what … is"*, *"which is what …
measures"* — so each reads as a live instrument. A reader following F47's own rule, grep the named term, gets
zero hits and correctly concludes the instrument does not exist. One of the three was written during task
#58's repair of the fifth site of the F49 family, which is to say while explicitly fixing this class of
defect.

**The fourth stale range literal, found by the same census.** This file states its own range or count in four
places: the title, the *"eighteen findings"* sentence, the *"numbered F34 through …"* sentence, and the
sentence *"this file is what makes F34–… citable"*. F50 landed in commit `f9f241e` having updated the first
three and not the fourth, which read `F34–F49` while F50's own entry sat in the file. That is a fourth
occurrence of the family F45 and F46 record; it happened in the commit that made it stale; and it happened
despite the general rule stated at the end of F46. The rule was honoured for the literal a check reads and
forgotten for the three that no check reads.

**What was done.** Both blocks are relabelled as superseded scratch runs, and each is followed by a mapping
from scratch label to landed label giving the source line of every landed assertion, so every surviving line
is either greppable or explicitly marked as surviving only here. Each block gains a second block of the
`PASS_` lines the gate actually prints. The two are not redundant and neither replaces the other: the `PASS_`
lines prove the assertions exist and passed, while the values they compare against are auditable only by
reading the `expectString` and `expectBool` literals, because the runner emits one bare label per assertion
and no values. The three citations now name `ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE`. The fourth range
literal is corrected and now carries a pointer here. A dead `<!-- F49_BODY_MARKER -->` anchor, referenced by
nothing in the repository, is removed. Six lines across the two blocks are marked as landing nowhere; the
weakest is `F48_DECLARED_NAMES`, which no landed assertion and no comment corroborates.

**The rule this adds**, beside F46's rule about numbers stated in more than one place: **a transcript is
evidence about what produced it, so the sentence introducing one is itself a claim, and it has to be true of
the artifact that still exists.** Renaming a label while landing an experiment is ordinary; leaving prose
that says the old labels are what ran is not. And the corollary the mis-diagnosis earned: **where a claim's
own stated method predicts a string will be absent, absence does not test the claim** — corroborate the
values instead, which is cheap here because the suite keeps its expected literals in the source.

**What is deliberately not done.** No assertion is added to cover the six lines that survive only in prose.
The clause-by-clause scoring and the `declaredNames` lists were exploratory, and asserting them now would pin
implementation detail no finding rests on; they are marked unasserted instead, the same disposition F47 item
14 took for refusal causes no fixture reaches. Line numbers into *this* file are also deliberately avoided
above, since an entry that shifts its own citations is the failure mode this entry is about.

---

## F52 — the design document asks for a checklist that cannot exist, and the file answering it claims to have over-delivered

**Grade: measured by evaluation.** The refutation below is an `#eval` against the built package, not
an argument. The two docstring readings are quotations with line numbers.

**The claim.** `docs/STAGE_E_DESIGN.md` §8 (`:767-772`) owes *"a sufficient condition for
acceptance. A decidable predicate over DTR models — no arity-zero external send, no colliding
generated names, and DTR well-formedness — that implies `.ok`."* It is careful to say the condition
is deliberately sufficient and not necessary, and that saying so in the theorem's docstring *"is the
difference between an honest lemma and stage D's biconditional overreaching."*

**The claim is false as worded, and the cheapest possible model refutes it.** `DTR.GeneralModel`
(`Relico/DTR/GeneralSyntax.lean:436`) has exactly two fields, `classes` and `instances`. Take both
empty. All three conjuncts hold: `DTR.GeneralModel.wellFormed` is exactly five conjuncts
(`Relico/DTR/GeneralWellFormed.lean`), every one of them a statement over a list that is now empty,
and the other two conjuncts hold vacuously because a model with no classes has no external send to be
arity-zero or to generate a name that could collide. But `LF.GeneralProgram.wellFormed`
(`Relico/LF/GeneralWellFormed.lean:538`) is **nine** clauses, and its first two are
`reactorsNonEmpty` (`:376`) and `instancesNonEmpty` (`:387`). The guard refuses. Predicate true,
acceptance false.

**What ran.** The block below is the output of a scratch witness kept deliberately *outside* the
repository, so that no untracked Lean landed in the tree, elaborated against the built package with
`lake env lean` and exiting 0. Its `F52_` labels therefore exist nowhere in the code, which is what
the method predicts and not evidence of anything — the reason that sentence is here at all is **F51**,
which records what happens when a block like this one is introduced as a verbatim transcript instead.

```
F52_MODEL_WELLFORMED true
F52_CONJUNCTS bindings=true arguments=true sendTargets=true sendsResolve=true names=true
F52_ROUTES OK routes=0
F52_COMPILE ERROR the translated LF program is not well-formed: no reactor is declared; no instance is declared
```

Three things this pins that an argument could not. `F52_ROUTES OK` locates the refusal: routing
**succeeded**, so the refusal is the guard's and not an earlier stage's. The refusal text names
**both** failing clauses rather than the first, independently reproducing the measurement F48 made
about `generalProgramExplanation`. And the five conjuncts are reported separately, so "DTR
well-formedness holds" is not being inferred from a single `true`.

**The counterexample is legitimate by §8's own standard**, which is what raises it above pedantry.
§8 (`:707-710`) justifies keeping the translation's defensive `.error` arms on the ground that *"the
translation is a total function on the *type* and not only on frontend output."* A predicate over
`DTR.GeneralModel` is therefore a predicate over the type, and the empty model inhabits it. §8 sets
the standard by which its own claim fails. Nor is the degenerate model the only witness: one class
with zero instances fails `instancesNonEmpty` identically, so the missing conjunct is non-emptiness
and not an artefact of the empty list.

**Adding non-emptiness does not rescue the wording, and this is the part that matters.** The conjunct
*"no colliding generated names"* is not a property of a DTR model that can be read off the model.
Port names are manufactured by `outputPortNameFor`, which concatenates message name, `To`, the
capitalized known rebec and a site suffix, and which **is not injective** — F34 records the unescaped
separator and F42 records `capitalizeName` folding case, two independent collision channels. So
whether a model's generated names collide can only be decided by *running the generator*. The
predicate §8 asks for must therefore reference the resolution pipeline, and §8 forbids exactly that
one sentence earlier, on the ground that *"a faithful characterising predicate would be a mirror of
the resolution pipeline, and a mirror is the shape of defect this development keeps finding."*

§8 thus demands a source-side predicate **and** forbids pipeline reference, and F34/F42 make those two
demands jointly unsatisfiable for this conjunct. The demands are not equally wrong, though, and the
distinction is worth keeping: what §8 was right to fear is **duplication**, because a re-implementation
of the pipeline's logic can drift from the pipeline. Naming the pipeline's own stages by **reference**
cannot drift, because there is only one implementation. That distinction is what leaves a real theorem
available, and it is recorded here because the section's wording collapses the two.

**Two docstrings in one file disagree about whether the ask was discharged.** This is F48's shape
again, and the second of them is mine.

- `Relico/Translation/GeneralBasic.lean:4259-4262` says the sufficient condition *"is deferred whole
  to the task this file's header records as the site-totality obligation"*, and gives as its reason
  that the condition *"rests on an induction showing that every external send site of a class has an
  entry in that class's resolved environment."*
- `Relico/Translation/GeneralBasic.lean:4654-4655` says *"§8 asks for a sufficient condition for
  acceptance. What comes out is *totality*"*, and that the proof *"buys more than the design asked
  for."*

**`:4654` is the wrong one.** `exists_compileGeneralReactiveClasses` (`:5272`) has hypothesis
`∀ reactiveClass ∈ classList, ∃ env, outputPortEnvOf allClasses reactiveClass = .ok env` and
conclusion `compileGeneralReactiveClasses … = .ok`. So it **assumes** that the resolution stage
already succeeded — which is part of what §8's conjuncts were meant to *deliver* — and it concludes
about the middle pipeline stage only. `compileGeneralModel` (`:2444-2467`) is `routesOf`, then
`compileGeneralReactiveClasses`, then `guardGeneralProgram` applied to the assembled program, so the
totality result stops one stage short of the guard and says nothing about it. Totality and §8's ask
are **incomparable**, not ordered, and the same file makes precisely that incomparability argument
correctly about the *other* owed statement at `:4249-4253` (*"The two are not comparable, and the
trade was deliberate"*) four hundred lines earlier.

`:4261`'s stated *reason* for deferring is wrong as well, and it is now stale in a way that proves it:
that induction **landed** at `efef73a`, so if the condition really rested on it the condition would
now be provable. It is not. What it actually rests on is the guard — `declaredNames.Nodup` and
`targetEndpointsUnique`, which F48 and F49 measured as failing on source the DTR layer accepts — and
site totality is not about names at all, as `:4674-4677` states in its own words: *"Nothing in this
section is about port *names*."* A deferral that names the wrong instrument is the same defect F48
recorded, one layer up.

**What the right theorem is.** §8's own title — *"Totality, and where each refusal lives"* — is a
better description of the available result than the checklist its body asks for. Acceptance factors
into exactly three conditions: the model is non-empty, name resolution succeeds for every class, and
the guard passes; and **nothing between them can fail**, which is where the site-totality induction
earns its keep. Stated as a biconditional this replaces stage D's deleted
`compileGeneralModel_ok_iff_selfSendOnly` with a stronger statement rather than a weaker one, and it
localises the refusal surface to two sites, which is what a reader wants from a fragment boundary.

The guard hypothesis is not an apology in that statement — it is this finding's positive content.
**No sufficient condition for acceptance can omit the guard**, because F32 and F43 established that
the guard genuinely refuses legal DTR models, and F34 and F42 established that its refusal is not
predictable from the source model without generating names.

**What was done.** This entry, §8's wording, and both docstrings. The theorem is deliberately *not*
part of the same change: the record is straightened first, so that the false docstrings do not sit in
the tree while a proof is written, which is how F48 and the theorem that replaced it were sequenced.

**What is deliberately not done.** `DTR.GeneralModel.wellFormed` is **not** strengthened to require
non-emptiness. It is the frontend's contract, an empty model is not malformed, and widening a
well-formedness predicate to make a downstream theorem convenient is the inversion of the discipline
this file exists to enforce. The refusal stays where it is, in the guard, which is the layer that
knows LF's requirements.

## What is left open, and who owns it


Ordered by what blocks something later, not by finding number. Each item names the experiment or reading
that would close it, so that no entry here can be closed by argument alone.

**1. The same-tag ordering measurement, which stage F needs.** `GENERAL_LF_TARGET_OK` compiles and runs a
three-reactor generated program, and `Gateway`'s five reactions are declared in an order that the
2026-08-17 probe showed to be observable — but its two port reactions fire at 0 msec and 3 msec, which are
*different tags*, so time order decides and declaration order is never consulted. The gate therefore
proves the generated declaration order **compiles**; it does not exercise a race. The paper's §III-D
ordering claim over *generated* text is still unmeasured, and what would settle it is a fan-in fixture
whose sends share a tag. Stage F cannot claim its ordering result until this runs.

**2. Two `schedule()` calls on one logical action at one tag** — pending task #39, and owed by stage D's
*landed* self-send path rather than by stage E. `self.tick(); self.tick();` already emits two
`tick_action.schedule(0ms)` calls in one reaction and no committed fixture exercises it. This is the
action-side analogue of the hazard **F40** found on the port side, and F40's requirement explicitly
allows two invocations of one action — so if this loses an event, F40's redesign rests on a false
distinction. Probe section 12, together with `policy: defer`.

**3. The preservation theorem's hypothesis** — pending task #47. **F32** says the theorem is false as
stated, **F43** says the guard converted the counterexample into a refusal rather than repairing it, and
the choice stage E deferred is between (a) an explicit extra hypothesis on the theorem and (b) a proof
that the elaborator's guarantee implies the LF-side `Nodup`. The instruction to "add the DTR mirror
clause" is **retracted**: it would duplicate `Relico/Frontend/GeneralElaborator.lean:793–796` and collapse
a layer partition that three docstrings state deliberately. Whichever branch is taken must say why.

**4. F44's missing assertions** — assigned to task #45, which already owns every count that moves with the
stage E fixtures, so `EXPECTED_PRINTER_ASSERTIONS` and the `runGeneralLfPrinterTests` docstring move once
rather than twice. Until it lands, `NameGeneration.lean:214–217` is making a false statement about the
test suite, which is the one kind of debt that hides itself.

> **Closed** — see the addendum under F44. This item is kept rather than deleted because the closing
> section is ordered by what blocks something later, and an item that vanishes leaves no record that the
> ordering was ever load-bearing.

**5. What the paper actually says about the send rule and where the delay goes.** This reading decides
whether **F35** becomes a `P`-series correction in `docs/PAPER_CORRECTIONS.md` or stays a repository
finding. Same document, and therefore the same sitting, as item 6.

**6. Fig. 5's `ActionDecl` production, owed since stage D to settle F26.** Grouping it with item 5 costs
nothing extra. Both are reads of the PDF at
`~/Desktop/LFStructuringNonDeterminism/DTR_LF__After_FMCAD_.pdf`, which is **outside** the repository and
is never edited as a side effect of anything.

**7. F31's paper fault, still not filed as a `P` entry** — owed from stage D's closing list. F31 is the
named-instance-arguments divergence; note the numbering trap, since an older note called F32 "F31".

**8. F38's experiment**, which needs the Java exporter and therefore Maven on the Mac, through
`frontend/java-bridge/check-general.sh`. It shares that requirement with pending task #36 — the `reject/`
fixture for a constructor formal shadowing a state variable — so the two travel together in one Maven
round trip. F38 is the only **inferred** finding in this file, and nothing rests on it.

**9. F41's real fix: a well-formedness clause quantifying over every declaration of a struct name.**
Unreachable from the translation today, so this blocks no current output; what it blocks is any claim that
a hand-built `LF.GeneralProgram` is checked. The printer is the wrong layer and says so.

**10. Is a payload-free port declaration legal?** §11.2 item 1, with its prediction already fixed: the bare
typeless form is rejected — the probe log already contains `Input must have a type.` — and `: void` is
accepted and compiles. If the second half holds, **F36**'s arity-zero refusal becomes a translation and
`GeneralPortPayload` gains a constructor. Confidence high on the first, moderate on the second.

**11. Does `p.set({a, b, c})` compile without naming the struct?** §11.2 item 2. Not needed by this design;
it would remove the printer's dependency on the port's stored payload and so would weaken **F37**.
*Prediction: ambiguous overload resolution, so no.*

**12. Splitting `LF.GeneralReaction.parameters`**, owed from stage D's closing list "in the next stage that
rewrites those sites". Stage E rewrote port sites, not those.

**13. Documentation hygiene, listed last because it is the easiest to defer and the least costly to miss.**
`docs/STAGE_E_DESIGN.md` §11.1 still describes **F36** as an open gap, though as landed it is closed by
construction, and still carries the *"provisional until the findings file lands"* warning that this file
discharges. Both should be corrected the next time that document is touched, with a pointer here rather
than a rewrite of its history — the same convention F40 relies on.

> **Two further corrections for that document, added in task #58, and they are not the same kind of debt as
> the two above.** `:633` states that `targetEndpointsUnique` *"follows from the routes being distinct in
> `(senderInstance, site)`"*, and `:891` owes §10.2 that clause *"from route-key distinctness (§7.2)"*. Both
> rest on the step F48's witness refutes, so this is a refuted **argument** presented as the design's
> reason, not bookkeeping that fell behind. When that document is next touched, the justification should be
> replaced by a pointer to `Translation.assembleGeneralProgram_targetEndpointsUnique` and to the fifth-site
> addendum under F49, and the hypotheses should be stated as they actually are: one shared `routes`, routes
> agreeing on an instance's class, and reactor input ports built from those same routes.
>
> It is filed here rather than fixed because the convention forbids rewriting that document as a side
> effect of a proof commit — **not** because it is cosmetic. Recording the distinction matters: this item is
> named "documentation hygiene", and if it silently accumulates refuted arguments alongside stale counts,
> its position last in a list ordered by what blocks something later stops being right.
>
> **All four corrections landed 2026-08-22, in the commit that added F53 — the touch this item was waiting
> for.** §11.1's F36 bullet and its *provisional* warning each carry a dated blockquote; §7.2's *"carried by
> construction"* sentence and §10.2's *"from route-key distinctness (§7.2)"* clause each carry one naming
> `assembleGeneralProgram_targetEndpointsUnique` and the guard's name check as what actually discharges
> them. Two notes on the citations above. `:633` was still accurate; **`:891` was not** — the clause it names
> sits in §10.2's owed-theorem paragraph, and the design's line numbers had moved under it. It is left as
> written, per the same pointer-not-rewrite convention, and F53's closing paragraphs are the pointer. The
> reason it went unnoticed is worth carrying forward: the quoted phrase *"route-key distinctness"* **wraps**
> in the design, so grepping it to re-find the line returns nothing at all, and a check that returns nothing
> looks like a check that passed.

**14. F47's six unasserted refusal causes.** Two of the eight causes in F47's table have their message text
asserted; six do not. The closing instrument is not an argument, it is six `expectString` assertions in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean` against hand-built models — the same shape as the two
that exist, and available for all six precisely because a hand-built `DTR.GeneralModel` need not satisfy
`wellFormed`, so the four causes that the frontend makes unreachable are still reachable there. The
alternative is a written, per-cause record that the branch is unreachable and deliberately untested; that is
acceptable for the bindings group and **not** acceptable for the arity-zero payload cause, which is a
restriction on the accepted fragment and is reachable from a document the frontend accepts. Either way it
moves `EXPECTED_PRINTER_ASSERTIONS` and the two docstrings that state the breakdown, so it is its own task
and must not be folded into a fixture commit. Blocks nothing; the reason to do it soon is that F47's table is
the only place the mapping from cause to text currently exists.

> **Closed in task #56** — see the addendum under F47 for the six labels and the gate evidence. Kept, not
> deleted, because this list is ordered by what blocks what. Two corrections to the item as written. The
> instrument is `expectRefusedTerm`, not `expectString` directly: it takes the `Except` value, fails if it
> is `.ok`, and delegates to `expectString` on the diagnostic, so a refusal that stopped being a refusal
> fails differently from one whose text drifted. And the escape hatch this item offered was not taken for
> any of the six, including the bindings group where it was permitted — the models cost about a dozen lines
> each, being one-field structure updates on `routedModel`, and a written record of deliberate untestedness
> would have been another prose claim about the suite, which is the failure this whole family is about.

**15. The relative endpoint-uniqueness theorem, which F48 leaves as the only achievable form of the proof
`:4366` had deferred.** Statement: for the program `assembleGeneralProgram` builds, `reactorsWellFormed`
together with `instancesResolve` implies `targetEndpointsUnique`. The argument to formalise is a counting
one and does not need site totality: two connections sharing a `(targetInstance, targetPort)` arise from two
distinct routes into the receiving class, `generalInputPortsOf` maps over exactly the routes into that class
with no deduplication, so the shared port name occurs twice in that reactor's `inputPorts` and hence twice in
its `declaredNames`, contradicting `Nodup`. The closing instrument is a Lean proof, not a run, and the
obstacle is that `eq_of_nodup_map` is `private` at `Relico/LF/GeneralWellFormed.lean:562`, so this needs its
own copy — the same obstacle §10.2's per-reaction `setPort` `Nodup` faces, which is why the two belong in one
task. **This is strictly weaker than what `:4366` promised and that is the point:** it derives one guard
clause from another rather than from the construction, so it does *not* license retiring the clause, and any
future attempt to strengthen it to a construction proof is refuted by F48's witness before it starts. Blocks
nothing; worth doing because it converts a nine-clause predicate's redundancy from a belief into a theorem.

> **Closed in task #58** — the theorem is `Translation.assembleGeneralProgram_targetEndpointsUnique`, with
> the route-level induction `generalRouteEndpoints_nodup` behind it. Kept, not deleted, for the same reason
> as items 4 and 14. **Three corrections to the item as written, and the first is that its statement is
> false.**
>
> `reactorsWellFormed` together with `instancesResolve` does **not** imply the clause: F49's own witness
> satisfies both, and all six other clauses, and fails this one. The counting argument the item gives is
> sound; what it got wrong is what indexes it. `instancesResolve` cannot close the gap because a target
> endpoint pairs an *instance* with a port name while input ports are declared on a *class* — resolution
> says the class exists, not that two routes into one instance were filtered into one reactor. The landed
> hypotheses are that both sides are built from the **same** `routes`, that those routes agree about which
> class an instance has, and that each receiver class has a reactor whose `inputPorts` are
> `generalInputPortsOf` of those routes. The first is what `assembleGeneralProgram` cannot know, since
> nothing in its body relates its `compiledReactors` to its `routes`; the last two are discharged by
> `routesOf` and `compileGeneralReactiveClasses` respectively, and are named in the theorem's docstring as
> residue rather than left silent.
>
> **The predicted obstacle was the wrong one.** `eq_of_nodup_map` being `private` never arose — no step of
> the proof needs it. The gap Lean core actually leaves is that `Nodup` of an append does not restrict to
> either side, so `nodup_of_append_left` and `nodup_of_append_right` are hand-rolled here for exactly the
> reason `eq_of_nodup_map` is hand-rolled there. They are needed because `declaredNames` is five appended
> lists and the input port names are the second of the five.
>
> **Therefore the reason this item gave for bundling §10.2's per-reaction `setPort` `Nodup` into one task —
> "the same obstacle" — is void**, and §10.2 is now its own task with its own prediction recorded before
> any proof attempt. One further method note worth keeping: the `wellFormed` clause is projected out by
> contradiction (assume the negation, and the `&&` chain collapses to `false`), which depends on neither the
> clause's position in the chain nor how the chain associates, so it survives edits to `wellFormed` that a
> positional projection would not.

---

## F53 — three "by construction" claims outlived the findings that refuted them, and the load-bearing one licensed dropping a refusal

**Grade: read, over a refutation that was already measured and already in the repository.** F48, F49 and
F50 each established that a guarantee stage E claims by construction is in fact bought by a check on
generated names. Each repaired the passage it was about — a docstring in
`Relico/Translation/GeneralBasic.lean`, an entry in this file — and none of the three swept the design
document for the same claim stated somewhere else. At `be50578`, `grep -n "by construction"
docs/STAGE_E_DESIGN.md` returned three hits and every one of them was either false or true for a reason
the design does not give. That command is the core of this finding, and it is the command that none of
the three closing commits ran. (The count is **not** a live invariant and must not be maintained as one.
It also did not move: re-measured with the corrections below in the working tree, `grep -c` still returns
three, and the reason it does is worth a paragraph of its own at the end of this entry. What is invariant
is that every hit is now dated and answered.)

**Hit one — §7.2 at `:633–639`.** *"`targetEndpointsUnique` then follows from the routes being distinct
in `(senderInstance, site)` … That is the point of the site key — under the old (rebec, message) key two
sites collapsed to one port and uniqueness had to be bought with a deduplication step and a delay
refusal; now it is carried by construction."* **False.** F48 exhibits a model
`DTR.GeneralModel.wellFormed` accepts whose routes are distinct in `(senderInstance, site)` and whose
connections still land twice on `hubActor.reportToToHubFromProbe`, because `outputPortNameFor` does not
escape its separator. F49 then measured the clause to be *independent* of the other eight, so nothing
in the construction implies it and no implication between clauses can supply it either. The strongest
true statement is `assembleGeneralProgram_targetEndpointsUnique`
(`Relico/Translation/GeneralBasic.lean:4560`), which derives the ninth clause from the third on programs
whose ports and connections come from one routing table — one guard clause from another, not from the
construction.

**Hit two — §11.2, in the *not owed* note.** *"Note also what is **not** owed: the corresponding
question for ports, what a second `set()` on one port at one tag does, is now unreachable by construction
(§10.2), so it stays unmeasured on purpose."* **The conclusion survives and the reason does not.** F50's
witness is one
emitted `reaction(startup)` that sets `reportToToHub` twice, so a second `set()` on one port at one tag
is reachable — from a DTR-well-formed model, through routing, through class compilation, into an
assembled program. It stays unmeasured because the guard refuses that program before any LF is emitted,
which is a different fact with a different failure mode: it depends on a clause continuing to run,
whereas *unreachable by construction* would not. This is the F45/F46 shape once more, a true sentence
resting on a false reason, and it is the reason that a later reader would rely on.

**Hit three — §11.3, decision 3, and this one is load-bearing.** *"…and with that the
'refuse when they coincide' half needs no refusal at all: coincidence on one port is structurally
unreachable (§6.2, §10.2). Both halves of the answer are therefore honoured, one by translation and one
by construction."* **Coincidence on one port is reachable, and it is what the assertion measures.**
`ALIASED_SETPORT_TWICE_IN_ONE_REACTION` pins the set-port list of that startup reaction as
`"reportToToHub | reportToToHub"`; both sends sit in `aliasedProbeClass`'s constructor, both carry delay
`⟨0⟩`, and `outputPortNameFor` maps their two distinct sites to one name because `reportTo` with `hub`
and `report` with `toHub` spell the same string (F34). That is exactly the configuration §6.1 calls
broken: two `set()` calls on one port inside one reaction at one tag, where the receiver's reaction
fires once and a message is lost or the runtime errors, *"and both are wrong."*

**What is and is not being claimed about the user's answer.** The instruction was *implement it when the
delays differ, refuse when they coincide*, and the coinciding case **is** refused — the program never
reaches `lfc`. So the answer is honoured. What is wrong is the design's account of the mechanism: the
refusal comes from `declaredNames.Nodup` in `LF.GeneralReactor.wellFormed`, carrying a diagnostic about
colliding *names*, and site keying closed only the route the section was thinking about. Keying on the
send site removes pair collapse; it does not make two sites unable to share a port name, because the
sites are arguments to a non-injective function. So the sentence should read *one by translation and one
by a check on generated names* — which is the same guard-relative shape as F37, and the shape every
stage E port-level guarantee has turned out to have.

**Why the third hit matters beyond its wording.** F48 records that this very clause was once proposed for
retirement: an earlier docstring on `compileGeneralModel_targetEndpointsUnique` said a construction proof
*"would … therefore let the guard's clause be retired as dead."* Hit three is a sentence in the design
document that would have supported exactly that reading — it says the hazard is structurally unreachable,
and a hazard that is structurally unreachable needs no clause. Retiring it would have replaced a refusal
with emitted LF in which a message is silently dropped. The two documents were one step from agreeing on
a change that loses messages, and the only thing standing in the way was a measurement neither of them
cited.

**Why all three survived.** Each of F48, F49 and F50 was closed by a commit that edited the declaration
the finding named and this file. The design document was treated as the *source* of each claim rather
than as a place claims are also *repeated*, and §8's precedent shows the convention existed: its first
owed statement carries a `> **Discharged 2026-08-21.**` blockquote and its second a
`> **Refuted 2026-08-22 — finding F52.**` one. Both were added by the task whose section that was.
Neither task looked one section over. (Those two were cited by line number in the draft of this entry,
and the citations were correct against `be50578` and wrong by eleven lines by the time this entry landed,
because the §7.2 blockquote below sits above them. The design's line numbers move under exactly the edits
these findings make — the next commit shifts §11 again — so its citable unit is the **section**, and the
line numbers kept below are only the ones no pending edit sits above.)

**A fourth site, and the same omission in its plainest form.** §10.2 is where the design *asks* for the
theorem F50 refuted. F50 recorded the refutation in this file and on the guard-relative theorem that
landed in its place, and left the request itself unmarked — so the document still asks, in its own list of
owed theorems, for a sentence its own repository has a counterexample to. That is not a *by construction*
claim and so it is not one of the three hits, but it is the same movement: the finding repaired what it
was looking at.

**What was done.** Seven dated blockquotes in `docs/STAGE_E_DESIGN.md`, following §8's two precedents — the
original text kept, so the record of what was believed stays legible. Three answer the three hits: §7.2,
§11.2's *not owed* note, and §11.3's decision 3. One marks §10.2's `setPort` paragraph refuted, which is
the fourth site described above. Three more discharge corrections this file had already filed and deferred
to "the next time that document is touched" — §10.2's owed-theorem clause, §11.1's *provisional* warning
and §11.1's **F36** bullet — and the last two paragraphs of this entry explain how they surfaced. No new
assertion is
added, and that is deliberate: the witness this finding rests on already runs on every gate as
`ALIASED_SETPORT_TWICE_IN_ONE_REACTION` and `ALIASED_SETPORT_REACTION_STILL_WELLFORMED`, so F53 is
checked rather than merely described. Adding a second assertion for the same reaction would inflate the
count invariant of `frontend/check-general-lean.sh` for no new coverage.

**The rule this finding leaves behind.** When a finding refutes a claim, grep the *claim's wording*
across every tracked document before closing the task — not only the passage the finding cites. The
phrase is usually short and usually repeated, and one `grep` costs nothing next to the cost of a
document that argues against a check the code depends on. The three phrasings here differ in every
respect except the words *by construction*, which is what made them findable at all and what makes the
sweep cheap enough to be unconditional. The instrument is less reliable than that argument makes it
sound, though, and the last paragraph of this entry is about how it fails.

**The sweep was run, not just prescribed.** Over every tracked `.md`, `.lean`, `.sh` and `.py`, the same
phrase turns up in many more places and all of them are sound. Three are the repaired sites and say the
opposite of the design's claim in as many words — `Relico/Translation/NameGeneration.lean:292` (*"It does
not say the sender side of `targetEndpointsUnique` holds by construction"*),
`Relico/Translation/GeneralRouting.lean:1318` and `:2889`. The rest concern other properties, and one is a
fixture note about a collision being guaranteed by reusing an identifier rather than by two spellings
agreeing, which is the phrase used correctly. One unrelated item surfaced and is filed rather than
addressed here: `docs/STAGE_D_FINDINGS.md:185` names a measurement stage E must take before the printer's
payload refusal can be called unreachable by construction, and that measurement has not been taken.

**The instrument this entry prescribes has a hole, and the hole hid a site that was owed to this very
commit.** `grep` is line-oriented and prose wraps, so a two-word claim whose wrap falls between the two
words is invisible to every search for it. Re-running the sweep with a wrap-tolerant matcher —
`by\s+construction` against whole file contents rather than line by line — turned up two occurrences that
no line-oriented grep in this project has ever seen. One is sound: `Relico/LF/GeneralSyntax.lean`, in the
`GeneralPortPayload` docstring, says that a guarantee which *used to* hold by construction now holds by
predicate, which is **F37** stated correctly and in the past tense. The other is `:1444` of this file —
item 13 of the closing *What is left open* section — and it was owed to whoever next touched the design
document. There is a
third level to the same trap, and it is why the design's phrase count did not move across this commit:
when the wrap falls inside a blockquote or a list item, Markdown puts `>` or indentation at the head of
the continuation line, so even `by\s+construction` does not span it, and the §11.2 blockquote this commit
adds is exactly that shape. The wrap-proof instrument is to match the rarer **single** word and read the
hits, or
to strip continuation prefixes and join lines before matching; the single-word search finds strictly more
sites than the phrase search in both of these files, and the difference is exactly the wrapped occurrences
plus the unrelated uses of the word. No count is given here on purpose — the numbers move with every
reflow, and a number in this paragraph would be the very defect F46 records. Two of this commit's own
blockquotes wrap the phrase, which is why the design still answers *three* to a phrase grep after seven
corrections were added to it.

**What item 13 asked for, and the rule it leaves behind.** It asked that §11.1's description of **F36** as
an open gap and its *"provisional until the findings file lands"* warning both be corrected "the next time
that document is touched", by pointer rather than rewrite. This commit is that touch, so both corrections
are in it — and F36 is closed for a reason worth stating precisely, because the two halves of it are not
equally strong: `LF.GeneralPortDecl` no longer has the `declaredType : LF.GeneralType` field the bullet
names, its `payload : LF.GeneralPortPayload` carries a `struct` constructor over
`List LF.GeneralTypedParameter` so the parameter types survive the crossing, and there is no `void`
constructor, so an arity-zero external send is *unrepresentable* rather than mistyped. That last one is
closure by construction in the strong sense the rest of this entry says the design does not earn. What
remains guard-relative in that layer is the struct's *name*, stored at both ends and checked — and that is
F37, not F36. The rule: a correction deferred to "the next time X is touched" fires on the toucher, not on
its author, and nothing in this repository enforces such a trigger. It fired here only because a
wrap-tolerant sweep re-read the file that defers it. Deferred corrections of that shape must therefore be
recorded *at* X, which is what putting these two in §11.1 rather than only citing them here achieves: the
next reader of §11.1 finds the correction in place instead of needing to be lucky.

**One list item, two deferrals, and a broken pointer inside the second.** Item 13 holds a nested blockquote
added by task #58, asking that §7.2's sentence and §10.2's owed-theorem clause both be repointed away from
the refuted argument. Both are in this commit as well, which is how a single list item came to account for
four of the seven blockquotes — and it is why the count in *What was done* is seven and not three. The
nested deferral also carried a defect of its own. It cites the §10.2 clause as `:891`. With this commit
applied the clause sits at `:929–930`, and the only insertion this commit makes above it is eleven lines,
so at `be50578` it was `:918`; either way, not `:891`. The pointer had gone stale before it was read, and
the reason no one noticed is the trap above one more time: the phrase it quotes, *"route-key
distinctness"*, **wraps** in the design, so the obvious way to re-find the line — grep the quoted words —
returns nothing, and nothing reads like agreement rather than like a miss. The stale number is left as
written, per the same pointer-not-rewrite convention, and this paragraph is its pointer. The rule here is
narrower than the one above and cheaper to apply: **a line number quoted from another document is a claim,
and re-measuring it costs one command.** This one was repeated in three places — F49's entry, F50's entry
and the closing section — and not one of them re-measured it.

---

## F54 — an entry that exists is indexed as absent, and every pointer to it counts §4.3's lemmas in the wrong order

**Grade: read, then decided.** Method: the `## F` heading list of this file read in full rather than from
F48 down; the numbering-history paragraph near the top; §4.3 and §10.2 of `docs/STAGE_E_DESIGN.md`; the four
tracked sites that name the refuted lemma; and one declaration line re-measured in
`Relico/Translation/GeneralBasic.lean`. No run, and nothing here needs one.

**What happened.** Task #66 was opened to file a finding that `docs/STAGE_E_DESIGN.md` §4.3 asks for **two**
one-sided injectivity lemmas about `outputPortNameFor` while its own site-suffix witness refutes one of them.
That finding is **F42**, in this file, filed in task #52 alongside F34–F44. The task was a duplicate of work
already complete, and it was opened by the task immediately before it — which had written the number F42 into
the design document, in prose, one commit earlier. Five things lined up to allow that, and each is recorded
because four of them are still live for the next reader.

**1. The numbering-history paragraph indexed two entries as having none.** It read *"F41 and F42 were never
in the design document. They were found during implementation and recorded **only** on the declarations they
concern"*, followed by six `path:line` cites and nothing else. Read as provenance the sentence is true: until
this file landed, the declarations were their only home. But every sibling sentence in that paragraph marks
its relationship to this file explicitly — F34–F40 *"were first written in `docs/STAGE_E_DESIGN.md` §11.1"*,
F43 was claimed in committed code *"while this file did not yet exist"*, F44 *"is stated here first and
nowhere else yet"* — and this one's unqualified *"only"* does not. So it reads as present tense, and a reader
who wants F42 goes to `Relico/Translation/NameGeneration.lean`, finds the whole matter documented there, and
never learns that a full entry sits three hundred lines below the sentence that sent them away. That is what
happened, and it is this file pointing the wrong way about its own contents — the same shape as **F45**,
where it denied a test that existed. Corrected in this commit to *"until this file landed"* plus *"Both have
full entries below"*, in the same four lines, so no cite into this file moved.

**2. Four sites call the refuted lemma §4.3's *second*, and §4.3 lists it first.** §4.3's ask is one
sentence: *"with the message fixed the name determines the rebec, and with the rebec fixed the name
determines the message."* The clause listed **first** is the one that fails — with the message fixed, prefix
cancellation yields the *infix* and the infix does not determine the rebec, which is F42's subject. The
clause listed **second** is the one that holds and is proved, `outputPortNameFor_message_injective`, by
suffix cancellation. Yet all four tracked sites attribute the ordinal to §4.3 and all four invert it: this
file's own F42 heading (*"the design's second one-sided injectivity lemma is false"*),
`Relico/Translation/GeneralRouting.lean:68` (*"§4.3's second injectivity lemma is false and is not stated"*),
`Relico/Translation/NameGeneration.lean:257` (*"the honest form of the second lemma §4.3 asks for"*, and its
own preceding words are *"Prefix cancellation"*, which names the failing direction), and
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean:3517`. A reader following any of them into §4.3 and
counting clauses lands on the lemma that is already proved, and would set out to strengthen it.

The four sites are **not** renumbered, and the reason is worth stating rather than assuming. Three of them
are Lean files, so touching them would turn a documentation commit into one owing a full `lake build` on the
machine that has the toolchain; and this file's F42 heading is quoted by title elsewhere, so rewriting the
heading breaks quotations of it. The correction instead goes where a reader meets the ask: §4.3's third
bullet now carries a dated blockquote that **quotes the failing clause** instead of counting to it. That is
the cheaper fix and also the better one, which is the general point — an ordinal reference into another
document is an *address*, exactly as a line number is, and it moves for the same reason. The discipline this
file already applies to line numbers extends to it unchanged: cite by quoted words. (That rule was stated
here as a bare section reference into a document this repository does not carry, which **F55** item 7
records and repairs.)

**3. The instrument that missed the duplicate had been measured to answer a different question.** The
F-heading map carried into this task listed F48 through F53 and was produced to establish which number was
free next. It was then reused, silently, as though it were evidence that the finding did not already exist.
Whether a pattern or a line range limited it is no longer recoverable; what is recorded is that its lowest
entry was F48, so F42 was never in the window. The aggravating detail is that the number was not merely
findable but already written: the design blockquote committed one task earlier says port names *"stay
guard-relative under F34, F37 and F42"*. Having the number in hand and not asking whether it had an entry is
the whole of the defect.

**4. Two documents cited one declaration fifty lines apart, and neither of them was wrong.** F48's entry
above cites `compileGeneralModel_targetEndpointsUnique` at `Relico/Translation/GeneralBasic.lean:4366`; the
F53 blockquote in §10.2 of the design cites the same declaration at `:4416`. That looked decidable — two
numbers for one named target, so one must be stale — and this entry said exactly that in its first draft,
and changed the findings side to `:4416` on the strength of it. Measuring the Lean file killed the
conclusion: `/--` opens at `:4363`, `-/` closes at `:4415`, and `theorem
compileGeneralModel_targetEndpointsUnique` is on `:4416`. Both cites land in the same block. F48's names the
docstring paragraph its next line quotes, which is what that sentence is about; the design's names the
declaration. The edit was reverted, and it had done real damage in the meantime: five other mentions in this
file address that same docstring as `:4366`, so changing one of six left the file disagreeing with itself,
which is the defect this entry exists to describe, committed by the entry describing it.

So the rule this defect leaves behind is the reverse of the one first written here. Cross-document
disagreement is **not** a decidable stale-cite detector, and it fails for the same reason range-suspicion
fails: a declaration carrying a fifty-line docstring has fifty-three defensible addresses, and two documents
can choose different ones indefinitely without either going stale. The decidable object is the **name**.
Resolve both cites to the declaration they name before concluding anything; if they name the same one, there
is nothing to repair. This is the third false alarm from one family in three commits — the first two
compared docstring cites against a declaration-line map, this one compared a docstring cite against a
declaration cite — and it is the only one of the three that reached an edit, because a disagreement between
two documents feels like evidence in a way that a suspicious range does not.

**5. A debt was discharged at one of the two places that asserted it.** Closing item 13 records that all four
of its corrections *"landed 2026-08-22, in the commit that added F53 — the touch this item was waiting for"*.
F50's entry asserts the same debt independently, and still read *"§10.2's own text **still** carries the false
argument, and is corrected when that document is next opened"* — a future-tense obligation that had already
been met. Corrected here in the same three lines. The mechanism is the one F53 named and did not escape:
when a claim is asserted in two entries, discharging it at one leaves the other arguing for work that is
done, and nothing in the file's structure connects them.

**The rules this leaves behind.** Four of them, and the first is the cheap one that would have prevented
the whole task. *Before opening a task for a defect in a document, grep every `^## F` heading in this
file* — all of them, not the tail. The instrument that failed here was not missing, it was aimed
elsewhere: the heading map had been measured to find the next free number, and its output was then read as
evidence that the finding was new. An instrument answers exactly the question it was pointed at, and the
same mistake appeared twice more in this commit alone — a `^> \*\*` sweep of the design missed every
blockquote that sits inside a bullet, because a nested quote carries an indent before its `>`, and so
disagreed with a count that had been recorded from an indent-tolerant pattern. Second: *an ordinal reference into another document is an
address, exactly as a line number is.* "§4.3's second lemma" moves when a clause is inserted or reordered,
and it moved here — four places call the refuted lemma the second while §4.3 lists it first. Cite by
quoted words, as this file's own practice already required for line numbers. Third: *no arithmetic over line numbers detects a
stale cite into a Lean file.* This commit tried both kinds available and both failed — range-suspicion
raised a false alarm, and cross-document disagreement raised one and got as far as an edit before
measurement reverted it. A declaration with a long docstring has as many defensible addresses as its
docstring has lines, so the one decidable question is whether two cites resolve to the same **name**;
resolve the name first, and stop there if it is the same. Fourth: *a record of what a search returned
must not be rewritten, and a live claim about a document's present state must be correct.* One sentence
can be either, and which it is decides whether a stale number in it is a defect or the evidence.

**What this commit did.** It moved all four numbering literals from F53 to F54 — line 1, the *Why this
file exists* paragraph, the citability sentence, and the numbering-history line — which is the test the
four-literals rule set for itself one finding ago, and it passed. It rewrote the numbering-history
sentence so F41 and F42 are indexed as entries that exist. It replaced a line cite into the
design with a section cite. It rewrote three lines of F50's entry that still asserted a debt discharged at
closing item 13. It changed F48's cite to `compileGeneralModel_targetEndpointsUnique` and then changed it
back, the fourth defect above being the record of why. And it added two dated blockquotes to `docs/STAGE_E_DESIGN.md`: one under §4.3's third
bullet quoting the clause that is false, and one in §10.2 discharging the promise task #65 committed there
in as many words — *"Task #66 owns that correction and will annotate §4.3 and this sentence."* Deliberately
not done: the four ordinal sites are not renumbered, three of them being Lean in an otherwise docs-only
commit, and F49's record of a search is not rewritten.

Those two insertions shifted §5 onward by twenty-one lines and §10.3 onward by twelve more, so the sweep
that discipline calls for — re-resolving every qualified cite into the shifted document — was run in both
directions afterwards. It found exactly three qualified cites into the design
anywhere in the repository: one names a commit and is immune, one sits above the first insertion, and one
is the search record above. No live cite needed repair — which is the first time that sweep has come back
empty, and it came back empty because the two cites that would have broken had already been converted to
section cites by earlier findings.

One thing is filed rather than fixed. The closing *What is left open, and who owns it* section is no
longer closing: F53 sits below it, F54 below F53, and F55 below F54, for the reason F53 gave — appending
is the only edit to this file that shifts nothing. Moving that section to the end would displace several
hundred lines and invalidate the cites this commit has just verified, so it belongs to a commit with no
other business. Until then, a reader who stops at the closing section stops three entries early, and this
paragraph is the pointer that says so.

---

## F55 — a recording run could not record, because the preflight forbade the state its own message asked for

**Grade: measured**, with the provenance of each part kept separate. The failing run is recorded in the code
it caused, `frontend/test_validate_general_v1.py:754-767`, written when it happened. The repaired run
printed `RECORDED — review before commit` for `send-sites` and then `General frontend check passed.` The
Lean gate afterwards ended `GENERAL_LEAN_GATE_OK`, reporting 24 frontend assertions and 88 printer
assertions. No part of this entry needs a run that has not happened.

**The defect.** Adding a positive to `frontend/fixtures/general` is a two-file change and only one of the
two files can be written by hand. `<name>.rebeca` is authored; `<name>.parser.json` has to be **recorded**
from a real exporter run, because every node in `general-v1` carries a `line`, those line numbers come from
the Rebeca compiler's own AST, and no other exporter in this repository reads them at all — the argument
`frontend/fixtures/general/README.md` makes at length under *"Why six are recorded rather than predicted"*.
The run that records is `check-general.sh --record`.

That run could not record. `check-general.sh` runs its own two checker suites at `:110-111`, before the
positives loop at `:128` that writes missing expected documents. One assertion in the first suite —
`PositiveFixturesAreAccountedFor.test_every_positive_has_an_expected_document`, at
`frontend/test_validate_general_v1.py:750` — requires every `.rebeca` under `fixtures/general` to have a
committed `.parser.json`. So on the one run whose entire purpose was to create the missing document, the
demand for that document was evaluated first and the creation never happened. **And the failing
assertion's own message named `--record` as the remedy** — the run that had just failed. A reader
following the diagnostic exactly is sent in a circle.

**Why it stayed latent for a whole positive.** The assertion was tightened once, deliberately, and
`:754-758` records the tightening: before the first gate run it asked something weaker, that a fixture
either be an anchor or be named in the README as not yet recorded, and once recording had happened the
invariant tightened to the strong form. The strong form is the right invariant — a positive with no
expected document asserts only that the exporter does not crash. What went unnoticed is that tightening it
put the suite in conflict with the recording run, and **that conflict is unreachable until the next new
positive arrives**, because in the interval every positive already has its document. It took a second new
positive to fire it. That is the general shape, and it is worth more than this instance: an invariant
tightened immediately after a one-off event is a trap armed for the second occurrence of that event.

**The fix, and why it is narrow rather than a relaxation.** `check-general.sh:106-108` exports
`RELICO_GENERAL_RECORDING=1` when and only when `MODE` is `--record`, and
`test_validate_general_v1.py:76` is its only reader in the tracked tree. The exemption at `:772` is
`if RECORDING and not document.is_file()`, and it **skips rather than passes**, so a recording run still
says out loud which positive it has yet to account for. Nothing about the content of a document that does
exist is affected, and for every ordinary run — the run whose green result is the gate — the invariant is
exactly as tight as it was. The narrowness is the whole design: the alternative on the table was to weaken
the assertion back to its pre-tightening form, which would have paid for one bad run with a permanently
weaker gate.

Seven things travelled with this repair, and a recurrence besides. Five are about counts, one is about
instruments, and one is about a cite that resolves to nothing. Only the first was known when the task
opened; the rest were found by verifying this entry's own claims before it landed, which is the argument for
doing that.

**1. A stale count was repaired by deleting it.** `check-general.sh` carried a comment saying the shared
Maven build saves "twenty-seven fixtures" a build each, while the corpus held twenty-eight. It is **not**
corrected to twenty-eight. The comment now states why: *"Deliberately not written as a count … a number
here has to be maintained by whoever adds a fixture anywhere, which is exactly the maintenance that keeps
failing."* Nothing executable reads that number. This gives F46's rule a corollary worth stating on its
own: **where a count is load-bearing for nothing, deleting it is strictly better than maintaining it**,
because a number that does not exist cannot go stale.

**2. The numeral sweep took three passes, and the third found the case the first two could not.** The
first pass swept for English number words and missed "twenty-seven", because that word was not in the list
the sweep was built from — an instrument answering exactly the question it was pointed at, which is F54's
first rule recurring within two commits. The second pass, with the word added, found it. The third found
something neither could: `fixtures/general/README.md` stated the size of `reject/` as a **numeral inside
Markdown table syntax**, `| | reject/ (11) | upstream-reject/ (8) |`, while the corpus held twelve. That is
a third way a count hides from a text search, and the least obvious: not by being wrong in a sentence, but
by sitting where no sweep for sentences looks. A count written as a numeral inside markup is invisible to a
sweep for number words, and invisible again to a sweep for prose, because its neighbouring bytes are table
delimiters rather than words. The sizes were then taken by counting the directories
instead of reading the prose: 12 `reject/`, 8 `upstream-reject/`, 10 positives, 14 `lean-reject/`.

**3. A neighbouring "eleven" was repaired by making it a record rather than by correcting it.**
`fixtures/general/lean-reject/README.md` said the exporter's parameter-shadowing branch was unexercised and
that *"`reject/` holds eleven sources"*. That number is **not** changed to twelve. One word is inserted —
*"`reject/` **then** held eleven sources"* — and the paragraph continues that the gap is closed as of
2026-08-22 by the new fixture, *"the companion this paragraph asked for"*. Two counts reading eleven, in
one commit, handled oppositely on purpose: the first is a live claim about the present corpus and had to be
corrected, the second describes the state at the time it was written and had to be preserved. This is F54's
fourth rule applied deliberately, rather than discovered in breach.

**4. Six sentences were left saying "nine", and the first count of them said three.**
`docs/STAGE_B_DESIGN.md` speaks of the nine positives six times — among them *"All nine positives elaborate
except"*, *"Eight of nine elaborate"* and *"All nine stage-A positives elaborate except"* — while a seventh
"nine" in that file counts inductive constructors and is unrelated. All six are stage-B-era measurements of
a corpus that held nine positives when they were taken, so all six are records, and none is touched. The
count in this item is the part worth reporting: it read *three* until a grep was run, having been written
from recollection inside an item about counts that nobody measured. That is F46's pattern — an off-by-one
written into prose at the moment of the edit describing off-by-ones — and it is one more count in this task
that a measurement moved after it had already been written down.

**5. The rule about counts that go stale is stated three times in this file, and no two statements name the
same places.** This is the item worth the most, because the defect is in the rule rather than in an
application of it. Measured, in file order:

- The numbering-history section, in the passage written when F48's commit repaired three stale numbers:
  *"The three places that have to move together are line 1, the "Why this file exists" paragraph, and the
  numbering-history line above."*
- **F51**: *"This file states its own range or count in four places: the title, the "eighteen findings"
  sentence, the "numbered F34 through …" sentence, and the sentence "this file is what makes F34–…
  citable"."*
- **F54**: it *"moved all four numbering literals … line 1, the* Why this file exists *paragraph, the
  citability sentence, and the numbering-history line."*

The first two describe the **same three places at two granularities** — F51 splits the *Why this file
exists* paragraph into the two sentences it contains, and so counts four where the earlier passage counts
three. F54 merges those back into one and adds a place neither earlier statement has, the running
numbering-history paragraph recording what each finding did about its numbers. So "four" is reached twice,
by two different routes, over two different sets, and each of the three tallies is internally correct.
Counted at F51's granularity the places are six, F54's closing paragraph included; counted at F54's they are
five. This entry moves all of them and the parenthetical near the top now gives both numbers, because
picking one silently is what produced three answers.

That sixth place is the one no rule anticipated, and it is a live count rather than a range: F54's closing
paragraph says a reader who stops at the stranded *What is left open* section *"stops two entries early"*,
which appending F55 falsifies. It is repaired in the paragraph immediately above this entry's heading, which
is where F54 ends.

Two things follow. First, **a count is not made safe by being carefully derived — three careful passes
derived three different numbers from one file**, because each fixed a granularity implicitly and none said
which. Where a rule counts things, the rule owes a statement of what it counts as one thing. Second, the
reason no pass saw the others is F54's first rule recurring a third time: each was written while repairing
one specific stale number, so each enumerated the places *that* number lives in and stopped. Nothing was
ever pointed at *how many such places exist*, so nothing answered it.

**6. Three instruments failed inside this one task, by three different mechanisms.** Complying with the
move-together rule meant reading it, and a `grep` for the phrase *four literals* in this file returns **no
matches**: the phrase wraps, "four" ending one line and "literals" beginning the next. That is the rule
about how counts hide, hidden by the mechanism it describes. The second was the number-word sweep with no
"twenty-seven" in its list, item 2 above. The third is the one worth recording, because unlike the others it
reached a conclusion that was then acted on: a `grep` for every `§` cite in this file was piped through
`head -40`, and the file then held **91** such marks, so the forty that came back were read as evidence
about all ninety-one. The conclusion drawn was that no `§4d` cite existed here — three did, all of them in
F54, as item 7 records — and it was reversed two commands later by a grep aimed at the letter suffix
instead. Truncated output is not a smaller answer to the same question, it is a complete answer to a
different one, and `head` over a match set whose size has not been measured substitutes the second for the
first, silently and in the direction of believing an absence.

The rule for the first: **a phrase grep over prose is not a search for a phrase, it is a search for an
unwrapped phrase.** The rule covering all three is F54's first, now recurring for the second, third and
fourth time — each instrument answered exactly the question it was pointed at. Both greps here were
recovered by reading the section, which is the case for citing by quoted words and *reading* by section
rather than by match.

**7. Three cites in F54 resolved to no document this repository carries.** F54 stated two of its four rules
by reference rather than in full. It said *"§4d's rule extends to it unchanged: cite by quoted words"*, and
*"Cite by quoted words, as §4d already required for line numbers"*, and it called a sweep the one *"§4d asks
for"*. Those are quoted in the past tense because this commit repairs all three, and no line numbers are
given for them, both for the reason this item is about. Measured, and the measurement is the point: **no
letter-suffixed section cite exists anywhere in this repository outside this file** — not in
`CONTRIBUTING.md`, whose six sections are unnumbered, not in `README.md`, not in any of the other 92
markdown documents under `docs/`, not in any Lean source — and not in the untracked working design under
`tmp/` either, whose §4 is *"Where the translator should live"* and carries no lettered subsections. That
numbering belongs to a set of working conventions held outside the repository altogether.

What made it read as legitimate is the company it keeps. This repository carries **308** dotted section
cites of the form `§4.1`, `§7.2`, `§10.2`, and they resolve — overwhelmingly into `docs/STAGE_E_DESIGN.md`,
which really does have those subsections, including the §4.3 that F54's own ordinal finding is about. A
`§4d` sitting among 308 working cites inherits their credibility while resolving to nothing, which is a
better explanation of how it passed review three times than inattention is. For a reader who has only the
repository it is a rule asserted by reference to nothing, and the sweep it names is a claim about a
procedure that reader cannot look up.

**And the ordinal itself is real, which is the part worth keeping.** `4d` *is* a live address in this
repository: `docs/actor-priority/phase4d/` exists and holds a document, alongside fifteen sibling
directories numbered by exactly this convention — `phase2b`, `phase3a`, `phase3b`, `phase3c`, `phase4a`,
`phase4b`, `phase4c`, and `phase4d1` through `phase4d7`, forty markdown files between them. So `§4d` is not
invented notation. It is a real ordinal from the *phase* namespace wearing the `§` sigil, which claims the
*section* namespace, and the sigil is the only part that is wrong. That is a narrower and more useful
diagnosis than "the cite resolves to nothing", because it names the mechanism: a collision between two live
numbering schemes, one of which resolves. It also sharpens F54's own rule. That entry established that
ordinals are addresses; this adds that **an ordinal is an address only together with its namespace**, and a
sigil is the whole of what carries the namespace.

This is F54's own ordinal finding one level up — an address into a document, cited where it should have been
quoted — and it was landed by the entry that states the rule against it. It is repaired the way that entry
prescribed: all three now state the rule in words and cite no section number. What is deliberately **not**
done is graduating those conventions into the repository as a real document with a real numbering, which is
what would make such a cite resolvable. That is a document to be written, not a repair to this one.

**A recurrence worth naming.** `frontend/java-bridge/check-general.sh`, in the comment above its `--record`
branch, says *"That is finding F55"*, and `frontend/test_validate_general_v1.py`, above its `RECORDING`
definition, says *"See finding F55 for why this flag has to exist"* — and both landed in
commit `c6ce367` while this entry did not exist. That is exactly the F43 situation the numbering history
above records, and that paragraph predicted it in as many words: *"It is recorded rather than tidied away,
because the pressure that caused it (a green gate is a strong incentive to land) will recur."* It recurred
one finding later and for the identical reason — the fixture commit was green, and the entry was docs-only
work that could follow. The interval is one commit rather than F43's several, which is the only respect in
which this is better.

**The rules this leaves behind.** First, and it is the one with teeth: **a diagnostic that names a remedy
is a claim that the remedy is reachable, and a gate must be able to reach the state its own failure message
asks for.** Nothing checks this class of defect and no ordinary run can, because the state that triggers it
exists only in the window between adding a fixture and recording it. Second: **an invariant tightened
immediately after a one-off event is armed for the second occurrence of that event**, so the question when
tightening is not "does this hold now" but "what is the next run that has not happened yet". Third: **a
provenance note naming a unique event goes stale the first time a second event of that kind happens** —
the `RECORDED` tuple's comment said "the first `--record` run" and now says "a real run", because five of
its six entries were recorded by one run and `send-sites` by another. Fourth: **where a count is
load-bearing for nothing, delete it rather than maintain it.** Fifth: **a rule that counts things owes a
statement of what it counts as one thing** — three careful passes over this file derived three different
totals from very nearly the same set of places, each having fixed a granularity without saying so. Sixth:
**truncated output is a complete answer to a different question**, so a `head` over a match set whose size
has not been measured is not evidence about that set, and the failure is silent in the direction of
believing an absence. Seventh, refining F54 rather than adding to it: **an ordinal is an address only
together with its namespace.** `4d` resolves in this repository and `§4d` does not, and the entire
difference is a sigil asserting a namespace the ordinal was not drawn from. Where two numbering schemes are
live at once — audit phases and design sections, here — a bare ordinal is ambiguous, and a sigilled one can
be confidently wrong while looking more precise than the bare one.

**What this commit did.** It added this entry and moved every place in this file that states its own range or
count — six counted at F51's granularity, five at F54's: line 1, the two sentences of the *Why this file
exists* paragraph, the citability sentence, the running numbering-history paragraph, and F54's closing
paragraph, which no earlier finding had cause to touch. It rewrote the numbering-history paragraph that
records what each finding did about its numbers, so that it points at the reconciliation rather than
asserting a fourth total, and recorded there that F55's number was already cited in two tracked files by
commit `c6ce367`, one commit before this entry existed. It repaired three cites in F54 that addressed a
section of a document
this repository does not carry, restating each rule in words instead. The code and fixture side of F55
landed separately in `c6ce367`, together with the tenth positive and the twelfth exporter reject, so this
commit is documentation only and owes no `lake build` — no gate script reads `docs/`.

**Deliberately not done.** The stranded *What is left open, and who owns it* section is still not moved to
the end; F55 left three entries below it where there had been two, and F56 below makes four, so the case for
a commit with no other business is stronger by exactly one entry each time. The working conventions this
file keeps citing — the rules about addresses,
instruments and quoted words that F54 reached for when it wrote `§4d` — are still held outside the
repository, so item 7 repairs three cites without removing the reason they were written. Graduating those
conventions into a numbered document in `docs/` is what would make such a cite resolvable, and it is a
document to write rather than an edit to this one, which is why it is filed here and not attempted. And the
gate gains no check for the class of defect F55 is: the first rule above is a rule for a reader, not an
assertion, and making it executable would require a run that deliberately deletes a committed document in
order to prove it can be recreated.

---

## F56 — two identical self-sends in one body compile to one message execution, silently

**Provenance: measured.** `lfc` 0.11.0, 2026-08-22, target `Cpp`, sections 12 and 13 of
`tools/paper-measurements/lf_semantics_probe.sh`. Three probes: two compiled and ran, one did not compile,
and the one that did not compile is half the finding.

**The claim this replaces.** `docs/STAGE_E_DESIGN.md` §6.3 recorded that `self.tick(); self.tick();` in one
body emits two `tick_action.schedule(0ms)` calls at one tag, and that *"two invocations of one action at one
tag are understood to be acceptable in LF, which is why this is not being treated as a defect"*. The grade of
*understood* was **inferred**, and §11.2 item 7 said as much in the same document: the behaviour was
**unmeasured**, and the item recorded a prediction that the reaction would fire twice at successive
microsteps. This is precisely the shape the provenance rule at the head of this file exists to catch — an
inferred claim doing the work of deciding that something is not a defect.

**What the run showed.**

    action_two_schedules_same_tag       lfc 0, run 0 -> ONE line,  RELICO_ACTION 2
    action_two_schedules_distinct_tags  lfc 0, run 0 -> TWO lines, 1 then 2
    action_defer_policy_same_tag        lfc 1        -> DID NOT COMPILE

Two schedules of one logical action at one tag keep only the **last** value; the first is discarded. `lfc`
exits 0, the generated C++ builds, the program runs, it exits 0, and nothing at any stage reports a lost
event. The second probe is the control, differing only in the second delay — `1ms` rather than `0ms`, so two
distinct tags — and it printed both values. That is what rules out a mistyped API call and establishes the
single line in the experiment as a real collision rather than a broken probe.

**The repair that does not exist.** LF actions take `(min_delay, min_spacing, policy)`, and `defer` is
documented to push a schedule that would violate `min_spacing` to the next permitted tag instead of
discarding it — exactly the mechanism that would reproduce Rebeca's queue. It cannot be used here:

    lfc: error: minSpacing and spacing violation policies are not yet supported
         for logical actions in reactor-ccp!

The `ccp` is `lfc`'s own. So both halves of §11.2 item 7's prediction were wrong, and the second was wrong in
a way that item's enumeration of candidate behaviours could not have covered: the outcome is not a behaviour
but the absence of a vocabulary in which to ask for one. Note the shape of the pair — the target refuses to
*discuss* spacing, while silently *implementing* the lossiest spacing behaviour when nothing is said. The
safe-looking declaration is the lossy one and the explicit one is unavailable, which is the opposite of
failing closed.

**Why it is reachable.** Nothing refuses such a model. Every `Nodup` in `Relico/DTR/GeneralWellFormed.lean`
constrains a set of *names* — class names `:332`, declaration names `:342`, message-server names `:346`,
message-server priorities `:460`, actor priorities `:490` — and none of them constrains repeated send
statements within a body. Repeating a send is legal Rebeca: the upstream compiler has no objection and
neither does the exporter. So a DTR well-formed model reaches the printer and is translated into a program
that performs one of its two sends. This was checked in the F32→F43 direction **first and deliberately**,
because the last time a defect of this shape was suspected it turned out to be a guard refusing the program.
Here there is no guard.

**Why no fixture caught it, and which fixture is the trap.** No committed positive puts two schedules of one
action in one body, and the near-miss is not the one the replaced §6.3 named. The version quoted above
pointed at `priorities`, which self-sends twice from its constructor (`:7`, `:8`) but to two *different*
message servers, so two different actions; the repair to §6.3 drops that remark rather than carrying it
forward, so it is preserved here and nowhere else. The closer near-miss is `keep-alive`, which repeats the
**identical** send `self.keepAlive()
after(1)` — same message, same target, same delay — at `:7` and `:11`, and is safe only because those two
occurrences sit in *different bodies*: the constructor schedules once, and each firing of `keepAlive`
schedules once more. So the property that decides safety is not whether a model repeats a send but whether
**one body** repeats it, and a fixture written by copying `keep-alive` would reproduce its safety rather than
the defect. Whoever writes the witness for task #69 needs two sends in a single body.

**Why no gate caught it either.** The divergence sits past the last artifact any gate inspects.
`check-general-lean.sh` compares emitted LF text against expected LF text, and the target gate checks that
`lfc` accepts what was emitted. Both pass on the defective output, because the output is well-formed LF that
compiles cleanly — it simply means something other than the source model does. Catching this class requires
**running** the produced binary and comparing observed message executions against the Rebeca semantics, and
no gate in this repository does that for any model, in any family.

**What follows, and it is forced rather than chosen.** With no declaration-level mechanism available in the
target, a faithful encoding needs a distinct action per self-send **site**. That is the same decision §6.2
reached for ports, arrived at a second time down an unrelated road, and it is the argument for restating
§6.2's key as forced rather than preferred — which its item 1 now does, and which the paper should follow.

**Necessary but not sufficient — measured 2026-08-23, probe section 14.** One action per site still leaves the
question of how many *reactions* those k actions feed, and the cheaper answer does not work. Two actions
scheduled at one tag with a single reaction triggered by both fire it **once** (`lfc` 0, run 0), since a
reaction's trigger list is a disjunction and is enabled if any trigger is present, so k−1 executions are lost
again — by a different mechanism than above, where the payload was overwritten on one action rather than the
firings merged across two. One reaction per action prints both values, in reaction declaration order. So the
repair is **an action and a reaction per site**, the alternatives are measured dead rather than disfavoured,
and §6.2's key and this one are one decision reached three times. It also puts an obligation on the printer:
declaration-order firing was previously measured only for *port*-triggered reactions, and now that it is known
to hold for *action*-triggered ones, the generator must emit site reactions in the order their sends appear in
the body, which makes emission order a correctness property rather than a formatting choice.

**Decided, not asked — the repair is implemented, not refused.** Whether to build the structural repair or
instead refuse repeated identical self-sends in the well-formedness predicate was left open above. It is
settled in favour of implementing. Refusing is far cheaper and fails closed, but it would narrow the accepted
fragment against Rebeca that is legal and that the paper's fragment contains, which is the opposite of what
this whole stage sequence exists to do; and the same trade was already resolved the same way when §10.2's
refuted item was recorded rather than converted into a stronger guard. The cheapness of refusing is real and
is the reason to record the choice here instead of letting it look inevitable.

**Still open.** Whether this earns a `P` number. It appears not to — the paper's SOS rules do not commit to an
action-based encoding of self-sends, so the mistranslation looks like this development's rather than the
paper's — but that reading has not been checked against the paper, which makes it **inferred**, and under
this file's own rule an inferred claim names the check instead of concluding it. The check is to read the
paper's send rule for the self-send case and confirm it constrains only the resulting queue, not the
mechanism.
