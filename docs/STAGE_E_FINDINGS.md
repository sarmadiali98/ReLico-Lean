# Stage E findings — F34 through F49

**Why this file exists.**
Stage E added external sends, ports and connections to the general translator, and in doing so it
produced sixteen findings about *this repository* — its own code, its own design document, and its own
test harness. They are numbered F34 through F49, continuing the single `F` series that
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
what makes F34–F49 citable.** Nothing below is provisional any more.

F41 and F42 were never in the design document. They were found during implementation and recorded
only on the declarations they concern — F41 across `Relico/Translation/GeneralRouting.lean:47`,
`:1127` and `Relico/LF/GeneralCppPrinter.lean:1526`, F42 across
`Relico/Translation/NameGeneration.lean:114`, `:208` and `Relico/Translation/GeneralRouting.lean:68`.

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

**Grade: decided.** The alternative was considered and rejected; `docs/STAGE_E_DESIGN.md:1081` records
the rejection.

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
overwritten: `docs/STAGE_E_DESIGN.md:19–20` and `:443` point at this finding from the document that
replaced it.

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

**What ran**, verbatim from the `#eval` output:

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

**Three things the run measured that were predicted wrongly or not at all**, recorded because each one would
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

<!-- F49_BODY_MARKER -->

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
class by step 4 of the environment"* — is what `F48_OUTPUT_PORTS reportToToHub | reportToToHub` disproved, two
entries with one name in a single class's port environment. The second — *"one instance binds one known rebec to
one instance, so one (sender instance, output port) pair contributes exactly one arrow"* — is true of a single
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
`outputPortNameFor` permits and what `F48_OUTPUT_PORTS reportToToHub | reportToToHub` is. So both wrong sites
in this module rest on the same unstated premise, that a (sender instance, output port name) pair identifies at
most one route, and both were written as though a theorem about names supplied it. **Fixed here too**, on the
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

---

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
