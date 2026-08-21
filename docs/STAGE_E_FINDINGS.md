# Stage E findings — F34 through F44

**Why this file exists.**
Stage E added external sends, ports and connections to the general translator, and in doing so it
produced eleven findings about *this repository* — its own code, its own design document, and its own
test harness. They are numbered F34 through F44, continuing the single `F` series that
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
what makes F34–F44 citable.** Nothing below is provisional any more.

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
