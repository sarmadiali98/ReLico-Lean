# Paper corrections found by building the tool

**Why this file exists.** User, 2026-08-17: *"we can change the paper. one of the goals of this lean
thing is to find out these kinds of issues."* That reclassifies every divergence below. These are not
obstacles to be worked around quietly in the translator — they are findings, and they are arguably the
most defensible contribution the formalization has produced so far, because each one was found by a
machine refusing to accept something a human proof accepted.

**Provenance rule.** Every entry is either (a) measured against real `lfc 0.11.0`, (b) measured across
the 49-model upstream corpus, or (c) quoted directly from the PDF at
`~/Desktop/LFStructuringNonDeterminism/DTR_LF__After_FMCAD_.pdf`. Nothing here is inferred from
`docs/actor-priority/phase2/*.tsv` or from this repository's own summaries of the paper. Each entry
states its evidence, and inferences are labelled as inferences.

A fourth grade was added on 2026-08-19: **(d) stated authoritatively by the project lead** about a system
this project does not control. Exactly one entry rests on it — P15, on LF connection delays — and it says
so in place. The grade exists because the alternative was worse: leaving a real finding unfiled because
the only available evidence was authoritative rather than mechanical. It is not a licence to promote
guesses, and an entry at grade (d) should be re-graded if a measurement later becomes available.

Fig. 4 and Fig. 5 are transcribed in full, once, in
[`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`](dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md),
alongside the numbered restrictions R1-R24 that the frontend enforces and the deliberate divergences
D1-D9. Entries here cite that document rather than re-quoting the grammar, so that a delimiter fix
lands in one place. That precaution is not hypothetical: P5 below previously misquoted a production.

**Reproducing the measured entries.** The three scripts that produced every corpus and `lfc` number
below live in [`tools/paper-measurements/`](../tools/paper-measurements/), with usage and the external
corpus they need documented in that directory's README. They are in git precisely so that no entry
here rests on evidence that cannot be regenerated.

---

## P1 — Lemma 2 is unsound as stated

**Claim in the paper:** reaction declaration order fixes execution order between reactions, used to
justify that upstream reactions run before downstream ones.

**Why it is wrong:** in LF, relative execution order between reactions in *different* reactors is
fixed only by the dependency graph, i.e. by connections. Two unconnected reactors receiving events at
the same tag are unordered, and the Cpp target may run them in parallel. Where "upstream before
downstream" does hold, the order comes from the **connection**, not from the declaration.

**Evidence:** LF semantics; corroborated by the probe, which could only demonstrate declaration-order
sensitivity *within* a single reactor (see P2's result).

**Suggested edit:** restate Lemma 2 as two separate claims — (i) within one reactor, declaration order
totally orders same-tag reactions; (ii) across reactors, the dependency graph induced by connections
orders them, and unconnected reactors are unordered. §III-D only ever needs (i), so nothing downstream
breaks.

**Status:** the honest silver lining is that this *strengthens* the case for §III-D. Its per-receiver
fan-in construction converts a cross-reactor ordering problem into a within-reactor one, which is
exactly the case where LF gives a guarantee. §III-D is not an arbitrary construction; given (i) and
(ii) it is the only place priority can be attached.

---

## P2 — Fig. 5's grammar admits indexed triggers that `lfc 0.11.0` rejects

**Claim in the paper:** Fig. 5 gives `Trigger ::= startup | inPort([Expr])? | act` and
`OutTarget ::= outPort([Expr])? | act`, i.e. a reaction may be triggered by an indexed channel of a
multiport.

**Why it is wrong:** `lfc 0.11.0` rejects `reaction(in[0])` outright with
`no viable alternative at input 'in'`. Both declaration spellings were tried; both fail. A
whole-multiport trigger `reaction(in)` is legal but fires **once per tag** regardless of channel count.

**Evidence:** measured, `tools/paper-measurements/lf_semantics_probe.sh` probes 5-8, `lfc 0.11.0`.

**Consequence, which is the load-bearing part:** a multiport therefore yields exactly one reaction for
all *k* senders — no separate reactions, hence no reaction ordering, hence nowhere to attach actor
priority. **Multiports cannot implement §III-D.** Named ports are forced.

**Suggested edit:** drop `([Expr])?` from the `Trigger` production, or mark it as not supported by the
reference compiler. Also note that Fig. 5's `LFProgram ::= target Cpp;` carries a semicolon the
checked-in fixtures do not emit.

**What the probe *confirmed*, and should be stated as a hypothesis the paper relies on:** two models
identical except for the order two reactions are declared, both senders firing at `startup` into
`after 0 msec` connections, printed `RELICO_A, RELICO_B` and `RELICO_B, RELICO_A` respectively. So
declaration order does decide same-tag order within a reactor. The paper currently assumes this
without stating it as an assumption about the target compiler.

---

## P3 — §III-F's cost claim is not achievable under the paper's own class-to-reactor mapping

**Claim in the paper:** the fan-in construction costs O(kb) per receiver, with *k* the number of
senders to that receiver.

**Why it is wrong:** the translation maps each reactive **class** to one reactor. A reactor declares
its ports once, for the class, so the port set must be the **union** of senders across *all instances*
of that class. `k` is therefore the union count, not the per-instance count. The stated bound is
achievable only with one reactor per instance, which would abandon the class-to-reactor correspondence
that most of the translation theorems are stated about.

**Evidence:** structural, plus probe 4 confirming that the resulting unconnected input ports are legal
(compile, run, exit 0, reaction never fires) — which is what makes the union design viable at all.

**Suggested edit:** state the bound as O(k\_union · b) and note the trade against per-instance
reactors. Ring topologies (`phils`, `node_and_switch_with_after`) are where the gap is widest.

---

## P4 — the paper has no tie rule, and ties are the norm upstream

**Claim in the paper:** none. Priority appears in neither SOS table's tie handling, and no rule
resolves two equal priorities. Confirmed lexically: "tie", "distinct", "equal priority", "same
priority" and "unique priority" occur **zero times** in the paper, and Lemma 2 compares priorities
with strict `<` only.

**Why it matters:** measured upstream, **3 of 49 models have actor-priority ties** (`TrainDoor`,
`TrainDoor2`, `TrainDoorFeedback` — the last a three-way tie) and **29 of 49 have msgsrv-priority
ties.** Ties are not a corner case.

**Evidence:** measured corpus inventory, reconfirmed by
`tools/paper-measurements/measure_priority_requirement.py`; the lexical counts measured directly on the
PDF text.

**Suggested edit:** add an explicit tie rule. The tool now **rejects** ties, scoped to senders into
the same msgsrv on the same receiver. Measured consequence of that scope: it rejects **zero** of the
three upstream tie models, because all three have zero contended message servers. A globally scoped
tie rule would reject all three. The scope is doing real work and should be stated.

---

## P5 — Fig. 4 makes `@priority` optional, contradicting §III-G's own prose

**CORRECTED 2026-08-17, twice.** Both corrections matter, and both were caused by trusting a
second-hand transcription instead of the PDF.

**Correction 1, the quotation.** This entry previously quoted
`InstanceDecl ::= Priority? C rebecName ⟨rebecName*⟩ : (IntLit*) ;`. The known-rebec binding list is
delimited by **large parentheses**, `(rebecName*)`, not angle brackets. Verified at font and charcode
level on page 13: the delimiters are `OUPIJB+CMEX7` charcodes 0 and 1, and no `⟨`/`⟩` occurs anywhere
on that line. Angle brackets do appear in Fig. 4, but only around `Type v` in `Constructor` and
`MsgSrv`.

**Correction 2, and this one reverses the entry's thrust.** This was filed as "the paper's grammar
admits models we now reject", implying the tool adds a restriction the paper never contemplated. It
does not. The paper states the restriction in prose, twice:

- §II-A p. 3: *"Full Timed Rebeca models with unresolved observable choices require priorities before
  translation."*
- §III-G p. 6: *"Full Timed Rebeca models with unresolved observable choices are outside the supported
  fragment."*

**So the defect is narrower and easier to fix than recorded: the grammar lags the prose.** `Priority?`
in `InstanceDecl` carries no side condition, so Fig. 4 in isolation derives models §III-G explicitly
excludes. The suggested edit is therefore "align Fig. 4 with §III-G", not "adopt a new restriction" —
a much stronger position, since it asks a reviewer to accept the paper's own stated intent.

**Suggested edit — and note which edit:** *not* dropping the `?`. Requiring priority on every instance
rejects **40 of 43** upstream files, including `node_and_switch_with_after` and `phils`, the two models
the paper's own irreducibility argument depends on. Instead attach a side condition to `InstanceDecl`:
*every instance that is one of ≥2 senders to the same message server of the same instance must carry
`@priority`, and those priorities must be pairwise distinct.* Measured cost: **9 of 43 files (7
distinct models)** rejected, every one of them a message server with ≥2 senders and **no** annotated
sender at all — `tcsma`, `sensornetwork`, three `yarn-deadline-fifo-*AMs`, `hybrid`, and `ASPIN` (34
contended message servers, zero actor priorities). Those models are genuinely nondeterministic at
those points, so the rejections are correct, and they are exactly the "unresolved observable choices"
§III-G names.

**Evidence:** grammar read directly from Appendix A, Fig. 4, page 13; prose quoted from §II-A and
§III-G. Corpus measurement: `tools/paper-measurements/measure_priority_requirement.py` over 43
statically analysable files.

**Bonus result worth putting in the paper:** the condition makes the corpus's own exemption idiom free.
15 of the 16 partially annotated models leave exactly one instance unannotated and it is
`KeepAlive ka`; measured, `ka` is **never** a sender into a contended message server anywhere in the
corpus, because it only self-sends. No allowlist required.

---

## P6 — Fig. 4 never defines `Type`, and the two readings disagree on whether the fragment is analysable

**Claim in the paper:** `Type` appears in four productions — `KnownRebecs`, `VarDecl`, `Constructor`,
`MsgSrv` — and is **never given a production.**

**Why it matters:** if `Type` ranges over reactive class names, then Fig. 4 admits rebec-typed state
variables and rebec references as message payloads. Under that reading the map from
`(receiver, msgsrv)` to sender set is not statically computable, which sinks §III-D's port layout,
§III-F's `k`, and any actor-priority well-formedness check at once. Under the primitives-only reading
everything is fine, but the figure does not say so.

**Evidence:** grammar read directly from Fig. 4. Measured: **5 of 49 upstream models exercise the
dangerous reading**, via four constructs —

| | construct | models |
|---|---|---|
| A1 | rebec-typed state variable, `statevars { CommunicationDevice d; }` | `TinyOSPV6-MACB`, `TinyOSPV6-TDMA`, `LeasingNRPFD`, `AutonomousVehicles` |
| A2 | rebec-typed msgsrv parameter, `msgsrv requestTicket(Customer c)` | `ticket-service`, `TinyOSPV6` ×2 |
| A3 | send to a cast of `sender`, `((CommunicationDevice)sender).m(...)` | `TinyOSPV6` ×2, `AutonomousVehicles` |
| A4 | capture `sender` into state, `d = (CommunicationDevice)sender;` | `TinyOSPV6` ×2 |

A3 and A4 are already outside Fig. 4, since `RebecExpr ::= self | rebecName` admits no cast and no
expression — worth noting explicitly, because it means the corpus contains models the paper's own
grammar excludes. A1 and A2 hinge entirely on the undefined `Type`.

**Suggested edit:** add a production for `Type` and a sentence stating that rebec references are not
first-class values — not assignable to state variables, not passable as payload. This is a
precondition that makes the rest of the translation well defined, not an apology.

**A caveat on that edit, added 2026-08-17.** An earlier draft of this entry proposed
`Type ::= int | boolean | byte | short`. Measured against the paper, that is unmotivated: **`int` is
the only type appearing in any example in the paper**, and `boolean`, `byte`, `short`, `long`,
`double`, `float`, `char` and `string` occur zero times in the whole document. Proposing four types
where the paper exhibits one invents a specification rather than repairing one. Either narrow the
production to what the paper uses, or state explicitly that the type set is inherited from Timed
Rebeca and is deliberately not re-specified here.

---

## P7 — §III-E prescribes `schedule` for internal sends, but the shipped fixture emits a `timer`

**Claim in the paper:** an internal (self) send becomes `act.schedule(v, d ms)` on a logical action.
Fig. 5 has no `timer` production at all.

**Why it diverges:** the checked-in fixture
`tests/benchmarks/global-multi-actor-payload--external-send--positive/expected/lf-source/V0Controller.lf`
renders the `keepAlive` self-send as `timer keepAlive(1 msec, 1 msec)` — a construct Fig. 5 does not
contain, and one with different semantics: it fires unconditionally forever, rather than only when the
message server body executes.

**Evidence:** the fixture, read directly; Fig. 5, quoted.

**Note on direction:** here the **repo** is the more likely offender, not the paper. Recorded so the
divergence is not lost, and so the fixture is revisited at stage D/E rather than being treated as
ground truth for internal sends.

---

## P8 — a self-send contending with an external send is not addressed

**Claim in the paper:** §III-D orders the *k* senders to a message server by actor priority, treating
them uniformly.

**Why it is incomplete:** per §III-E an internal send becomes a **logical action** while an external
send becomes a **port**. When both target the same message server, the two arrivals reach the
receiving reactor through different LF constructs, so ordering them against each other requires the
action-triggered reaction to be interleaved into the priority-sorted port reactions at the receiver's
own priority position. §III-D as written has no place to put it.

**Evidence:** measured, 2 of 49 models — `hybrid` (`node0.processData <- {node0, switch0}`) and `ASPIN`
(17 such sites, e.g. `r00.give_Ack <- {r00, r01, r03, r10, r30}`).

**Suggested edit:** extend §III-D's ordering to range over the receiver's own priority alongside its
senders'. Cheap in the paper, cheap in stage F, expensive to retrofit later.

---

## P9 — a corpus-inventory correction, not a paper claim

`noc-prop/routings-detailed.rebeca` was previously recorded as the largest model at "109 instances /
783 lines." Its entire `main` block is inside a `/* ... */` comment, so the model has **no live main**
and cannot be instantiated or measured. The class declarations are real; the instantiation is not.
Recorded here so the 49-model denominator is stated honestly: 43 statically analysable, 5 non-static
(P6), 1 with no live main.

---

## P10 — Fig. 4 rejects Fig. 1a and Fig. 2a, the paper's own examples

This is the most concrete defect in the ledger, because it needs no interpretation: a frontend that
implements Fig. 4 literally fails on the figures printed earlier in the same paper. Three independent
causes.

**Cause 1 — `knownrebecs` is mandatory and cannot be empty.**
`ClassDecl ::= reactiveclass C(IntLit) {KnownRebecs Vars Constructor? MsgSrv*}` puts no `?` on
`KnownRebecs`, and `KnownRebecs ::= knownrebecs { Type id+ ;}` requires `id+`, at least one name. But
**Fig. 1a line 14 is `knownrebecs { }`** and **Fig. 2a line 30 is `knownrebecs { }`**. Neither is
derivable.

**Cause 2 — `statevars` is mandatory.** `Vars` also carries no `?`. But **Fig. 2a's `Controller`,
lines 29-34, has no `statevars` block at all** (and no constructor, which `Constructor?` does permit).
Not derivable.

**Cause 3 — two known rebecs of different types are not derivable.** `KnownRebecs` has exactly one
`Type`, one `id+`, and one `;`, so it declares one type group. A class knowing both a `Sensor` and an
`Actuator` cannot be written. The real Rebeca parser accepts repeated groups — its field is
`List<FieldDeclaration> knownRebecs` — so this is a transcription failure in the figure rather than a
language restriction.

**Evidence:** Fig. 4 and the two figures read directly from the PDF, pages 2, 7 and 13. The parser
field is read from the Maven sources in the FMCAD artifact zip.

**Suggested edit:** `ClassDecl ::= reactiveclass C(IntLit) {KnownRebecs? Vars? Constructor? MsgSrv*}`
and `KnownRebecs ::= knownrebecs { (Type id+ ;)* }`, with `Vars` likewise closed over an empty body.
All three edits are mechanical and none touches the semantics.

**What the tool does:** accepts all three shapes deliberately, recorded as D1-D3 in
`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`. Enforcing Fig. 4 here would have been the
literal-minded choice and the wrong one.

---

## P11 — `Expr` has no production anywhere in the paper

**Claim in the paper:** none, and that is the finding. `Expr` is used **7 times** in Fig. 4 — in `if`,
all three `for` slots, assignment, send arguments, and `after` — and never defined. No operators, no
literals, no precedence, no typing rule. It is not alone: Fig. 4 has thirteen left-hand sides and
leaves **eight** symbols undefined (`Expr` 7 uses, `Type` 4, `v` 4, `IntLit` 3, `C` 3, `rebecName` 3,
`msgsrvName` 2, `id` 1). Fig. 5 has the same gap and additionally leaks Fig. 4's `Stmt` into its
`for(Stmt; Expr; Stmt)` production without saying that the two languages share a statement class.

**Why it matters, concretely:** the paper's only handles on expressions are semantic and opaque —
§II-A p. 3, *"The function eval(expr, e) computes the result of an expression expr under the current
valuation e"*, and §IV p. 9, *"DTR expressions are translated directly into equivalent LF code"*.
Neither pins down a syntax. So **no expression restriction the frontend imposes can cite the paper**,
and equally no expression the frontend accepts can be justified by it. Any claim of the form "our
translator supports the paper's expression language" is unfalsifiable as the paper stands.

**Evidence:** Fig. 4 and Fig. 5 read directly; the two prose sentences quoted; symbol counts taken
from the transcription in `docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`.

**Suggested edit:** add `Expr` and `Type` productions, even minimal ones, and a line stating which
symbols are lexical (`IntLit`, `C`, `rebecName`, `msgsrvName`, `v`, `id`) so their absence reads as
deliberate. Also collapse `rebecName` and `id`, which are used interchangeably for instance names
with no stated distinction, and either connect `RebecExpr`'s `rebecName` to `KnownRebecs`'s `id` in the
grammar or state §III-A's "sends only to known rebecs" as an explicit side condition — as written,
nothing in Fig. 4 requires a send target to be a known rebec.

**What the tool does:** fixes an expression language as its own choice and says so, D5 in the fragment
document.

---

## P12 — Fig. 4's `for` loop is unusable, and Fig. 4 and Fig. 5 disagree about loop headers

**Claim in the paper:** `Stmt ::= … | for (Expr? ; Expr? ; Expr?) {Stmt*} | …` in Fig. 4, versus
`LFStmt ::= … | for(Stmt; Expr; Stmt){LFStmt*} | …` in Fig. 5.

**Why it is wrong:** in Fig. 4 assignment is a `Stmt`, not an `Expr`, so no assignment can appear in
the init or update slot. Combined with P11 — `Expr` having no production, hence no increment operator
and no comma operator — **the ordinary loop `for (i = 0; i < n; i = i + 1)` is not derivable from
Fig. 4 at all.** Every slot can hold only an undefined `Expr`. Fig. 5's LF form has the slots right;
the two figures simply disagree, and the DTR one is the broken one.

That the loop is thereby unusable rather than merely restricted is an inference, since the paper never
exhibits a DTR `for` loop. It is a safe one: §V claims the benchmark suite exercises control flow, and
no loop that terminates can be written in Fig. 4's shape.

**Evidence:** both figures read directly from page 13.

**Suggested edit:** give Fig. 4 the same header shape as Fig. 5, `for (Stmt? ; Expr? ; Stmt?)`, and
note that the statement slots are restricted to assignment. One-token fix.

**What the tool does:** follows Fig. 5's shape, D4 in the fragment document.

---

## P13 — Fig. 5 hardcodes `target Cpp;` but the evaluated models are C

**Claim in the paper:** `LFProgram ::= target Cpp; Reactor+ MainReactor`. The target is a terminal in
the grammar, so every LF program the figure derives is a Cpp program.

**Why it is wrong:** §V p. 9 says *"Because the LF verification backend supports only C, RQ1 uses
C-target LF models; ReLico otherwise generates LF/C++."* So the models behind the paper's own
evaluation — 20 benchmarks — are **not derivable from Fig. 5**. The grammar excludes the artifact the
results were produced from.

**Evidence:** Fig. 5 and §V read directly from the PDF.

**Suggested edit:** `LFProgram ::= target Target ; Reactor+ MainReactor` with
`Target ::= C | Cpp`, or drop the target line from the grammar and state it in prose. Worth doing
because a reader reproducing RQ1 hits this immediately.

**Second-order note:** this also affects P2's aside about the stray semicolon. If the target line is
generalized, the semicolon question is settled at the same time.

---

## P14 — the queue bound is mandatory syntax with no semantics, and overflow-freedom is assumed rather than checked

**Claim in the paper:** `reactiveclass C(IntLit)` makes the queue size mandatory (R7), and Theorem 1
assumes the source model is overflow-free — §IV p. 8, in full: *"Now we prove that the DTR model M_dtr
is weakly bisimilar to its LF translation M_lf, assuming M_dtr is overflow-free (no dropped
messages)."*

**Why it is a gap:** these two facts are never connected, and neither is discharged.

- `IntLit` occurs in exactly **3 places in the paper, all inside Fig. 4.** The queue bound is never
  mentioned in the semantics, never appears in a rule, and is never related to overflow-freedom.
- The DTR semantics contradicts the existence of a bound: §II-A p. 3 models the bag as unbounded —
  *"The message bag for an actor x ∈ AID, denoted by b_x, is modeled as a multi-set of time-tagged
  messages"* — and Table I's `SEND` rule adds unconditionally, `b_y ∪ {(x, y, ms, v⃗, e_y(now) + d)}`,
  with no capacity test. **No rule in Table I can drop a message.**
- So within the paper, overflow is not merely unchecked, it is *unreachable*: the hypothesis of
  Theorem 1 is vacuously true of the semantics the paper defines, while being a real and violable
  condition in the tool that RMC actually runs. The mandatory `IntLit` is decoration.

This matters for a reader trying to trust Theorem 1, because the hypothesis they must discharge is
about a system the paper does not model. `phils` makes it concrete: `reactiveclass Philosopher(3)` has
a queue bound of 3, small enough that overflow is reachable under RMC.

**Evidence:** occurrence counts and all three quotations taken directly from the PDF. Queue bound
availability in the AST measured from the artifact zip: `ReactiveClassDeclaration.getQueueSize()`
exists and returns the header integer, and all four Java exporters in this repository currently
discard it.

**Suggested edit:** either give the bound semantics — a capacity side condition on `SEND`, and an
overflow transition or a stuck state — or state plainly that the bound is carried for compatibility
with Rebeca tooling and that overflow-freedom is a hypothesis discharged externally by the model
checker. The second is cheaper and honest; the first is what makes Theorem 1's hypothesis meaningful.

**What the tool does:** carries `queueBound` into the JSON without enforcing it, and records
overflow-freedom as a documented assumption rather than a checked property (design §5.6). The general
frontend does the same and the repository-side detail is recorded as F18 in
[`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md): `queueBound` is decoded from the wire and then dropped,
because `DTR.GeneralModel` has no field for it and no rule of the semantics could consult one.

---

## P15 — an external send's delay is a run-time expression in DTR and a compile-time constant in LF, and the mapping does not say so

**Claim in the paper:** §III-E p. 6, in full: *"DTR's `after(d)` maps to LF timing in two ways. For
internal sends, delay d becomes a `schedule()` call on a logical action: `self.sendReading(v) after(5)`
(Fig. 2a, line 11) → `sendReading.schedule(v, 5ms)` (line 10). For external sends, delay maps to an
`after` clause on the connection: `c.receiveReading(v) after(2)` (line 10) → LF connection with
`after 2ms` (line 38)."* Table III states the same mapping in one row: `r.m() after(t)` ↦ *"output/input
ports and a connection `after t`"*. Fig. 4 writes the source production as `(after(Expr))?`.

**Why it is a gap:** the two halves of §III-E are presented as symmetric, and they are not. The internal
half is sound for any delay; the external half is sound only for a constant one, and no restriction to
constants appears anywhere.

- Fig. 4 admits an arbitrary `Expr` as the delay. On the DTR side that delay is a value carried into the
  bag: Table I's SEND rule adds `(x, y, ms, v⃗, e_y(now) + d)`, quoted in P14 above from p. 3. That `d` is
  an *expression* under Fig. 4 and a *value* in the rule means an evaluation happens at send time, in the
  sender's state — **inferred**, from the two together rather than from a rule that says so.
- The LF side takes its delay from somewhere else entirely. Table II's EXTERNAL SEND rule reads the delay
  out of `portMap(out) = (z, in, d)` — that is, `d` is a property of the **connection**, fixed when the
  program is elaborated, not a value the sending reaction computes. The paper's own semantics therefore
  exhibits the mismatch it does not mention.
- So `c.receiveReading(v) after(delayVar)`, legal under Fig. 4, has **no image** under §III-E's external
  mapping. There is no LF connection to write it as, because there is one connection and it needs one
  delay while the source can produce a different delay per send.
- The asymmetry is what makes this easy to miss: the identical construct on the internal path translates
  without trouble, since `schedule(v, d)` takes its delay as a run-time argument. Every delay in every
  example in the paper is a literal, so the distinction never surfaces.
- §III-G *Translation Limitations* is the natural place to state it and does not: it lists exactly two
  exclusions — models with unresolved observable choices, and multiple identical messages from one sender
  to one receiver at the same logical time. A reader who checks their model against §III-G will conclude a
  computed external-send delay is supported.

**Evidence:** all quotations taken directly from the PDF, pp. 6-7 — §III-E, Table II's EXTERNAL SEND rule,
Table III's `r.m() after(t)` row, and §III-G in full. The Fig. 4 production is cited from
[`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`](dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md) D9 per
this file's convention. The claim that an LF connection delay is fixed at elaboration time is grade **(d)**
— stated by the project lead, 2026-08-19: *"lf delay has to be static"* — and is the one thing here not
measured against `lfc 0.11.0`; an `lfc` probe would upgrade it. See F13.

**Suggested edit:** add one sentence to §III-E restricting the external-send delay to a compile-time
constant, and one line to §III-G recording it as a third limitation. The internal-send half needs no
change, and saying so explicitly is worth the words, because the restriction looks like it should apply to
both and does not.

**What the tool does:** enforces the restriction (D9) — an `after` delay must be a non-negative integer
literal — and represents it as `Delay : Nat` in `GeneralStmt`, so a non-constant delay is unrepresentable
rather than merely rejected. The restriction is applied to internal sends too, which is stricter than this
finding requires; that is deliberate for now, since stage D translates neither, and it is the kind of
over-restriction that should be revisited when internal sends acquire a translation rather than left to
harden by default.

---

## P16 — both TAKE rules are guarded by a predicate the paper never defines, and without it time cannot advance

**Claim in the paper:** Table I's TAKE rule is guarded by `enabled_m((y, x, ms, v⃗, ar_m), b_x)`, and Table
II's LF TAKE rule by `enabled_tr((r, ep, ν⃗, ar_r), q_r)`. Neither predicate is defined anywhere in the
paper, including both appendices.

**Why it matters:** everything that decides *which* pending message an actor takes lives inside that
predicate. TAKE's only other premises are that the message is in the bag and that the actor is between
message servers (`π_x = ε`); **no premise mentions time.** Read literally, Table I therefore lets an actor
take any message in its bag, including one whose arrival is still in the future.

That is not a slack reading, it is a fatal one, and the reason is TIME PROGRESS. TIME PROGRESS fires only
when `s ̸--ms-->` and `s ̸--τ-->`, i.e. when no TAKE is available anywhere. If `enabled_m` does not compare
`ar_m` against the clock, then every actor with a non-empty bag has a TAKE available, so TIME PROGRESS can
fire only once all bags are empty — at which point its own premise takes a minimum over the empty set.
**The semantics as printed has no time progress at all**, and the entire timed behaviour of DTR rests on a
clock comparison that appears nowhere except inside an undefined symbol.

**The description is not missing — it is in the prose, three times.** §II-A: *"A rebec takes a message with
the earliest arrival time from its message bag and executes its corresponding message server ... atomically
(without interruption)"*, then *"in the case of having messages with the same earliest arrival time, the
order of the execution of their corresponding message servers is non-deterministically chosen"*, which p. 3
narrows to *"We use DTR, where designer-specified actor and message-server priorities resolve observable
same-time choices."* The LF side gets the same treatment in §III-B: *"The TAKE rule expresses that a
reactor can take a trigger from its queue when the trigger has the minimum arrival time."* So the rule is
stated three times in words and zero times in the semantics. The gap is easy to miss precisely because the
prose is complete: `enabled_m` reads as a forward reference to a definition that never arrives.

**It is load-bearing for the proof.** Lemma 1's inductive step reasons about the missing content directly:
*"The DTR take rule removes the earliest pending message and executes the associated reaction body. The
corresponding LF take rule removes the earliest pending trigger."* The word "earliest" is doing real work
there — the bijection needs both sides to pick corresponding elements — and it is imported from §II-A's
prose, not from the rule the sentence names. The singular *"the earliest"* additionally presumes uniqueness,
which §II-A has already said may fail; what happens when it does is P4.

**Evidence:** grade (c), quoted directly from the PDF. Measured lexically over the extracted text of the
whole paper: `enabled_m` occurs **once** (Table I, p. 4) and `enabled_tr` **once** (Table II, p. 6); the
string "Definition" occurs twice, both introducing Definition 1 (Weak Bisimilarity). There is no third
occurrence of either predicate at which it could be defined. The consequence for TIME PROGRESS is
**inferred**, from TIME PROGRESS's own premises together with the absence of a clock premise in TAKE.

**Suggested edit:** define it once, beside Table I, as the conjunction of the two conditions the prose
already gives — `ar_m` minimal among the arrival times of `b_x ∪ {m}`, **and** `ar_m ≤ e_x(now)` — and say
that a tie among minima is resolved by message-server priority (see P4 for the case where priorities tie
too). The LF counterpart needs the same treatment with `q_r` and the current tag. Both are one line each,
and stating them is what makes TIME PROGRESS applicable.

**What the tool does:** defines it, in `Relico/DTR/GeneralState.lean`, and makes both halves explicit.
`earliestDueArrival b now` is the minimum `arrival` among the messages of `b` with `arrival ≤ now`, or
`none`; `GeneralActorState.dueArrival` is that at the actor level; `GeneralConfiguration.readyActors` is the
cohort of actors with something due, each tagged with the arrival it would take, in the model's instance
order. The tie half is deliberately *not* supplied: `readyActors` returns the cohort and selects nothing,
because selection is what priority decides and priority arrives in stage G. So the implementation is
strictly **more specified** than the paper on dueness and exactly as unspecified on ties, which is the
honest split rather than a convenient one. A divergence in the direction of precision is the easiest kind to
leave unrecorded and the most misleading to.

Two smaller divergences fall out of that and are recorded here rather than given entries of their own.
First, the repo's actor state is `(valuation, bag)` with no counterpart of the paper's third component
`π_x`, so TAKE's `π_x = ε` premise is currently inexpressible: statement execution is stage H, and until
then `readyActors` characterises an actor that *has something due*, not one that *may take it now*. Second,
the guard is written `arrival ≤ now` where the paper's own rules only ever produce `=`: every arrival is at
least `now`, since SEND adds `e_y(now) + d` with `d ≥ 0` and TIME PROGRESS advances to the global minimum,
so an actor's earliest due arrival equals `now` whenever it has one. That invariant is **inferred** from the
rules and is not stated in the paper; the strict inequality is therefore unreachable rather than wrong, and
it is kept because no type in the development enforces reachability.

---

## P17 — TIME PROGRESS writes the message tuple with sender and receiver transposed

**Claim in the paper:** Table I, TIME PROGRESS, premise:
`ar_min = min_{x∈AID} {ar_m | s(x) = (e_x, (x, y, ms, v⃗, ar_m) ∪ b_x, ϵ)}`.

**Why it is wrong:** p. 3 defines a message of `b_x` as `(y, x, ms, v⃗, ar_m)`, *"where y is the sender, x is
the receiver"*, and TAKE uses exactly that order two rules earlier. Here the same bag's message is written
`(x, y, …)`, which puts the bag's owner in the **sender** slot. Read literally the minimum ranges over
messages that `x` sent, and those are in no bag at all; `y` is also left free in the comprehension with
nothing to bind it. The intended reading is not in doubt and the fix is one transposition, which is the whole
of the finding — but it sits in the premise that determines every logical time the system ever visits, so it
is worth fixing rather than leaving for a reader to repair silently.

**Evidence:** grade (c), quoted directly from the PDF — the tuple definition on p. 3, the TAKE premise and
the TIME PROGRESS premise on p. 4, all three compared side by side.

**Suggested edit:** write the premise as
`ar_min = min_{x∈AID} {ar_m | s(x) = (e_x, (y, x, ms, v⃗, ar_m) ∪ b_x, ϵ)}`, and bind `y` explicitly if the
notation elsewhere in the table is tightened the same way.

**One further thing to check while fixing it.** The comprehension is restricted to actors with `π_x = ϵ`, so
an actor part-way through a message server contributes no arrival to `ar_min`. With rules for every statement
form that is harmless, because such an actor has a `τ`-transition and TIME PROGRESS could not have fired.
Table I has no rule for `for`, though, while Fig. 4's grammar admits one — P12 — so an actor whose remaining
statements begin with a loop has neither a `τ`-transition nor a place in the minimum. Whether that is
reachable depends on how P12 is resolved, which is why it is noted here rather than filed: it is **inferred**,
and the inference is contingent on another open entry.

**What the tool does:** cannot exhibit either problem, and for a reason worth stating because it is a third
divergence rather than a defence. `GeneralMessage` has fields `sender`, `messageName`, `payload`, `arrival`
and **no receiver at all**: a message's receiver is the bag it sits in, since the configuration keys bags by
actor name. The paper's tuple carries the receiver redundantly with the bag containing it, and the
development drops the redundancy instead of cross-checking it — the same choice F10 records for two
redundant schema fields. So there is nothing to transpose, and the position-free field names mean a
sender/receiver mix-up is a type error rather than a notation slip. The state also has no `π_x` for an actor
to be stuck in (see P16). Time progress itself is not implemented at this stage, so the premise this entry
corrects has no counterpart in the development yet. It will in stage D, and the entry exists partly so that
it is transcribed from a corrected rule.

---

## P18 — Appendix A and Fig. 5 disagree about whether the LF syntax is complete

**Claim in the paper:** §II-B says *"the complete LF syntax is provided in Appendix A"*, Appendix A is
titled *"Complete Syntax"* and opens *"we give the complete syntax for Deterministic Timed Rebeca and
Lingua Franca"*. Fig. 5's own preamble says *"This fragment is not intended to be the complete LF language
syntax. It includes only the constructs needed by our translation."*

**Why it matters:** this is the entry that decides the standing of every other "the grammar admits X"
finding, so it is filed first among the new ones even though it is the least interesting on its own. If
Fig. 5 is a complete syntax of the fragment, then a production it contains that the translation never
emits and `lfc` rejects is a defect in the grammar — that is P2, and it is P19. If Fig. 5 is only an
illustration, those are not defects, but then Appendix A's title and §II-B's sentence are wrong instead.
One of the two has to give. The figure's internal evidence points one way: it contains productions the
translation demonstrably does not need, indexed ports (P2) and an optional `after` (P19), so the *"only
the constructs needed by our translation"* half of the preamble is already false on its own terms,
independently of the completeness question.

**Evidence:** grade (c) — §II-B's sentence, Appendix A's title and Fig. 5's preamble, all quoted from the
PDF.

**Suggested edit:** pick one. Either retitle Appendix A to name the fragment rather than claim
completeness and drop *"complete"* from §II-B, keeping Fig. 5's disclaimer; or promote Fig. 5 to a real
complete grammar of the fragment and prune the productions the translation cannot produce. The first is
far cheaper and is all the surrounding argument needs.

**What the tool does:** takes the strict reading for itself. The development's LF AST is closed under what
the printer emits, so a Fig. 5 production with no constructor is a recorded omission rather than an
oversight — `docs/STAGE_C_DESIGN.md` §7 lists stage C's, one line per production, with the stage that owes
each. That discipline is only possible against a grammar that claims to be exact, which is the practical
reason to want the ambiguity resolved rather than tolerated.

---

## P19 — `Connection`'s `after` clause is optional in Fig. 5 and mandatory in §III-E

**Claim in the paper:** Fig. 5 gives
`Connection ::= ins.outPort([Expr])? → ins.inPort([Expr])? (after delay)? ;`, making the delay optional.
§III-E says *"An external send in DTR with no explicit `after` is treated as delay 0. Our tool translates
it to an LF connection with `after 0ms`… This avoids causality loops: LF connections without `after` are
instantaneous (same tag (t, m)), and cycles cause compiler rejection."*

**Why it is wrong:** §III-E does not merely prefer the delayed form, it states why the delay-free form is
unusable — it is what produces the causality cycles that make `lfc` reject the program. So the grammar's
`(after delay)?` describes a connection the translation must never emit, and a reader implementing from
Fig. 5 alone would emit it. The contrast with P2 is what makes this the more dangerous of the two: there
the surplus production is rejected by `lfc` outright, so the mistake announces itself. Here the surplus
production compiles fine in the acyclic cases and fails only once a cycle exists, which may be a model the
implementer never tries.

**Evidence:** grade (c), both passages quoted from the PDF. The mandatory direction is corroborated at
grade (a) by the three committed port-bearing LF fixtures, whose every connection is spelled
`after 0 msec` and which `lfc 0.11.0` accepts.

Probe 10 of `tools/paper-measurements/lf_semantics_probe.sh`, run on 2026-08-19, isolates the defect from
two things it could be mistaken for. First, the **unit spelling is not the problem**: `after 0 msec`,
`after 0ms` and `after 0 ms` all compile and run under `lfc 0.11.0`, so the paper's `0ms` and `2ms` are
valid LF and this entry is about the `?` alone. Second, §III-E's *reason* is **measured true, not merely
quoted**: the `self_cyclic` case builds a real causality loop — `reaction(in) -> out` connected back to
`in` — and it is schedulable precisely because the connection carries `after 0 msec`, printing
`RELICO_SELF_CYCLIC 1`, `2`, `3` at increasing microsteps. The paper's justification for making the delay
mandatory therefore holds; only the grammar contradicts it.

**Suggested edit:** drop the `?` —
`Connection ::= ins.outPort([Expr])? → ins.inPort([Expr])? after delay ;` — and keep §III-E's sentence as
the justification for it. If a delay-free connection is wanted in an example, say in the figure that the
translation never produces one. This is separable from P18: the `?` is wrong on either reading, because a
grammar for *"the constructs needed by our translation"* should not include one the translation is
forbidden to use.

**What the tool does:** stage C's `GeneralConnection` carries `delay : Delay`, not `Option Delay`, so the
delay-free connection is unrepresentable rather than merely unused, and `Delay`'s single `value : Nat`
field (`Relico/Common/Time.lean:15`) makes the delay static and non-negative structurally. The staticness
half of that is P15's subject, not this entry's.

---

## P20 — no rule is given for naming the generated ports, and the two figures disagree

**Claim in the paper:** Table III maps `knownrebecs` to *"port declarations and connections in main"* and
`r.m() after(t)` to *"output/input ports and a connection after t"*. Nothing anywhere says what those
ports are called.

**Why it matters:** for a translation whose §III-D argument turns on each sender getting *a unique input
port on the target reactor*, the naming function is not cosmetic — it is the thing that has to be
injective, and uniqueness of the generated ports is the whole mechanism. The two worked examples use two
different schemes. Fig. 1b gives `Controller` an `input receiveReading:int;`, named after the DTR msgsrv.
Fig. 2b gives `Controller` an `input readingFromTemp:int;` and an `input readingFromSmoke:int;`, named
after the output port plus `From` plus the capitalized sender *instance*. Neither scheme accounts for the
output port: both figures declare `output reading:int;` on the sender while the msgsrv being called is
`receiveReading`, so the sender-side name follows no stated rule at all. A reader cannot reproduce any of
the three names from the paper.

**Evidence:** grade (c), Fig. 1b and Fig. 2b transcribed from the PDF and compared name by name.

**Suggested edit:** state the naming function once, inside §III-D's construction, and make its injectivity
explicit — for instance target input port `= <msgsrv> ++ "From" ++ capitalize(<sender instance>)` and
source output port `= <msgsrv> ++ "To" ++ capitalize(<receiver instance>)`, or one output port per msgsrv
broadcast to every receiver. Injectivity then follows from DTR instance names being distinct, which they
are. Then redraw Fig. 1b so its single-sender case is that same function's output instead of a second
scheme, since a reader will reasonably read the simpler figure as the general rule.

**What the tool does:** nothing yet, deliberately. Stage C prints only port names it is handed and invents
none (`docs/STAGE_C_DESIGN.md` §7), because a naming scheme chosen inside the printer would be
unreviewable — it belongs to the translation, where it can be stated once and proved injective. This entry
is the reason stage E and stage F are blocked on a paper decision and not only on code, and it is the
cleanest example in this file of a gap that a prose proof can leave open and an implementation cannot.

---

## P21 — both figures render DTR state variables as LF parameters, contradicting Table III

**Claim in the paper:** Table III maps `statevars ↦ state variables`. Fig. 1b writes
`reactor TempSensor(v:int=0)` and `reactor Controller(v:int=0)` with
`main reactor { sensor = new TempSensor(v=1); controller = new Controller(v=2); … }`, and declares no
`state` anywhere. Fig. 2b does the same.

**Why it is wrong:** an LF parameter and an LF state variable are different constructs. A parameter is
fixed per instance at instantiation; a state variable is mutable across reactions. DTR `statevars` are
assigned by message servers — Fig. 4's own `var = Expr;`, exercised in Fig. 1a — so they have to become
state, exactly as Table III says. As drawn, the figures' reactions could not assign `v` at all, which
means the figures cannot be an instance of the mapping the table states.

A second, smaller problem falls out of the same lines: `ArgList ::= Expr (, Expr)*` cannot derive `v=1`.
The named-argument form both figures use is not in Fig. 5, which is a grammar gap of the same kind as P22.
Taken with P10, where Fig. 4 rejects Fig. 1a and Fig. 2a on three independent counts, the pattern is that
the figures and the grammars were written against each other only loosely on both sides of the
translation — which is worth one sentence in the paper's own terms, because a reader calibrates on the
figures.

**Evidence:** grade (c), the Table III row and both figures quoted from the PDF.

**Suggested edit:** redraw both figures per the table — a `state v:int = <initial>;` declaration inside the
reactor and `new TempSensor()` in main — and state explicitly where per-instance initial values go, since
that is the job the parameters appear to be doing. DTR constructor arguments are already that mechanism,
so the natural sentence is that `statevars` become `state` declarations and a constructor's argument
values are applied in the startup reaction. If instead a parameter really is wanted alongside the state
variable, the named-argument form still needs adding to `ArgList`.

**What the tool does:** follows Table III rather than the figures, and this is measured, not asserted. The
committed `lfc`-accepted output in
`tests/benchmarks/bound-payload--dispatch--positive/expected/lf-source/V0Controller.lf` declares
`state x: int = 0`, replays the constructor as `x = 0;` inside `reaction(startup)`, and instantiates with
`main reactor { controller = new Controller() }` — no parameter list, no arguments. Stage C keeps
argument-free instantiation for this reason (`docs/STAGE_C_DESIGN.md` §6.5); adopting the figures' shape
would be a translation change, and one that would lose assignability.

---

## P22 — `act.schedule(delay)` has no payload slot, so §III-C's own example is underivable

**Claim in the paper:** Fig. 5 gives `LFStmt ::= … | act.schedule(delay); | …`, with one argument. §III-C
prints `sendReading.schedule(v, 0ms)`, with two.

**Why it is wrong:** Fig. 5 deliberately admits a *typed* logical action —
`ActionDecl ::= logical action act(: Type)? ;` — and a typed action exists precisely to carry a value that
nothing in `LFStmt` can then supply. The optional action type and the single-argument `schedule`
contradict each other inside one figure, and the paper's own worked translation of a payload-carrying
self-send uses the two-argument form. This is P19's mirror image: there the grammar is too permissive for
what §III-E requires, here it is too restrictive for what §III-C does.

**Evidence:** grade (c) for the contradiction — Fig. 5's `LFStmt` and `ActionDecl` productions and
§III-C's statement, quoted from the PDF. Corroborated at grade (a) by the committed fixture
`bound-payload--dispatch--positive`, whose `lfc`-accepted output is `dispatch_action.schedule(1, 1ms);`,
so the two-argument form is the one that compiles.

**Suggested edit:** `act.schedule((Expr ,)? delay) ;`, matching how the rest of Fig. 5 marks optional
parts. While fixing it, the read side is worth a sentence too: the payload has to be recovered in the
receiving reaction, and `LFStmt`'s `var = Expr;` is the only candidate production, but nothing says whether
`Expr` may mention an action or a port — and `Expr` has no production at all, which is P11. So this is a
*not stated* rather than a prohibition, and it is noted here instead of filed separately because the fix is
one clause in the same production the payload slot lands in.

**What the tool does:** emits the two-argument form, and refuses more than one payload value with
*"has more than one payload value; the current C++ printer foundation supports at most one integer
payload"* (`Relico/LF/MultiStorePayloadCppPrinter.lean:93-96`). So the implementation sits strictly
between the two: more than Fig. 5 can derive, less than a general payload. Stage C inherits the refusal at
the same layer rather than widening it (`docs/STAGE_C_DESIGN.md` §6.6), so the limit stays in one place and
stays visible.



