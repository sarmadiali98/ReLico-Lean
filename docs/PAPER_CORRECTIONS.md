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

Fig. 4 and Fig. 5 are transcribed in full, once, in
[`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`](dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md),
alongside the numbered restrictions R1-R24 that the frontend enforces and the deliberate divergences
D1-D6. Entries here cite that document rather than re-quoting the grammar, so that a delimiter fix
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
overflow-freedom as a documented assumption rather than a checked property (design §5.6).
