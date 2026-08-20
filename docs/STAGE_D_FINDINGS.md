# Stage D findings — what building the DTR → LF translation turned up

**Why this file exists.** [`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md) opened the `F` series with F1–F20 and
stated the rule it follows: [`PAPER_CORRECTIONS.md`](PAPER_CORRECTIONS.md) records places where the *paper*
says something this tool cannot accept, and an `F` finding records places where *this repository* — an
exporter, a design document, or an earlier family's Lean module — says something the next family could not
accept, or says nothing where it needed to say something. This file continues that series with F21–F33.

It also discharges a task the stage D design set for itself. §10.1 of
[`STAGE_D_DESIGN.md`](STAGE_D_DESIGN.md) wrote F21–F29 into the design document as an interim measure,
observing that the ledger *"still lives under a gitignored `tmp/` path — which means the project's most
reusable artefact is the one thing a fresh clone does not get"*. This file is where stage D's range of the
series now lives, and it is committed.

**What is restated and what is not.** F21–F29 were reasoned out at length in the design document and that
reasoning is not copied here; each one below is stated with its grade, its current status, and a pointer to
where the argument lives. F30–F33 were found while writing the Lean and are stated in full, because this
file is the only place they are written down. Two of them contradict the design document that authorised the
work, which is the reason to write them down at all.

**Provenance rule**, unchanged from stage B. Every finding states how it is known, in one of four grades:

- **measured** — produced by running something: `lake build`, `lfc`, a probe script, or a gate. The run is
  named.
- **read** — read directly out of a file in this repository, cited as `path:line`.
- **decided** — a design choice with a stated reason, where the alternative was live and is recorded.
- **inferred** — reasoned from the above without being run. Labelled as such, and no soundness claim rests
  on this grade.

**What is deliberately not here.** Divergences between the paper and this repository belong in
`PAPER_CORRECTIONS.md` as `P` entries; divergences from the paper's *DTR fragment restrictions* belong in
`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md` as `D` entries, a series that is cited from Lean source
and is untouched by anything here. Where a finding is a mechanics measurement of no interest outside this
codebase, it is one paragraph rather than three.

---

## Numbering history, in full

Two renumberings happened before any of this was committed, and both are recorded rather than tidied away.

**D1–D9 → F21–F29, at design review.** The design document numbered its own findings `D1–D9` when first
written. That collided with `docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`, which already defines a
`D1–D9` series meaning *divergences from the paper's DTR fragment restrictions* — and those labels are cited
from Lean source, at `Relico/DTR/GeneralWellFormed.lean:92` and `:108`. The fragment series' own D8,
*"instance arguments may be boolean literals, not only integer literals"*, is close enough in subject to the
design's original D8 to mislead a reader badly. The mapping D1→F21 … D9→F29 was applied uniformly and no
citation of the fragment series was touched.

**Three printer citations, during implementation.** `Relico/LF/GeneralCppPrinter.lean` was written citing
F26 for the payload struct-name rule, F27 for the payload binder collision, and F29 for the named-argument
divergence. Re-reading design §10.1 showed all three disagreed with it: the struct-name rule is F25, the
binder collision is F29, and the named-argument divergence had no number at all. The file now cites F25, F29
and a newly filed F31, in that order, and F30 was free for the disagreement below. A citation that points at
the wrong finding is worse than no citation, because it reads as corroboration.

One further correction was applied in the same pass and is *not* given a number, because it never reached a
reader outside this stage: the printer's closing note claimed that `frontend/check-general-lf-target.sh`
pins the emitted program *"by comparing bytes"*. That script contains no byte comparison — it emits,
compiles and runs. The two pinned strings live in
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean` (`expectedProgramText` and
`expectedWidenedProgramText`), and the note now credits them and records the mis-credit.

---

## F21–F29 — carried over from the design, with their status after implementation

The argument for each of these is in [`STAGE_D_DESIGN.md`](STAGE_D_DESIGN.md) §10.1 and in the section it
cites. What is added here is the status: whether writing the Lean closed it, narrowed it, or left it exactly
where it was.

**F21 — "general" described the ports, never the data.** The LF half of the family was assembled from an
earlier integer-only, single-payload, parameterless family; five distinct gaps with one cause (§2). *Read.*
**Closed by stage D**: the widening landed in `Relico/LF/GeneralSyntax.lean`, and
`Relico/Translation/GeneralBasic.lean:229` records the shape of the gap at the declaration it made
untranslatable.

**F22 — stage C dropped a production it was quoting.** Fig. 5 spells `Reactor ::= reactor R (ParamList?)`
and stage C's own docstring quoted that line while omitting the parameter list, which made two instances of
one class with different constructor arguments indistinguishable in LF (§5.5). *Read.* **Closed**:
`renderGeneralParameterList` restores it, `assembleGeneralReactor_parameters` pins the translation half, and
the bridge assertions `PARAMETER_LIST_OMITTED_WHEN_EMPTY` and `PARAMETER_LIST_DECL` pin both branches — the
empty one being what keeps every stage C fixture byte-identical.

**F23 — three refusals blamed the target for our own limit.** They read *"the current C++ printer foundation
supports at most one integer payload"*. *Measured*, against `lfc 0.11.0`: a preamble struct compiles, runs
and carries its values, including a mixed `bool` field. **Closed**: the refusals are gone, the wording is
rewritten at `Relico/LF/GeneralCppPrinter.lean:48`, and the construct is now asserted three times over
(`STRUCT_ACTION_DECL`, `MULTI_VALUE_PAYLOAD_SCHEDULE`, `MULTI_VALUE_PAYLOAD_BINDERS`) and compiled by real
`lfc` in the target gate.

**F24 — a correction to our own record.** `-Wunused-private-field` fires only for a field neither read nor
written, so stage C's warning was narrower than recorded. *Measured.* **Closed as a record correction**; the
warning is still reachable, so the target gate's report-but-do-not-fail policy for warnings stays justified.

**F25 — the payload carrier's name is ours.** The paper supplies no naming rule, so
`<ReactorName>_<ActionName>_Args` is this project's invention, exactly as the port-naming rule of P20 is.
*Decided.* **Open by nature** — it is a divergence and not a defect, and it is filed so that the rule is
visibly ours rather than silently attributed to Table III. Cited at
`Relico/LF/GeneralCppPrinter.lean:288`.

**F26 — provisional, and stage D leaves it exactly where it found it.** Whether Fig. 5's `ActionDecl`
production admits a *typed* action at all, and whether it admits more than one payload value, has still not
been read against the PDF. Nothing is claimed either way here. It is recorded as an open check rather than as
a finding, because filing a paper fault on an unread production is the precise failure this project's trust
order exists to prevent, and the fact that stage D's implementation went green without reading it is not
evidence about the production.

**F27 — local message-server priority has no source of truth.** It appears in neither of the paper's SOS
tables and no tie rule is given, so what a translation should *do* with `msgsrv m(...) : 3` is undefined by
the paper. *Read.* **Open, and owned by stage G**: stage D drops the field deliberately rather than guessing,
and `assembleGeneralMessageReaction_priority` records the drop as a theorem so the field cannot be wired back
in without breaking a proof.

**F28 — narrowed twice, and still open in one place.** The design first claimed arity agreement between a
`schedule` and its action was *"unstateable at the LF level"*; reading `LF/GeneralWellFormed.lean` refuted
that, since `stmtWellFormed` already requires the lengths to agree. Stage D narrowed it again: the *instance*
half is now fully checked, because `argumentsMatchParameters` compares each argument's type against its
parameter's, and an instance argument is a value whose type is computable. What remains open is *expression*
type agreement inside a `schedule` payload, which needs a typing judgment on `LF.GeneralExpr`. *Read*, at
`Relico/LF/GeneralWellFormed.lean:136` and `Relico/LF/GeneralSyntax.lean:320`. The superseded wording is left
visible in the design document rather than rewritten, because a design that silently repairs itself is not
evidence of anything.

**F29 — the generated binder shares a scope with source identifiers.** `<action>_payload` sits in the same
C++ scope as the source-derived parameter binders beneath it, and nothing proves a model has no message-server
parameter of that name. *Read*, `Relico/LF/GeneralCppPrinter.lean:583`. **Open, and inherited rather than
introduced** — the earlier payload family emits a bare `auto payload = …`. Deriving the name from the action
narrows the exposure; closing it needs a freshness condition over a reactor's source identifiers, which is a
well-formedness obligation and does not belong inside a printer.

---

## F30 — one of the three refusals the design ordered removed had to stay

**What it is.** [`STAGE_D_DESIGN.md`](STAGE_D_DESIGN.md) §6 stated that the widening removes all three
refusals in the reaction parameter reader. Two of them did go. The multi-value *action* payload is now
printed, as a preamble struct bound once and destructured field by field; the parameterised *startup*
reaction now prints nothing, which is the correct emission and is finding F33 below. The third did not go: an
input port whose reaction declares two or more parameters is still refused, and
`Relico/LF/GeneralCppPrinter.lean:687` returns

> ``reaction `receive_reaction` for input port `in` declares more than one parameter; a port declares one
> type and so carries one value, and unlike a logical action it has no parameter list to destructure``

This is recorded as a disagreement with the document that authorised the work, not as a shortfall against it.
The design's premise was that these three refusals all blamed the target for a limit of ours, which was true
of the other two and is not true of this one.

**How it is known.** *Read.* `LF.GeneralPortDecl` has exactly two fields, `name : PortName` and
`declaredType : LF.GeneralType` — `Relico/LF/GeneralSyntax.lean:372`. A port therefore delivers one value of
one type. The action case is not analogous: `LF.GeneralActionDecl` carries a parameter *list*, which is what
gives the struct its fields and the destructuring its names. So there is no struct to name and no second
value to bind, and the two refusals that were removed were removed because a struct could be built, which is
the step unavailable here.

**Consequence, and who owns it.** Three parts, and the third is the one that matters.

Stage D does not reach this arm at all: it emits no ports, because the whole stage is defined as translation
*without* external sends. The refusal is exercised only by the bridge assertion
`MULTI_PARAMETER_PORT_REFUSED`, which calls `renderGeneralParameterRead` directly. That assertion is the only
reason this branch is known to say what it says rather than merely to exist.

Keeping an unreachable refusal is a deliberate cost. The alternative — deleting it and letting the
partiality vanish — would have made `renderGeneralParameterRead` total and removed an `Except` from the
printer's signature chain. It was rejected because a refusal that names an unrepresentable shape is
information, and the shape becomes reachable one stage later.

Stage E owns the meaning, and there is a candidate answer worth writing down while the reasoning is fresh: if
a message server of arity two is reached by an external send, its port could be declared with the payload
struct as its type — `input in: Receiver_m_Args` — at which point the reaction reads one value and
destructures it exactly as the action case does, and this refusal becomes unreachable by construction rather
than by the absence of ports. That is *inferred* and rests on `lfc` accepting a preamble struct as a port
type, which has not been measured; probe 10 measured struct payloads on actions only. Stage E must measure it
before relying on it, and if it fails, the refusal is the honest answer and the arity limit becomes a stated
restriction on the accepted fragment rather than a printer detail.

One thing the 2026-08-20 target gate did add here, and one thing it did not. It *did* move the action-side
half of route A from an ad-hoc probe onto a committed script: the translated program it compiles declares
`struct Configured_adjust_action_Args { int left; int right; bool flag; };` in a program-level
`public preamble`, gives a logical action that struct as its type, schedules it with a brace initialiser, and
destructures it by field name — and `lfc` plus the C++ compiler accepted all of it over printer output rather
than over hand-written LF. It did **not** touch the port position, because stage D emits no ports at all. So
the sentence above stands exactly as written: struct-as-port-type remains unmeasured, and it is the one
measurement stage E must take before this refusal can be called unreachable by construction.

---

## F31 — the emitted instance arguments are named, and Fig. 5's grammar cannot derive that

**What it is.** `renderGeneralInstance` emits `configuredOn = new Configured(bound=7, active=true)`. Fig. 5
gives `ArgList ::= Expr (, Expr)*`, which admits only positional arguments: there is no production for
`identifier = Expr` anywhere in the argument list. So the text this repository emits is not derivable from the
paper's own grammar.

The paper is not self-consistent here, and that is the more interesting half. Fig. 1b and Fig. 2b both write
`new TempSensor(v=1)` — the named form — which their own `ArgList` cannot produce. This project follows the
figures rather than the grammar, because the figures are what a target compiler was evidently run against.

**How it is known.** *Read*, for the divergence: Fig. 5's `ArgList` production, transcribed at
`docs/STAGE_C_DESIGN.md:187` and `docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md:86`, against the emitted
form at `Relico/LF/GeneralCppPrinter.lean:1046`. *Measured*, for the target's acceptance: the stage D
parameter probe compiled and ran a program whose instance line is exactly the one above, which is what
`docs/STAGE_D_DESIGN.md:341` records as a measured target form.

One correction to that measurement's standing. Unlike probe 10, the parameter probe was run ad hoc and its
script was never folded into `tools/paper-measurements/lf_semantics_probe.sh`, so a fresh clone cannot
reproduce it — the design document's prose is the only trace. That is repaired by construction rather than by
adding a script: the LF target gate's `emit-widened` cycle compiles and runs the translated widened program,
and that program contains the named-argument instance, so every green run of the gate re-measures it. If
`lfc` ever stops accepting the form, the gate fails instead of a paragraph going stale. Committing the probe
script is still owed and is on the open list.

That repair has since been exercised. On 2026-08-20 `frontend/check-general-lf-target.sh` ran green end to
end, and the `emit-widened` half of it compiled and ran a program whose main reactor is

```
main reactor {
  configuredOn = new Configured(bound=7, active=true)
  configuredOff = new Configured(bound=0, active=false)
}
```

with `lfc` reporting acceptance and the binary exiting cleanly. The named form's provenance is therefore no
longer an ad-hoc probe recalled in prose: it is *measured*, by a committed script, over text this repository
generated rather than text a probe hand-wrote. Note the exact scope of what that settles — it settles that
`lfc 0.11.0` accepts the named form. It says nothing about whether the positional form of Fig. 5's `ArgList`
would *also* be accepted, which was never measured and is not needed, since nothing here emits it.

**Consequence.** The divergence is one-directional and safe in the direction that matters: everything this
repository emits is accepted by `lfc`, and what is *not* accepted is the paper's grammar as a description of
the paper's own figures. It is filed as an `F` entry because the emission is ours, but the underlying fault is
the paper's, and a `P` entry recording that Fig. 5's `ArgList` cannot derive Fig. 1b's `new TempSensor(v=1)`
is the right home for it. That entry is not filed here — the `P` series has its own file and its own
numbering, and appending to it as a side effect of a stage D findings write is exactly the kind of drift this
file exists to prevent. It is on the open list below with the observation that the closest existing entry,
P21, is about *which source construct* becomes a parameter and not about the syntax of the argument list, so
this is a new entry rather than an extension of that one.

The pin is threefold and deliberately not a single assertion: the form is asserted as text
(`INSTANCE_WITH_NAMED_ARGUMENTS`), the argument-free form is asserted separately
(`INSTANCE_IS_ARGUMENT_FREE`, which is what keeps stage C's fixtures byte-identical), and the names come from
`program.reactor?` at print time rather than from a second stored list, so a name disagreement between the
instance and its reactor is unrepresentable rather than merely unchecked.

---

## F32 — nothing proves a translated program is well-formed, and the missing theorem looks false

**What it is.** `Relico/Translation/GeneralBasic.lean:58` states the obligation in the module's own words:

> One obligation is discharged nowhere yet, and is filed as **F32**: nothing proves that a program this file
> produces satisfies `LF.GeneralProgram.wellFormed`. The printer's refusals are justified in the design by
> appeal to well-formedness — an unresolvable instance, an argument list that disagrees with its parameter
> list — so until that theorem exists, *"the printer never refuses a translated program"* is an argument and
> not a fact. The `lfc` gate narrows it to one witness rather than closing it: the bridge test main asserts
> `wellFormed` of the program this file produces from its widened model, so the claim is checked for that
> model on every build and unproved for every other.

That is where stage D leaves the code. What was found afterwards, while writing this file, is worse than an
unproved theorem: the obvious statement of it — *if `compileGeneralModel m = .ok p` and `m.wellFormed` then
`p.wellFormed`* — appears to be **false**, with a small counterexample.

`LF.GeneralReactor.declaredNames` gained the parameter list in stage D, on the ground that a reactor parameter
is readable in a reaction body exactly as a state variable is, so parameters, ports, state variables and
actions are one LF name scope; `LF.GeneralReactor.wellFormed` then requires that union to be `Nodup`
(`Relico/LF/GeneralWellFormed.lean:84` and `:249`). The DTR side imposes no matching condition.
`DTR.GeneralModel.namesUniqueAndValid` (`Relico/DTR/GeneralWellFormed.lean:323`) requires distinct class
names, distinct known-rebec names, distinct message-server names and non-empty spellings — and mentions state
variables **nowhere at all**, let alone their relation to the constructor's formals. So a DTR class with a
state variable `x` and a constructor formal `x` satisfies `DTR.GeneralModel.wellFormed`; the translation is an
identity-shaped map on both lists and preserves both names; and the resulting reactor declares `x` twice.

**How it is known.** *Read*, for both predicates, at the four lines cited above. *Inferred*, for the
composition: no build has produced the counterexample, because stage D's assertion set was fixed before this
was noticed and no fixture exercises it. It is labelled inferred deliberately and no claim here rests on it
being true — the point of writing it down is that it is cheap to settle and expensive to discover later.

The experiment that settles it, stated precisely enough to run without rediscovering it: take
`widenedModel` from `frontend/lean-bridge/GeneralLfPrinterTestMain.lean`, rename one constructor formal of its
`Configured` class to the name of one of that class's state variables, and assert three things — that
`DTR.GeneralModel.wellFormed` accepts the model, that `compileGeneralModel` returns `.ok`, and what
`LF.GeneralProgram.wellFormed` then says about the result. If it says `false`, the theorem is refuted and the
fix is a DTR-side clause; if the translation refuses the model for some reason not visible from reading, the
finding downgrades to "unproved" and the reason gets recorded.

**Consequence.** Three, in increasing order of importance.

It was not folded into a new finding number. F34 was considered and rejected: this is the same obligation F32
already names, and splitting "the theorem is missing" from "the theorem is false" across two numbers would let
a reader close one and think the other was handled.

No assertion was added to stage D for it. The assertion count was stated before the gates ran and is not
adjusted afterwards, which is the rule that makes the count worth anything; and a hand-built DTR model
written to a predicate's shape rather than measured is exactly the kind of first-round-trip elaboration risk
this stage has been avoiding. It is on the open list as a stage E item instead.

It changes what stage E must do first. Stage E adds ports, so it enlarges `declaredNames` again — a port name
joins the same union — and it is the stage where the well-formedness preservation theorem was going to be
attempted. If the counterexample stands, that theorem cannot be stated as planned until the DTR side gains a
clause requiring a class's constructor formals, state variables, known rebecs and message-server names to be
distinct as one set. That clause is the DTR mirror of the LF one, and the fact that the LF side needed it is
evidence the DTR side does too.

---

## F33 — stage C's startup refusal would have rejected a fixture stage B had already committed

**What it is.** Stage C's `renderGeneralParameterRead` had

```
  | .startup, _ =>
      .error
        ("startup reaction `" ++ reaction.name.value ++ "` must not declare payload parameters")
```

with the docstring *"A startup reaction with parameters is an error rather than an ignored field, because
nothing could deliver a value to it."* The reasoning is sound about a payload and wrong about what the field
holds. `assembleGeneralStartupReaction` fills `parameters` with the constructor's formals
(`Relico/Translation/GeneralBasic.lean:931`), and those are the *reactor's* parameters: in the generated C++
they are already members, readable in a reaction body with no binder at all. The correct emission for that arm
is the empty string, which is what stage D now does, and the two startup arities are the one place in the
function where two arities share an arm.

The committed fixture that would have been refused is `frontend/fixtures/general/constructor-arguments.rebeca`,
which has been a *positive* — accepted, decoded, asserted — since stage B:

```
reactiveclass Configured(4) {
    statevars { int limit; boolean enabled; }
    Configured(int bound, boolean active) { limit = bound; enabled = active; }
    ...
}
```

So the refusal did not merely restrict the fragment. It contradicted a fixture the repository already claimed
to accept, and the contradiction was invisible for exactly one stage because stage C had no translation: the
printer was only ever handed hand-built programs, and every one of them had a parameterless startup reaction.

**How it is known.** *Read*, three places that have to be put side by side, which is why it went unnoticed:
the refusal, recovered from the committed stage C printer via `git show HEAD:Relico/LF/GeneralCppPrinter.lean`
at its lines 307–325; the assembler that fills the field at `Relico/Translation/GeneralBasic.lean:931`; and
the fixture on disk. *Measured*, for the repair: the assertion `STARTUP_PARAMETERS_READ_NOTHING` pins the
empty emission, and `ACCEPT_TRANSLATED_WIDENED_PROGRAM` translates that fixture's model end to end, so the
combination that used to be refused is now the one the gate depends on.

**Consequence.** The field is polysemous, and that is the finding worth carrying forward rather than the
deleted branch. `LF.GeneralReaction.parameters` means *payload formals to bind* under a logical-action trigger
and *the enclosing reactor's parameters* under `startup`, and both are referenced through the same
`LF.GeneralExpr.parameterVar` constructor, checked by the same clause —
`Relico/LF/GeneralWellFormed.lean:164` reads `| .parameterVar name => parameters.contains name`. The list is
therefore load-bearing under `startup` and could not simply have been left empty to dodge the refusal: the
translated constructor body is `setState limit (parameterVar bound)`, so with an empty list
`ACCEPT_TRANSLATED_WIDENED_PROGRAM` would fail. One field with two meanings, distinguished only by the
trigger, is what let a defensible-sounding docstring be wrong; splitting it into two fields is a candidate for
a later stage and is on the open list, not done here, because it touches every reaction site in the family.

Two smaller consequences. The startup arms are not collapsed under a wildcard even though both return `.ok
""`, so the stage that adds a fourth trigger form still gets a build error at this function. And this is the
second finding in the series — F23 was the first — where a refusal justified by an appeal to what the *target*
or the *source* could not do turned out to be a limit of this repository's own printer; the pattern is enough
to be worth a habit, which is that a refusal's justification should name the file and line that forces it.

---

## What is left open, and who owns it

Ordered by whether something later is blocked on it, not by finding number. Each item says what would settle
it, because an open item that does not name its experiment tends to stay open.

**Blocking stage E — settle F32's counterexample first.** Write the collision model described in F32 and
record what the three predicates actually say. If the counterexample stands, the DTR side needs a clause
requiring each class's constructor formals, state variables, known rebecs and message-server names to be
distinct as one set, and it needs it *before* the well-formedness preservation theorem is attempted, because
that theorem is false without it. Stage E is where ports join the same union, so the cost of discovering this
late rises there rather than staying flat.

> **The compiler half is now measured (2026-08-20) and it raises the stakes.** See the `declaredNames` item
> below: the collision survives `lfc`'s validator and dies in the generated C++. So if the Lean-level
> counterexample stands, the pipeline does not merely fail to prove a theorem — it can take a model this
> repository certifies as DTR-well-formed and emit an LF program that **does not build**. That reclassifies
> the missing DTR clause from bookkeeping to a soundness fix, and it means the clause is required whether or
> not the preservation theorem is ever stated. The Lean half is still unwritten and is still what settles it.

> **Correction, same day, before the above was acted on.** The paragraph above is **wrong**, and it is left
> standing because the reasoning that produced it is the kind worth being able to recognise later. It
> inferred a pipeline-level conclusion from a toolchain-level measurement without checking the layer in
> between. `Relico/Frontend/GeneralElaborator.lean:793–796` rejects a constructor formal that shadows a state
> variable, with a dedicated `.parameterShadowsStateVariable` diagnostic. A `.rebeca` file therefore cannot
> deliver this collision to the translator, `namesUniqueAndValid`'s delegation to "the elaborator's concern"
> is honoured rather than betrayed, and **there is no soundness gap**.
>
> What survives is narrower and still blocks stage E: the preservation theorem is false *as stated*, because
> its hypothesis `m.wellFormed` does not imply the LF-side `Nodup`, and a hand-built model witnesses that.
> The fix is therefore **not** a new clause in `DTR.GeneralModel.wellFormed` — that would duplicate the
> elaborator's check and collapse a two-layer partition that `GeneralWellFormed.lean:319–321`,
> `GeneralElaborator.lean:820–823` and `GeneralDecoder.lean:30` all state deliberately. It is either an
> explicit extra hypothesis on the theorem, or a proof that the elaborator's guarantee implies the LF
> predicate. Stage E's design must choose between those two and say why.
>
> One consequence worth its own line: nothing in the twelve lean-reject fixtures exercises
> `.parameterShadowsStateVariable`. The guarantee this correction leans on is **untested**, which is the
> shape of the `PrioritiesDistinct` defect from stage B — a predicate that exists and is never reached.
> A fixture for it is now the cheapest thing on this list.

**Blocking stage E — measure whether a preamble struct can be a port's type.** F30's candidate answer for a
multi-parameter message server reached by an external send is `input in: Receiver_m_Args`. Nothing has
measured that `lfc` accepts a preamble struct in that position; the struct probe covered actions only. If it
fails, the arity limit becomes a stated restriction on the accepted fragment rather than a printer detail, and
that changes what stage E can claim.

> **Measured 2026-08-20, and it succeeds.** `lf_semantics_probe.sh` section 11, probe `struct_as_port_type`:
> a `public preamble` struct used as both an `output` and an `input` type, carried across an `after 0 msec`
> connection, compiled and printed `RELICO_STRUCT_PORT 9 1`. So the candidate answer is available and this
> item is closed as evidence; what remains is a stage E *design* decision, not a measurement.

**Blocking nothing, cheap, and stale the moment it is deferred — read Fig. 5's `ActionDecl` production.** F26
has been provisional across two stages. The paper is at
`~/Desktop/LFStructuringNonDeterminism/DTR_LF__After_FMCAD_.pdf`, outside this repository and not to be
edited. The question is narrow: does the production admit a typed action, and does it admit more than one
payload value? One reading closes F26 or turns it into a real entry.

**File F31's paper fault in the `P` series.** Fig. 5's `ArgList ::= Expr (, Expr)*` cannot derive Fig. 1b's
own `new TempSensor(v=1)`. That is a fault in the paper and belongs in `docs/PAPER_CORRECTIONS.md` under the
next free `P` number, not in this file. It is deliberately not appended here: the `P` series has its own file
and its own numbering, and extending it as a side effect of a findings write is the drift this file exists to
prevent. The nearest existing entry, P21, is about which *source construct* becomes a parameter and not about
argument-list syntax, so this is a new entry rather than an extension.

**Commit the parameter probe.** The named-argument and parameter-default forms were measured ad hoc and only
`docs/STAGE_D_DESIGN.md:341` records the result; probe 10 by contrast lives in
`tools/paper-measurements/lf_semantics_probe.sh` and a fresh clone can re-run it. The LF target gate now
re-measures the instance form on every green run, so nothing rests on the missing script, but the probe should
join its sibling.

> **Done 2026-08-20.** `lf_semantics_probe.sh` section 11, probe `parameter_defaults_named_args`: one reactor
> `Configured(bound: int = 0, active: bool = false)` instantiated both bare and with named arguments, printing
> `RELICO_PARAM 0 0` and `RELICO_PARAM 7 1`. A fresh clone can now re-run what `STAGE_D_DESIGN.md:341` merely
> asserts.

**Measure the conservatism in `declaredNames`.** Parameters were added to the reactor's name-uniqueness union
on the stated ground that including them is the conservative side of an *unverified* question —
`Relico/LF/GeneralWellFormed.lean:81` says so outright. The probe is two lines of LF: does `lfc` reject
`reactor R(x: int = 0) { state x: int = 0 ... }`? If it accepts it, this repository is stricter than its
target on purpose and should say so; if it rejects it, the conservatism becomes a measured requirement and
F32's counterexample becomes a bug with a compiler behind it.

> **Measured 2026-08-20, and the answer is *both*.** `lf_semantics_probe.sh` section 11, probe
> `param_state_name_collision`: `lfc`'s own validator **accepts** the collision — it emits no error and
> proceeds to code generation — and the *generated C++* then fails to compile. So `declaredNames` is stricter
> than the LF validator and **not** stricter than the toolchain, and the conservatism is justified on
> toolchain grounds rather than validator grounds. Both halves matter and they point opposite ways, which is
> why the item was worth measuring rather than arguing.
>
> The diagnostic is not the one predicted, and the difference is informative:
>
> ```
> lfc: error: reference member 'x' binds to a temporary object whose lifetime would be
>      shorter than the lifetime of the constructed object [R.cc:50:7]
>  --> src/V0Controller.lf:1:1
> ```
>
> Not a redeclared member. **The Cpp target emits a reactor parameter as a C++ reference member**, so a
> parameter colliding with a state variable does not produce a duplicate name — it produces a reference bound
> to a dead temporary. That is a fact about the target worth carrying into stage E independently of this
> finding: a parameter's storage is a reference into the instantiation expression, not a copy.
>
> Note also where `lfc` attributes the failure: `src/V0Controller.lf:1:1`, the top of the file. A clang error
> inside generated code cannot be mapped back to the declaration that caused it, so the user-visible symptom
> of this bug is a lifetime error pointing at nothing. Catching it in our own predicate is not merely
> equivalent to letting the toolchain catch it.

**Consider splitting `LF.GeneralReaction.parameters`.** F33's underlying cause is one field meaning two
things. Splitting it touches every reaction construction site in the family, so it is not a stage D change,
but the next stage that rewrites those sites for another reason should do it in the same pass.

**The letter `D` is overloaded four ways, and the rename fixed only the newest claimant.** The `D1–D9 → F21–F29`
mapping above was verified uniform before stage D was committed — a repository-wide search of `*.md`, `*.lean`
and `*.sh` for a bare `D` followed by a digit found no surviving label in either stage D document outside the
two numbering-history paragraphs, and none at all in `Relico/Translation/GeneralBasic.lean`. The same search
found three *other* live series wearing the same letter: the fragment divergences in
`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`; **deliverables** `D1–D8` in
`docs/actor-priority/phase4d/PHASE4D_IMPLEMENTATION_PLAN.md:25–32`, where `D2` means "LF target model" and has
nothing to do with `statevars` being absent; and regression-case labels `D1A`, `D2B`, `D3B+`, `D4A+` plus a
"theorem-level `D3` invariant" in `Relico/DTR/GlobalMultiStorePayloadExternalSend.lean:218` and
`Relico/Tests/GlobalMultiStorePayloadExternalSend.lean`. Worth having measured, too: the fragment series is
cited from Lean at more sites than the design's prose names — `Relico/DTR/GeneralWellFormed.lean:92`, `:108`
and `:216`, and `frontend/lean-bridge/GeneralFrontendTestMain.lean:40` — so renaming *that* series would be
considerably more expensive than renaming this one was, which is the second argument for having renamed this
one. No action is proposed for the existing three: they are load-bearing where they are. The rule this yields
is for new work only — a bare single letter is not a namespace, so any future series takes a word or a prefix
that reads as one. `P` and `F` are grandfathered and are not to be joined by a third.

**Carried, with owners already named.** F25 and F31 are divergences that stay open by nature and are filed so
the choices read as ours. F27 belongs to stage G, which is where local message-server priority becomes
observable and where the drop currently pinned by `assembleGeneralMessageReaction_priority` must be justified
or reversed. F28's remaining half needs a typing judgment on `LF.GeneralExpr`, which no stage has yet had a
reason to build. F29 needs the same freshness machinery F32's clause would introduce, so the two are worth
doing together. The port-name spelling of ledger P20 is settled in stage E and is not an `F` item.
