# Stage E design — external sends, ports and connections

Stage E is the stage at which this translator stops being a translator of *one actor at a time*.
Everything before it compiled a Timed Rebeca model whose actors never spoke to each other; stage E
admits `rebec.message(args) after d`, which in the Lingua Franca target means output ports, input
ports, connections in `main reactor`, and a second reaction on the receiver for every sender that
reaches it.

Stage D is closed at `3290ad4`; its groundwork commits `15b5172` and `fe63c6f` and the fixture
`b14809b`/`687c00e` are landed and remote-verified. Nothing in stage D is outstanding except the
`ActionDecl` reading owed to F26, which is noted in §11 and does not block this design.

**Revision 2, 2026-08-20.** Revision 1 landed at `6298284` and keyed ports on the (known rebec, message)
pair. That was wrong, in a way review caught and this revision repairs: two sends to one pair became two
`set()`s on one port at one tag, so one Rebeca message was silently lost, and no sound syntactic refusal
can separate that case from the legal per-statement-delay case. Ports are now keyed on the **send site**,
which makes the hazard structurally unreachable and per-statement delays representable. §6 is rewritten
end to end and §4.1, §4.2, §4.3, §7.1, §7.2, §7.3, §8, §10.2, §10.3 and §11 are amended; the four
decisions §11.3 put to the user are answered and recorded there. The defect itself is written up as F40
rather than quietly overwritten, and F35 is weakened to what survives of it. Revision 1's text is not
otherwise altered, so `git diff 6298284 -- docs/STAGE_E_DESIGN.md` is a faithful record of what changed
and why.

## 1. What stage E is, and exactly where its boundary falls

Stage E replaces one refusal with a translation. `Relico/Translation/GeneralBasic.lean` currently
refuses any model containing a send whose target is not `self`, and it does so through a predicate
chain — `generalStmtSelfSendOnly`, `generalBodySelfSendOnly`, `generalMessageServersSelfSendOnly`,
`generalClassSelfSendOnly`, `generalClassesSelfSendOnly`, `generalModelSelfSendOnly` — that stage D
deliberately built as a *characterisation* rather than a guard: `compileGeneralModel_ok_iff_selfSendOnly`
(`:3181`) proves acceptance and self-send-onlyness are the same condition. Stage E is the stage that
falsifies that biconditional on purpose.

Concretely, stage E delivers four things that do not exist today:

| what | where it lands | what it is today |
| --- | --- | --- |
| output ports on the sending reactor | `assembleGeneralReactor.outputPorts` | `[]`, hardwired at `GeneralBasic.lean:1180` |
| input ports on the receiving reactor | `assembleGeneralReactor.inputPorts` | `[]`, hardwired at `:1177` |
| connections in `main reactor` | `assembleGeneralProgram.connections` | `[]`, hardwired at `:1487` |
| one reaction per (sender instance, send site) on the receiver | `assembleGeneralReactor.messageReactions` | one reaction per message server, sender-blind |

What stage E does **not** deliver, and the boundary is worth stating precisely because the previous
stages' boundaries were each misread once:

- **It does not deliver the §III-D ordering guarantee.** Stage E emits the receiver's per-sender
  reactions in a defined order and proves what that order is; it does not prove that the order
  realises actor priority, and it does not make priority observable. Fan-in *topology* is stage E
  because it falls out of the naming rule (§4.1); fan-in *ordering* is stage F, and the observable
  trace is stage G. The distinction is real: the topology is a structural property of the emitted
  program, and the ordering claim is a statement about executions.
- **It does not deliver control flow.** A send inside an `if` or a `for` is still refused, by the
  same `iterationNotSupported` and `branchingNotSupported` reasons, at the frontend. Stage H owns
  that. So every send stage E sees is at the top level of a message-server body — which is load-bearing
  for §6's central invariant, and §6.3 states the obligation stage H inherits because of it.
- **It does not touch local message-server priority.** `assembleGeneralMessageReaction_priority`
  (`:850`) still proves `priority = none`, and stage G still owns it. This matters more in stage E
  than it did in stage D, because stage E multiplies the receiver's reactions, so it multiplies the
  places stage G will later have to attach a priority.
- **It barely widens the LF syntax layer, and what it does widen is a correction stage D already
  made once.** Everything *structural* was pre-built: `LF.GeneralPortDecl`, `LF.GeneralConnection`,
  `LF.GeneralTrigger.inputPort`, `LF.GeneralReactor.inputPorts`/`outputPorts`,
  `LF.GeneralProgram.connections`, `connectionWellFormed`, `connectionsWellFormed` and
  `targetEndpointsUnique` were all written in stage C and widened in stage D against a translation
  that never produced one of them, and stage E is the stage that finally exercises them. Two things
  do change, both in §5: `LF.GeneralPortDecl.declaredType : LF.GeneralType` cannot name a payload
  struct, so it becomes a parameter list exactly as `LF.GeneralAction.parameters` did in stage D
  (§5.2); and `LF.GeneralStmt.setPort` carries one expression where it needs a list, for the same
  reason `schedule` already carries one (§5.1). Neither is a new *construct* — both replace a field
  that cannot represent something the target demonstrably accepts.

## 2. What stage E inherits: the translator refuses three of its own committed positives

Stage D's design opened by measuring that the translator rejected its own fixtures, and that argument
is what justified the stage. The same argument is available here, and it is stronger, because the
fixtures in question are not hypothetical inputs — they are checked-in `.parser.json` documents
produced by the real Java exporter, accepted by `Frontend.elaborateGeneralModel`, and then refused by
`Relico.Translation.compileGeneralModel`.

Measured over all nine committed positives in `frontend/fixtures/general/`. Six contain no external
send at all (`minimal-class`, `constructor-arguments`, `control-flow`, `expressions`, `keep-alive`,
`priorities` — the last two do send, but to `self`). The other three are the whole of stage E's
inherited obligation:

| fixture | the send | sender instances | all bound to | args | delay |
| --- | --- | --- | --- | --- | --- |
| `two-classes` | `Producer.tick` → `sink.accept` | `producer0` | `consumer0` | 1 | none |
| `two-instances` | `Worker.work` → `hub.report` | `workerAlpha`, `workerBeta` | `collector0` | 1 | **`after 2`** |
| `fan-in` | `Sensor.sample` → `gateway.collect` | `sensorFirst` (1), `sensorSecond` (2), `sensorThird` (3) | `gateway0` | 1 | none |

Each of the three has exactly **one** external send statement, each carries exactly **one** argument,
and each argument is a plain variable reference. That is worth recording explicitly, because it means
the corpus does **not** exercise arity 0, arity 2+, or a compound argument expression through an
external send, and §5 has to decide what the translation does there on evidence other than the corpus.

The refusal itself is not a `GeneralDiagnosticReason`; it is an `Except String` message raised in
`compileGeneralStmt`'s `.knownRebec` arm (`GeneralBasic.lean:625`), and its text names stage E out
loud: *"…is an external send; stage D translates self-sends only, and external sends are stage E"*.
The bridge test main asserts on that string verbatim
(`frontend/lean-bridge/GeneralLfPrinterTestMain.lean:1632–1633`, over a fixture model described as
*"the same model with one message server replaced by an external send"* at `:1468`), so stage E cannot
land without rewriting that assertion into its opposite — §10 lists it as a tripwire rather than
letting it surface as a surprise failure.

The three fixtures also happen to be exactly the shapes the design needs, and they are not
interchangeable:

- **`two-classes` is the base case.** One sender instance, one receiver instance, one message. Any
  naming rule at all handles it, which is why it proves nothing on its own.
- **`two-instances` is the case that forces the port keying.** `workerAlpha` and `workerBeta` are two
  instances of *one* class `Worker`, and `Worker.work`'s body is *one* piece of class-level code
  shared by both. So the sender's `set()` target must be a name fixed at class level, while the
  receiver has to distinguish the two arrivals — and it cannot merge them, because many-to-one
  connections are rejected by `lfc`. §4.1 is entirely about this asymmetry.
- **`fan-in` is §III-D's figure, verbatim.** Three `Sensor` instances with distinct actor priorities
  1, 2 and 3, all three bound to the single `gateway0`. Stage E must produce its *topology* — three
  connections arriving at three distinct input ports on the one `Gateway` instance — and must
  deliberately **not** claim its ordering, which is stage F.

One inherited asset makes this cheaper than it looks. `DTR.GeneralModel.resolve_topology_of_actor`
(`Relico/DTR/GeneralSyntax.lean:685`) already proves that known-rebec resolution through the derived
topology equals `Store.lookup actor.bindings knownRebec` whenever the sender is an instance of the
model, and `resolve_topology_of_missing` covers the other case. Its docstring says it is *"the
statement the external-send layer needs and could never obtain from a decoded model before this
family"*. Stage E is the first consumer of both. Note that this corrects a note carried in the
project's own stage B design: bindings are **not** hardwired to `[]` any more —
`Relico/Frontend/GeneralElaborator.lean:937` populates them (`bindings := raw.bindings.map bindingOf`),
which is what the measured table above depends on.

## 3. The measured target facts this design rests on

Every claim in this section comes from `tools/paper-measurements/lf_semantics_probe.sh`, which is
committed, re-runnable, read-only outside `/tmp/relico_lf_probe`, and now carries seventeen probes
against real `lfc 0.11.0`. Nothing here is derived from the paper's Fig. 5 grammar, which is already
known to disagree with its own compiler on at least one point (P-series finding on indexed multiport
triggers). Four facts are load-bearing enough that the design would change shape without them:

1. **Many-to-one connections are prohibited.** Exact wording: `Cannot connect: Port named 'inShared'
   may only appear once on the right side of a connection.` This is why the receiver cannot own one
   port per message and let every sender write into it, and therefore why §4.1 exists at all. It also
   means P20's uniqueness requirement is not an aesthetic preference — a colliding name fails to
   compile.
2. **Unconnected input ports are legal.** A declared-but-unconnected input compiles, runs, exits 0,
   and its reaction never fires; no warning surfaced. This is the fact that makes the receiver's port
   set a *union over sending instances* affordable: a `Gateway` reactor declares one input per
   (sender instance, message) across the whole model, and an instance of `Gateway` that some sender
   never targets simply carries an idle port.
3. **A program-level `public preamble` struct is legal as a *port* type** (probe
   `struct_as_port_type`, 2026-08-20): `output out: Receiver_m_Args` → `input in: Receiver_m_Args`
   across `after 0 msec`, written with `out.set(Receiver_m_Args{7, 2, true})` and read with
   `auto p = *in.get();`, printing `RELICO_STRUCT_PORT 9 1`. Route A therefore reaches ports and not
   only logical actions, which is what makes §5.2 a translation rather than a refusal.
4. **Two instances of one reactor are fine, and self-connections are legal.** The first is what
   `two-instances` needs; the second means a rebec that holds *itself* as a known rebec is
   translatable rather than a special case, since `a.out -> a.in after 0 msec` compiles and runs.

Two further facts are in hand but belong to later stages, and are recorded here only so that stage E
does not accidentally spend them: reaction **declaration order** decides same-tag execution order
within one reactor (that is stage F's entire mechanism, and stage E must not claim it), and a reactor
**parameter is emitted as a C++ reference member** (which is what makes `GeneralWellFormed`'s
name-disjointness conservatism justified on toolchain grounds — see §9).

The delay spelling is a free choice: `after 0 msec`, `after 0ms` and `after 0 ms` all compile and
deliver. The printer keeps ` msec` for byte-identity with the committed fixtures, and stage E changes
nothing there.

**The one hole, and it is the arity that looks easiest.** Ranked by evidence, external-send payload
arities stand as follows. Arity 1 is measured *and* exercised by all three inherited fixtures. Arity
≥ 2 is measured, by fact 3 above. **Arity 0 is unmeasured**: no probe has ever declared a port with no
payload, and there is no evidence that either `input in: void` or a bare untyped `input in` is
accepted, even though `logical action settle_action: void` demonstrably is. Actions and ports are
different declarations in the grammar and the `: void` spelling cannot be assumed to carry over. §5.3
says what stage E does about that, and §11 records the probe that would close it, with a prediction
made in advance.

## 4. P20 settled: what the ports are called, and why uniqueness is a theorem about programs

Ledger correction P20 records that the paper supplies no port-naming rule and that its own two figures
disagree — Fig. 1b names the receiver's port after the receiving message server (`receiveReading`),
Fig. 2b after the output port plus the capitalized sender instance (`readingFromTemp`). The user's
criterion is on record and is not being re-asked: *readable generated code, unique names*, with Fig. 1b
ruled out because a bare message-server name collides the moment two senders arrive, and Fig. 2b
presumptive. This section fixes the spelling and, more importantly, fixes *what kind of guarantee*
uniqueness is.

### 4.1 The asymmetry: the sender's ports are class-level, the receiver's are instance-level

This is the whole of the design and it is forced, not chosen.

A message-server body is **class-level code**. `Worker.work` contains `hub.report(identifier)`, and
that one body is shared by `workerAlpha` and `workerBeta`. It becomes one reaction on reactor `Worker`,
and the `set()` in it names a port declared on `Worker`. So an output port name may depend only on data
available at class level: the **known-rebec name** and the **message name**. It cannot depend on the
sending instance — there are two — and it cannot depend on the receiving instance either, because
nothing in DTR requires two instances of one class to bind the same known rebec to the same actor.

The receiver's side is the opposite. A connection is
`senderInstance.outPort -> receiverInstance.inPort`, many-to-one is rejected by `lfc` (§3 fact 1), and
the set of arrows landing on one receiver instance has one element per *sending instance* that binds a
known rebec to it and whose class sends on that rebec. So each arrival needs its own port, and the port
name must distinguish the sending instance.

It must also distinguish the known rebec, which is less obvious. `knownrebecs { Collector hub1;
Collector hub2; }` with both bound to `collector0` and a body containing `hub1.report(x)` and
`hub2.report(x)` is legal DTR. That sender declares **two** output ports, both connecting to
`collector0`, and two arrows into one instance may not share a target port.

And it must distinguish the **send site** — the individual send statement — which §6 derives at length
and which is the reason this key is not the (rebec, message) pair it looks like it should be. Two sends
to one pair are two Rebeca messages and must remain two `set()`s on two ports, because one LF port
carries one value per tag; and each carries its own `after`, because DTR delays a statement. The site
is class-level data, so this respects the class-level constraint above. Concretely the key is the
statement's index within the class, counting external sends only, in body order — constructor first,
then message servers in declaration order. So:

| | key | declared on |
| --- | --- | --- |
| output port | (known-rebec name, message name, **send site**) | the **sending** reactor |
| input port | (sending instance name, known-rebec name, message name, **send site**) | the **receiving** reactor |

The receiving reactor's input-port list is therefore a **union over every sending instance in the
model**, and an instance of that reactor which some sender never targets simply carries an idle port.
That is only affordable because unconnected input ports are measured legal (§3 fact 2); without that
fact this design would be forced into one reactor per instance, which Table III and
`LF.GeneralProgram`'s own rationale forbid.

Two consequences worth naming now because they surface again later. First, the map from source
endpoint to target endpoint is a **function**: a known-rebec name binds to exactly one actor per
instance, so (sending instance, output port) determines the receiver instance and hence the whole
connection. That is what makes `targetEndpointsUnique` — already in `GeneralWellFormed.lean:454` and
deliberately silent about sources — the right existing predicate, and the site index simply extends the
key it ranges over. Second, with the site in the key **no deduplication is needed anywhere**: distinct
send statements generate distinct output ports, distinct connections and distinct input ports, so the
routing table is a straight walk of the model with nothing to merge. An earlier version of this design
keyed on the pair and required connection generation to deduplicate; that requirement is gone.

### 4.2 The spelling

Fig. 2b's rule is adopted verbatim for the receiver and extended minimally for the sender:

```
outputPortNameFor  (rebec, message, site)    = message ++ "To"   ++ capitalize rebec ++ siteSuffix
inputPortNameFor   (senderInstance, outPort) = outPort ++ "From" ++ capitalize senderInstance
```

The site index carries no source identifier and so is pure noise in the common case. It is therefore
**omitted when the class has exactly one send to that (rebec, message) pair**, and appended as
`ordinal`-style digits from `2` upward, in body order, when it has more:

```
siteSuffix = ""            if this is the class's only send to (rebec, message)
           = toString n    otherwise, n = 1, 2, 3, … in body order
```

The receiver's rule needs no change: it wraps whatever the sender's port is called, so the suffix
propagates for free and both ends stay derivable from the same data.

On the three inherited fixtures that reads:

| fixture | output port on the sender | input ports on the receiver |
| --- | --- | --- |
| `two-classes` | `Producer.acceptToSink` | `Consumer.acceptToSinkFromProducer0` |
| `two-instances` | `Worker.reportToHub` | `Collector.reportToHubFromWorkerAlpha`, `…FromWorkerBeta` |
| `fan-in` | `Sensor.collectToGateway` | `Gateway.collectToGatewayFromSensorFirst`, `…FromSensorSecond`, `…FromSensorThird` |

Every one of those classes sends exactly once to its pair, so the suffix is empty and **all three tables
are byte-identical to what the pair-keyed version of this design produced**. Nothing inherited changes
name; only a class that earns the proliferation pays for it, and then it reads
`reportToHub1` / `reportToHub2`.

Long, and readable: every component is a source identifier and the two infixes read as English in the
direction the arrow points. `readingFromTemp` in the paper's own figure is the same idiom with one
factor fewer. Recorded, as P20 requires, as **this project's rule with no paper basis for the output
half** — the same category as the `<Reactor>_<Action>_Args` struct name (F25). The suffix is a third
such invention, and the paper cannot arbitrate it because no figure sends one message twice.

### 4.3 Concatenation is not injective, so uniqueness is stated about programs and not about the function

The memory of the P20 decision asks for uniqueness to be a *proved* property, with an injectivity
lemma beside `actionNameFor_injective` and `messageReactionNameFor_injective` in
`Relico/Translation/NameGeneration.lean`. Those two are cheap because they append a fixed **suffix**:
`s ++ "_action"` is injective by right-cancellation and both proofs are a `simpa`. A two-argument
concatenation is a different animal, and the naming rule above is **not injective**:

```
message = "reportTo", rebec = "hub"    ⟶  "reportTo" ++ "To" ++ "Hub"    = "reportToToHub"
message = "report",   rebec = "toHub"  ⟶  "report"   ++ "To" ++ "ToHub"  = "reportToToHub"
```

Both are legal Rebeca identifiers, so this is a real collision and not a hypothetical one. The site
suffix opens a second channel of the same kind: `report`/`hub` at site 2 and `report`/`hub2` at its
class's only site both give `reportToHub2`. Every readable separator has this property; underscore
joining has it too (`my_msg`+`hub` versus `my`+`msg_hub`), which is why the standard fix is to escape
the separator in each component — double every `_` and join with a single one. That does buy genuine
injectivity, and it is recorded here as the known alternative, but its cost is a string-decoding proof
in Lean and names like `my__msg_hub`.

The resolution is to move the guarantee rather than to weaken it. Uniqueness of the generated names is
already a conjunct of the LF side's own well-formedness: `declaredNames`
(`GeneralWellFormed.lean:84`) is `parameters ++ inputPorts ++ outputPorts ++ stateVariables ++
logicalActions` and must be `Nodup`. So stage E's obligation takes this shape:

- The translation **decides** name uniqueness on the program it has just built, and refuses with a
  named diagnostic when it fails. A model containing both `reportTo`/`hub` and `report`/`toHub` on one
  class is refused, not silently mistranslated.
- The theorem is then *acceptance implies well-formedness* — if `compileGeneralModel` returns `.ok p`
  then `p` satisfies the LF well-formedness predicate, port-name `Nodup` included. Quantified over all
  models, that is a strictly stronger and more useful statement than injectivity of one naming
  function, and it is the same discipline stage D used for instance arguments rather than a new one.
- Two *one-sided* injectivity lemmas are still cheap and still worth having, because they are the ones
  a reader expects: with the message fixed the name determines the rebec, and with the rebec fixed the
  name determines the message. Both reduce to suffix or prefix cancellation.

That the readable rule is not injective is a finding, not an embarrassment, and it gets an F-number in
§11: the paper's Fig. 2b idiom cannot be made injective by inspection, and any implementation that
claims unique port names from a concatenation rule without either escaping or checking is wrong.

A reserved prefix — `relico_`, with the elaborator refusing source identifiers that start with it —
was considered and is **not** adopted here. It would give injectivity *and* disjointness from every
source-derived name in one move, which is tempting because disjointness is exactly what F32 is short
of. It is declined for three reasons: it makes every generated name uglier for a hazard that is not
specific to ports; it would have to be retrofitted onto `_action` and `_reaction`, which have carried
the same hazard since stage C, so it is not a stage E-sized change; and F32 deserves to be settled on
its own terms in §9 rather than dissolved as a side effect of a naming convention.

## 5. The payload: what an external send carries, and the two fields that cannot express it

### 5.1 `setPort` carries one expression and needs a list

`LF.GeneralStmt.setPort : PortName → GeneralExpr → GeneralStmt` (`GeneralSyntax.lean:342`), and its
docstring justifies the single expression from the paper: *"`LFStmt ::= outPort([Expr])?.set(Expr);`
admits exactly one value, while a typed logical action's payload arity follows the parameter list of
the message server it was derived from."* That reading of Fig. 5 is right, and it is still not enough,
for a reason that has nothing to do with the paper.

A message server of arity two or more is carried by a payload **struct**, and the struct literal
`Collector_report_Args{a, b}` is not expressible in `LF.GeneralExpr` — that type has integer and
boolean literals, state and parameter variables, and unary and binary operators, and nothing else. Two
ways out, and only one of them is acceptable:

- Add a struct-literal constructor to `LF.GeneralExpr`. Rejected: it would let a struct literal appear
  in every expression position — the right-hand side of an assignment, an operand of `+`, a `schedule`
  argument — where it means nothing and where no well-formedness condition currently rules it out.
  Widening the expression layer to carry one statement's payload is the wrong shape.
- Give `setPort` a list and let the **printer** build the struct, which is exactly what
  `renderGeneralStmt`'s `.schedule` arm has done since stage D: `[]` prints
  `a.schedule(delay)`, `[e]` prints `a.schedule(e, delay)`, and `e₁ :: e₂ :: rest` prints
  `a.schedule(Struct{e₁, e₂, …}, delay)`. Adopted.

So `setPort : PortName → List LF.GeneralExpr → GeneralStmt`, and the three arms of the printer mirror
`schedule`'s three arms. **The emitted LF still matches Fig. 5**: `p.set(Struct{a, b});` passes exactly
one expression to `set`, so this is a change in how the Lean syntax model *represents* a set, not a
divergence from the target grammar. `stmtWellFormed`'s `.setPort` arm already requires the port to be
declared as an output on the reactor whose body sets it (`GeneralWellFormed.lean:214–220`), and it
gains the arity conjunct `declared.parameters.length == arguments.length` that `.schedule` already
carries.

### 5.2 A port declaration cannot name its own type

`LF.GeneralPortDecl` is `name : PortName` and `declaredType : LF.GeneralType`, and
`LF.GeneralType` is `int | boolean` and nothing else (`GeneralSyntax.lean:67–72`). A port carrying two
values has no representable type. This is the *identical* gap stage D found on the action side and
described in its own words: a `msgsrv logic(boolean first, boolean second)` *"had nowhere to record
that its parameters are booleans, so the printer could only ever have guessed."* Stage D's fix was to
give `LF.GeneralAction` a `parameters : List GeneralTypedParameter` and let
`renderGeneralActionDecl` (`:517–536`) derive the printed type from arity — `void`, the bare scalar, or
`generalPayloadStructName`. Stage E makes the same correction to ports, and the symmetry is the
argument for it.

The complication is that a port's struct name cannot be derived from the port itself, and that is worth
spelling out because the obvious scheme fails. The two ends of a connection must name the *same* C++
type, but the two ends have different port names and different declaring reactors:
`Worker.reportToHub` and `Collector.reportToHubFromWorkerAlpha`. So
`<DeclaringReactor>_<PortName>_Args` — the direct analogue of the action rule — produces two different
names for one type. The name has to come from something both ends share, and the only such thing is the
**receiving reactor together with the message server**, which is precisely
`generalPayloadStructName receiverReactor (actionNameFor message)` — the helper stage D already owns
and calls *"the single owner of this spelling"*.

Hence the port payload is a small inductive carrying what both ends must agree on, rather than a
`GeneralType`:

```
inductive GeneralPortPayload where
  | scalar : LF.GeneralType → GeneralPortPayload
  | struct : ReactorName → ActionName → List LF.GeneralTypedParameter → GeneralPortPayload
```

with `GeneralPortDecl.payload : GeneralPortPayload` replacing `declaredType`. Four things follow, and
each is a gain rather than a cost:

1. **The preamble stays derived, not stored.** `generalProgramStructDecls` currently walks each
   reactor's `logicalActions`; it gains a walk over `inputPorts` and `outputPorts`. The principle the
   printer states for actions — *"a stored struct list could declare a struct no action uses, or omit
   one an action needs… Derived, neither is expressible"* — survives intact for ports, because the
   thing that types the port is the same thing that declares the struct.
2. **Duplicate declarations become possible and must be deduplicated by name.** One struct is now
   named by up to three declarations: the receiver's logical action if the message is also self-sent,
   the sender's output port, and every input port on the receiver. `generalProgramStructDecls` must
   dedup on the rendered name, and that dedup is the mechanism by which a message server that is
   *both* self-sent and externally received gets exactly **one** struct used in both positions —
   measured legal, since a `public preamble` struct works as an action type and as a port type.
3. **Type agreement across a connection becomes checkable.** `connectionWellFormed`
   (`GeneralWellFormed.lean:277`) today resolves both endpoints and checks that the source declares
   that output and the target that input; it says nothing about their types, even though `lfc` requires
   connected ports to agree. With the payload stored it gains a decidable equality conjunct. That is a
   new well-formedness *strengthening* stage E can prove its own output satisfies.
4. **The receiver's reaction needs no new machinery.** Its binders are the message server's parameter
   names, which is what `renderGeneralParameterRead` already consumes for actions of arity 1 and
   arity ≥ 2 alike.

One honest weakening to record rather than bury: the struct's *name* is now stored at both ends
instead of derived at one, so two ends **could** carry different names. That is not left to hope — it
is what conjunct 3 decides — but it is a place where stage D's "cannot disagree" became stage E's
"is checked", and the difference deserves an F-number (§11).

### 5.3 The arity that is measured least is zero

`msgsrv ping()` reached by an external send needs a port with no payload. Arity 1 is measured and
exercised by all three inherited fixtures; arity ≥ 2 is measured by probe `struct_as_port_type`;
**arity 0 is not measured at all.** `logical action settle_action: void` is measured and works, but an
action declaration and a port declaration are different productions and the `: void` spelling cannot
be assumed to carry over, and the probe log contains an `Input must have a type.` diagnostic — raised
for a different malformation, but a warning that a typeless `input in` may not be accepted either.

Stage E therefore **refuses an arity-zero external send**, with a named diagnostic that says the
measurement is missing rather than pretending the construct is impossible, and the probe that would
close it is listed in §11 with a prediction stated in advance. This is the one place where the design
is narrower than the target may allow, and it is narrower on purpose: a translator that emits an
unmeasured declaration is guessing, and this project's whole method is that it does not guess about
`lfc`. The DTR corpus contains no arity-zero external send, so nothing in the fixture set regresses.

`GeneralPortPayload.scalar` covers arity 1 and needs no struct, so `two-classes`, `two-instances` and
`fan-in` all translate through the scalar arm and the struct machinery above is exercised only by a
new fixture written for it.

## 6. The delay, and the collision that makes send sites the unit of translation

**Revised 2026-08-20, after the first version of this section got it backwards.** The original text, at
`6298284:docs/STAGE_E_DESIGN.md:408–409`, read: *"Two sends to the same (rebec, message) with the
**same** delay: fine. They deduplicate to one connection, and the second statement is a second `set()`
on the same port."* — and refused only the case where the delays differed. That is exactly inverted, and
the error is recorded as F40 rather than quietly corrected, because the case it blessed is the one that
loses a message.

In DTR the delay is a property of a **statement**: `hub.report(x) after 2` and `hub.report(y) after 5`
are two well-formed sends in one body, and `hub.report(1); hub.report(2);` enqueues **two** messages, so
the receiver's `report` runs **twice**. In LF, following the paper's own figures, the delay is a
property of a **connection**: Fig. 1b line 22 and Fig. 2b lines 41–42 write `after 2ms` on the arrow in
`main reactor`.

### 6.1 Why one port per (rebec, message) is wrong

An LF port carries **one value per tag**. If both statements name the same output port, the translated
sender performs two `set()` calls in one reaction at one tag, and the receiver's reaction fires **once**.
Either the second `set` overwrites the first and one message is silently lost, or it is a runtime error;
which of the two is **unmeasured**, and the design does not need to know, because both are wrong. So the
same-delay case is not the easy one — it is the broken one.

The refusal the original section proposed cannot be repaired by widening it, either. "Two sends arrive
at the same tag" is a property of **executions**, not of syntax: `hub.report(x) after 2` in one message
server and `hub.report(y) after 5` in another coincide whenever the first fires three time units after
the second, which no static rule decides. A *sound* syntactic refusal would therefore have to reject any
class containing two sends to one (rebec, message) pair **regardless of delay** — which would reject
precisely the differing-delay case that must work.

### 6.2 The send site is the unit

Both requirements are met at once by keying ports on the **send site** — the individual send statement —
rather than on the (rebec, message) pair:

- Each send statement gets its own output port on the sending reactor, its own connection, and its own
  input port on the receiving reactor.
- One statement performs **at most one `set()` per reaction per tag**, because a reaction fires at most
  once per tag and, control flow being stage H's business, each statement in a body executes at most
  once per firing.
- Two statements are two different ports, so no tag can carry two values on one port.

Two sets on one output port at one tag therefore becomes **structurally impossible rather than
checked** — an invariant to state as a theorem (§10.2), not a refusal to exercise. Three further
consequences follow, and every one of them simplifies the design:

1. **Per-statement delays are representable.** Each site's own connection carries that site's own
   `after`, which is DTR's placement exactly. So the delay conflict of the original §6 does not exist,
   the sender-side logical-action workaround it recorded as the alternative is **not needed**, and no
   extra action, reaction or microstep is spent.
2. **Nothing legal is refused on delay grounds.** The refusal count drops from three to two (§8).
3. **F35 dissolves.** What looked like an unrepresentable mismatch between a statement-level and a
   connection-level delay was an artifact of choosing the wrong key. The finding survives only in
   weakened form: the paper's figures show one send per pair and so never expose the choice.

Deduplication also disappears rather than moving. The original §4.1 required connection generation to
deduplicate two sends naming one pair; with sites as the key there is nothing to deduplicate, and the
routing table is simply longer.

### 6.3 What it costs, and what stays owed

The cost is proliferation: a class with *k* sends to one pair declares *k* output ports, and the
receiver declares *k* input ports per sending instance. Since the site index carries no source
identifier, it is appended **only when a class has more than one send to the same (rebec, message)
pair** (§4.2), so every one of the three inherited fixtures — each with exactly one external send —
keeps byte-identical names, and the ugliness is confined to models that earn it.

**The invariant is conditional on the fragment, and stage H is where it comes due.** "One statement
executes at most once per firing" is true only because bodies are flat: a send inside a `for` runs many
times in one reaction and so sets one port many times, which is the message-losing case again, arriving
by a different road. Stage H therefore inherits a real obligation and this design records it in advance
rather than letting stage H discover it: either a loop containing an external send is refused, or the
loop is compiled so that each iteration reaches its own tag — which is what a sender-side logical action
buys, the mechanism §6.1's rewrite made unnecessary here but which stage H may well need. The theorem in
§10.2 must be stated so that adding loop constructors **breaks its proof loudly** rather than silently
weakening its meaning, in the same style as stage D's deliberate tripwires (§10.1).

One measurement stays owed, and it is now about **stage D's landed self-send path** rather than about
stage E. `self.tick(); self.tick();` in one body emits two `tick_action.schedule(0ms)` calls at one tag.
Two invocations of one action at one tag are understood to be acceptable in LF, which is why this is not
being treated as a defect — but it is **unmeasured**, no committed fixture exercises it (`priorities`
self-sends twice from its constructor, to two *different* message servers, so nothing collides), and
stage E's external-send path deliberately does not rely on it. §11.2 carries the probe.


## 7. The translation, function by function

### 7.1 The one structural change: local functions gain a context

Every translation function from `compileGeneralStmt` (`:607`) up to `compileGeneralReactiveClass`
(`:1302`) takes **only local data** today. That is what makes stage D's proofs short, and stage E
cannot keep it: turning `hub.report(x)` into a `setPort` requires the *receiving* class's message-server
parameter list, which lives in another class. So a context has to arrive from somewhere, and the choice
of what it is decides how much of the proof layer moves.

Rejected: passing `DTR.GeneralModel` down to statement level. It couples the smallest function to the
largest type and makes every statement lemma mention a model when only two lookups are used.

Adopted: **resolve once per class, then compile against the resolution.** One new function builds a
class's output-port environment, and `compileGeneralStmt` takes that environment plus the address of the
statement it is compiling, and nothing else:

```
inductive GeneralBodyKey where
  | constructor  : GeneralBodyKey
  | messageServer : MsgName → GeneralBodyKey

structure SendSite where
  body  : GeneralBodyKey
  index : Nat            -- position within that body's statement list

outputPortEnvOf : List GeneralReactiveClass → GeneralReactiveClass → Except String OutputPortEnv
OutputPortEnv  := List (SendSite × KnownRebecName × MsgName × PortName × LF.GeneralPortPayload × Delay)
compileGeneralStmt : OutputPortEnv → GeneralBodyKey → Nat → DTR.GeneralStmt → Except String LF.GeneralStmt
```

The site is an **address, not a counter**, and that is a deliberate choice with a proof cost attached to
the alternative. Numbering the class's external sends with a running total would force every body
compiler to thread the count and every statement lemma to carry an arithmetic side condition. Naming a
site by its body and its position within that body is unique class-wide for free — a message-server name
occurs once per class and the constructor is unique — so each body compiler already knows its own key,
`List.zipIdx` supplies the index, and no state is threaded. Bodies are flat lists until stage H, at
which point a nested statement needs a path rather than an index, and this is the shape that extends to
one.

Every interesting refusal then happens in `outputPortEnvOf`, once per class, where the diagnostic can
say something specific; `compileGeneralStmt`'s `.knownRebec` arm becomes a lookup whose failure means
the class sends on a rebec it does not declare — which DTR well-formedness D6
(`Relico/DTR/GeneralWellFormed.lean:92`, quoting that file's own requirement numbering, which has
nothing to do with any finding number) already forbids, so the arm survives as a defensive refusal
rather than as the stage boundary it is today.

`outputPortEnvOf` is where §5 and §6 are enforced. It walks every message-server body **and the
constructor body** — a constructor may send, and `assembleGeneralStartupReaction` already compiles its
statements — in canonical order, constructor first and then message servers in declaration order,
producing one entry per external send site with **nothing merged**, then for each entry:

1. resolves `rebec` through the class's `knownRebecs` to a class name, and that name through the class
   table, refusing on an undeclared rebec or an unknown class;
2. finds the message server of that name on the target class, refusing when it has none;
3. builds the payload from the target server's parameters — `scalar` at arity 1, `struct` at arity ≥ 2
   named by `generalPayloadStructName` on the **receiving** reactor and the message (§5.2), and a
   refusal at arity 0 (§5.3);
4. names the port `outputPortNameFor rebec message siteSuffix` (§4.2), where the suffix is empty when
   this is the class's only entry for that (rebec, message) pair and its 1-based ordinal among the
   pair's entries in canonical order otherwise;
5. keeps the site's **own** delay, unexamined — no comparison against any other site, because two sites
   are two ports and two connections, so differing delays are not a conflict and equal delays are not a
   collision (§6).

### 7.2 Output ports come from the class; input ports and connections come from the model

This asymmetry was forced once already by §4.1, and there is a second, independent reason for it. A
class with **no instances** still compiles to a reactor, and its body still contains `set()` calls. If
output ports were derived from the model's instances they would be empty for such a class, and
`stmtWellFormed` — which requires a `setPort`'s port to be declared on the reactor — would fail on the
translator's own output. So output ports must come from the class, and only from the class.

The model-level object is a **routing table**, and everything about the topology is a projection of it:

```
structure GeneralRoute where
  senderInstance   : ActorName
  senderClass      : ClassName
  site             : SendSite
  knownRebec       : KnownRebecName
  message          : MsgName
  receiverInstance : ActorName
  receiverClass    : ClassName
  outputPort       : PortName
  payload          : LF.GeneralPortPayload
  delay            : Delay

routesOf : DTR.GeneralModel → Except String (List GeneralRoute)
```

built by walking `model.instances` in **main-block declaration order**, and for each instance, its
class's output-port environment in canonical site order, resolving each `knownRebec` through
`Store.lookup actor.bindings` — which is exactly what
`DTR.GeneralModel.resolve_topology_of_actor` (`Relico/DTR/GeneralSyntax.lean:685`) proves agrees with
resolution through the derived topology. Refusals: an unbound known rebec, or a binding naming an
instance the model does not declare.

`outputPort` is carried rather than recomputed, so that the two ends of a connection are built from one
string and cannot drift; `site` is carried because it is what makes routes distinguishable, and because
stage F will want to say which statement an arrow came from.

The four projections:

| target | projection |
| --- | --- |
| `reactor C .outputPorts` | `outputPortEnvOf classes C`, mapped to port name and payload |
| `reactor C .inputPorts` | routes with `receiverClass = C`, mapped to `inputPortNameFor senderInstance route.outputPort` and payload |
| `program.connections` | every route, mapped to `⟨senderInstance, outputPort, receiverInstance, inPort, delay⟩` |
| `reactor C .messageReactions` | see §7.3 |

`targetEndpointsUnique` then follows from the routes being distinct in `(senderInstance, site)`, because
the input-port name is built from the sender instance and the sender's output-port name, and the
output-port name determines the site within its class: step 4 of `outputPortEnvOf` (§7.1) assigns
distinct pairs distinct names or refuses (§4.3), and assigns the same pair's several sites distinct
ordinals. That is the point of the site key — under the old (rebec, message) key two sites collapsed to
one port and uniqueness had to be bought with a deduplication step and a delay refusal; now it is
carried by construction.

### 7.3 The receiver's reactions, and the order they are declared in

Each message server `m` on class `C` produces, in this order:

1. the existing action-triggered reaction, `messageReactionNameFor m`, triggered by
   `actionNameFor m` — kept **unconditionally**, even when nothing self-sends `m`. An unscheduled
   action whose reaction never fires is legal, and making the action conditional would rewrite stage
   D's per-message-server invariants for an optimisation nobody asked for. The choice is recorded, not
   assumed;
2. one reaction per route into `C` for `m`, in **route order**, named `<inputPortName>_reaction`,
   triggered by `.inputPort inputPortName`, with the message server's parameter names as its
   `parameters` and the same compiled body as (1).

Because routes are keyed by send site, a sender class with two sends to one (rebec, message) pair
contributes **two** reactions here per instance, not one, both compiling the same message-server body.
That is the intended reading of Rebeca's semantics rather than duplication for its own sake: two sends
enqueue two messages and the body runs twice, and since each arrives on its own port it can arrive at
its own tag. What the two reactions must never do is fire at one tag with one of them losing its value,
which is exactly the hazard §6.1 rules out structurally.

Grouping by message server rather than emitting all action reactions and then all port reactions is
deliberate: stage F's ordering argument is about the port reactions of *one* message server, so keeping
them contiguous makes the later statement compositional.

**Route order is main-block instance-declaration order, and stage E proves exactly that and nothing
more.** For `fan-in` the instances are declared `sensorFirst`, `sensorSecond`, `sensorThird` with actor
priorities 1, 2 and 3, so declaration order and priority order **coincide** — and that coincidence must
not be mistaken for a result. If the fixture declared them in any other order the emitted reaction
order would change and no theorem in stage E would notice. Making the order follow priority is stage
F's entire content; a fixture whose declaration order disagrees with its priority order is the fixture
stage F needs and stage E should not pretend to satisfy.

### 7.4 The printer

Three changes, all of them narrowing an existing refusal or generalising an existing derivation.

- `renderGeneralStmt` gains the declaring reactor's output ports and returns `Except String String`,
  so that a `setPort` of arity ≥ 2 can name its struct from the port's stored payload. `stmtWellFormed`
  already licenses the lookup (`GeneralWellFormed.lean:214–217`), and `renderGeneralReactor` is already
  `Except String String`, so the refusal channel exists and nothing new is invented.
- `renderGeneralParameterRead`'s `.inputPort port, _ :: _ :: _` arm is currently an **error** whose
  message is *"a port declares one type and so carries one value, and unlike a logical action it has no
  parameter list to destructure"* (`GeneralCppPrinter.lean:687`). §5.2 makes that sentence false, so the
  arm becomes the struct-destructuring arm, and `generalPayloadBinderName` — which takes an
  `ActionName` — generalises to any trigger name. Its F29 exposure (a source parameter called
  `foo_payload`) is inherited unchanged and not made worse.
- `generalProgramStructDecls` walks ports as well as actions and **deduplicates on the rendered name**,
  which is what lets one struct serve a message server that is both self-sent and externally received.

`renderInputPortDecl` and `renderOutputPortDecl` derive their printed type from the payload exactly as
`renderGeneralActionDecl` does, and `renderGeneralConnection` (`:1061`) and its ` after ` spelling
(`:1072`) need no change at all — they were written in stage C against connections that did not yet
exist.

## 8. Totality, and where each refusal lives

Stage E has four refusals that stage D did not, and they do not all belong in the same layer. Sorting
them properly is what keeps the translator's refusal surface honest, because two of the four are
already someone else's job. (It was five until §6 was rewritten; the conflicting-delay refusal is gone
because per-site ports make conflicting delays representable.)

**Already guaranteed upstream, so defensive in the translation.** `Frontend.GeneralDiagnosticReason`
already contains `sendTargetsDeclaredFailed` — every external send names a known rebec its class
declares — and `sendsResolveToMessageServersFailed` — every such send resolves to a message server on
the bound class — alongside `bindingsMatchDeclarationsFailed`. These are DTR well-formedness
conjuncts, checked before any translation runs, so steps 2 and 3 of `outputPortEnvOf` (§7.1) can never
fire for a document that reached the translator through the frontend. They still return `.error`
rather than a default, because the translation is a total function on the *type* and not only on
frontend output, and because a silently defaulted port name would be far worse than a refusal nobody
sees.

Those two reasons are also, as far as the fixture set shows, **unexercised**: none of the twelve
`lean-reject` documents names either. Stage E is the first stage in which a send to another actor
exists at all, so it is the first stage in which they are reachable, and §10 makes two new
`lean-reject` fixtures a deliverable rather than a nice-to-have.

> **Discharged 2026-08-21.** Both reasons are now asserted, by
> `invalid-send-target-undeclared.json` and `invalid-send-message-server-unknown.json`, and the
> corpus is fourteen documents rather than twelve. The paragraph above is kept as written because it
> is the argument that produced the deliverable, and because the claim it makes is the one this
> section exists to justify: these conjuncts are checked upstream, so the translation's steps 2 and 3
> are unreachable from frontend output *and* were, until now, unreachable from the test corpus too —
> defensive code guarded by an untested predicate. Only the second half of that has changed.
>
> One qualification the deliverable did not meet, stated here because §10 counted fixtures rather
> than channels: `sendsResolveToMessageServers` also fails when a send's payload length disagrees
> with the message server's parameter count (`Relico/DTR/GeneralWellFormed.lean:282`), and no
> document exercises that. The reason is asserted; one of its two channels is not.

**Genuinely new, and genuinely the translation's own.** Two refusals have no upstream owner because
neither is a malformedness — each is a legal DTR model that this target mapping cannot carry:

1. **An arity-zero external send** (§5.3). The model is well formed; the port declaration it needs is
   unmeasured, and the project does not guess about `lfc`.
2. **A generated-name collision** (§4.3), when two distinct sites on one class concatenate to one port
   name — either two distinct (rebec, message) pairs colliding outright, or a pair's ordinal suffix
   colliding with another pair spelled to end in that digit. The model is well formed; the naming rule
   is not injective.

Both stay `Except String` rather than becoming `GeneralDiagnosticReason` constructors, which is
the existing division of labour — reasons describe what is wrong with a *document*, and these describe
what this *translation* cannot represent — and each message must say which of the two it is in those
terms. Refusal 1 additionally names the missing measurement, so that the day the probe runs, the
person reading the message knows the refusal is provisional.

**And one refusal that was designed and then designed away.** Two sends to one (rebec, message) pair
with different delays was to be refused; §6 shows the refusal would have been both unsound as stated and
an obstacle to a legal model, and that keying on the send site removes the need for it. It is recorded
here rather than deleted because the surviving §9 guard is the only thing in stage E that now stands
between a legal DTR model and a mistranslation, and a reader comparing this section against the
implementation should be able to see that the missing refusal is missing on purpose.

**What replaces stage D's characterisation.** `compileGeneralModel_ok_iff_selfSendOnly` (`:3181`) proves
acceptance and self-send-onlyness are the same condition, and stage E deletes that biconditional on
purpose — it is the theorem whose falsification *is* the stage. It is not replaced by another
biconditional, and the reason is worth stating rather than eliding: acceptance now depends on
cross-class resolution, payload arity and rendered-name distinctness, so a faithful
characterising predicate would be a mirror of the resolution pipeline, and a mirror is the shape of
defect this development keeps finding elsewhere in the repo. Instead stage E owes two statements that
are together more useful and separately provable:

- **Acceptance implies well-formedness.** If `compileGeneralModel model = .ok program` then
  `program` satisfies the LF well-formedness predicate — ports declared, connections resolving,
  `targetEndpointsUnique`, `declaredNames` `Nodup`, payload agreement across every connection. This is
  the direction that protects the printer and `lfc`, and it subsumes P20's uniqueness requirement
  (§4.3).
- **A sufficient condition for acceptance.** A decidable predicate over DTR models — no arity-zero
  external send, no colliding generated names, and DTR well-formedness — that
  implies `.ok`. It is deliberately *sufficient* and not *necessary*, and saying so in the theorem's
  own docstring is the difference between an honest lemma and stage D's biconditional overreaching
  into a stage that had not happened yet. Note that delay agreement is **not** a conjunct: it was one
  until §6 was rewritten, and per-site ports removed it.

> **Refuted 2026-08-22 — finding F52.** The second statement is **false as worded**, and the empty
> model refutes it. `⟨[], []⟩` satisfies all three conjuncts — DTR well-formedness is five conjuncts
> over lists that are now empty, and a model with no classes has no send to be arity-zero or to
> generate a name that could collide — while `compileGeneralModel` refuses it, because
> `LF.GeneralProgram.wellFormed`'s first two clauses are `reactorsNonEmpty` and `instancesNonEmpty`.
> Measured rather than argued, and routing succeeds (`routes=0`), so the refusal is the guard's. The
> bullet is kept as written because the paragraph above supplies the standard that makes the
> counterexample legitimate rather than pedantic: the translation is total on the *type*, so a
> predicate over `DTR.GeneralModel` has to meet the empty model.
>
> Non-emptiness is the missing conjunct, but adding it does not rescue the wording. *"No colliding
> generated names"* cannot be read off a DTR model — `outputPortNameFor` is not injective (F34, F42),
> so collision is decidable only by running the generator, which is the pipeline reference this
> section forbids two sentences earlier. The fear is right about **duplication**, which can drift from
> what it duplicates; it over-generalises to **reference**, which cannot, there being one
> implementation.
>
> So what is actually owed here is this section's own **title** rather than its body. Acceptance
> factors into exactly three conditions — the model is non-empty, name resolution succeeds for every
> class, and the guard passes — and **nothing between them can fail**, which is where the
> site-totality induction earns its keep. As a biconditional that *replaces* stage D's deleted
> `compileGeneralModel_ok_iff_selfSendOnly` with a stronger statement, and it localises the refusal
> surface to two sites, which is what a fragment boundary is for. **No sufficient condition can omit
> the guard**: F32/F43 make the guard refuse legal DTR models, and F34/F42 make that refusal
> unpredictable from the source. That is F52's positive content, and the owed theorem is stated
> against it.

## 9. How F32 is discharged, and why the answer is neither of the two options offered

F32 records that nothing proves `compileGeneralModel`'s output is well formed, and that the obvious
statement — `compileGeneralModel m = .ok p → m.wellFormed → p.wellFormed` — is **false as stated**,
because `LF.GeneralReactor.declaredNames` (`GeneralWellFormed.lean:84`) unions constructor formals with
state variables while `DTR.GeneralModel.namesUniqueAndValid` (`DTR/GeneralWellFormed.lean:323`) never
mentions state variables at all. Four assertions witness it and they stay.

F32's own instruction is that stage E must choose between **(a)** an explicit extra hypothesis on the
theorem and **(b)** a proof that the elaborator's guarantee implies the LF predicate, and must say why;
adding a mirror clause to `DTR.GeneralModel.wellFormed` is explicitly retracted, because
`Relico/Frontend/GeneralElaborator.lean:793–796` already refuses a formal that shadows a state variable
and the two layers genuinely partition the question. This design takes a **third** road, and the
argument for it is that both offered options are worse in ways that are visible before either is
attempted.

**Why (a) is weak.** An extra hypothesis is the mirror clause again, moved from a definition into a
binder. It does not collapse the partition, so it is not *wrong* — but the hypothesis has no
discharger. No call site in this repo can supply it, so the theorem would protect nothing while
looking as though it protected something, which is precisely the failure mode this project keeps
finding in the paper and in its own earlier families.

**Why (b) cannot close, and why finding that out is valuable.** Option (b) requires the elaborator's
guarantee to be strong enough to imply the LF `Nodup`. It is not. Work through the union: formals
against state variables is guaranteed (`.parameterShadowsStateVariable`); formals internally and state
variables internally are guaranteed (`duplicateParameter`, `duplicateStateVariable`); actions
internally follow from distinct message-server names plus `actionNameFor_injective`. What is guaranteed
by **nothing** is *actions against state variables and formals*. A class with
`statevars { int tick_action; }` and `msgsrv tick() { … }` is, as far as any rule in this repo says,
ordinary Timed Rebeca: the elaborator has no opinion about the `_action` suffix, `namesUniqueAndValid`
does not relate the two lists, the translation is name-preserving, and the emitted reactor declares
`tick_action` as both a state variable and a logical action. So (b) would fail, and the failure would
be the finding — a hole *reachable from a `.rebeca` file*, unlike F32's own hand-built witness. Stage E
adds ports to the same union, so it inherits the identical exposure for port names.

That claim is stated as a **hypothesis with an experiment**, not as a result, because F32's own
correction is the cautionary tale: a toolchain measurement was turned into a pipeline conclusion
without checking the layer in between, and the layer in between refuted it. Here the layers in between
are the Java exporter and the elaborator, and nothing yet measured says either rejects a state variable
named `tick_action`. §11 records the experiment.

**The third road: the translation validates its own output.** `LF.GeneralProgram.wellFormed` is
`Bool`-valued and decidable, so `compileGeneralModel` can compute it on the program it has just built
and refuse when it is false. Stage E adopts that, and it subsumes §4.3's generated-name-collision
refusal — that refusal is simply this one, seen from the naming side. What it buys:

- **The preservation theorem becomes true with no extra hypothesis and no cross-layer import.**
  Acceptance implies well-formedness because acceptance now *entails a check* of it. No mirror clause,
  no unbound binder, no collapse of the elaborator/DTR partition, and no new module importing both
  ends — which matters concretely, since `Relico/Translation/GeneralBasic.lean` imports DTR *syntax*
  only and cannot mention DTR well-formedness at all.
- **The `tick_action` model is refused with a diagnosable message** instead of producing LF that
  `lfc`'s validator accepts and whose generated C++ then fails to build. That asymmetry is measured:
  probe `param_state_name_collision` shows the validator accepting a parameter/state collision and
  clang then reporting `reference member 'x' binds to a temporary object…` attributed to
  `src/V0Controller.lf:1:1` — an error no user could act on. Catching it in our own predicate is
  strictly better than delegating to the toolchain, and this is where
  `GeneralWellFormed.lean:81`'s conservatism earns its keep.
- **It is honest about where the content went.** The theorem becomes short — a guard implies the
  predicate it guards — and the docstring must say that the triviality is deliberate and that the real
  obligation moved to *reachability*: the refusal must be exercised by a fixture, or the guard is
  untested code. That is the same lesson `lean-reject/invalid-parameter-shadows-state.json` taught at
  `b14809b`, where a guarantee three docstrings relied on turned out never to have been tested.

What is lost, and it is worth naming: option (b) would have told us something about *the elaborator*
that the guard does not. So (b) is not abandoned, it is **demoted** — from stage E's mechanism to a
separate question worth answering later, with its value understood as diagnostic rather than
protective. The F32 experiment already written down (rename one `Configured` formal to `limit` or
`enabled` in `widenedModel`, then assert what all three predicates say) still runs in stage E, because
it is what tells us whether the guard is reachable at all from a hand-built model.

Two consequences for the rest of the stage. Every one of the nine committed positives must still pass
the guard, which is a prediction to state before the gate runs rather than a hope. And the guard's
refusal message must distinguish *which* conjunct failed, or the first user to hit it learns only that
their model is unwell.

## 10. What breaks, what is owed, and what the gates must say

### 10.1 The tripwires, all of which were planted on purpose

Stage D wrote theorems whose job was to fail here. Each is listed with what happens to it, because a
tripwire that is quietly deleted is indistinguishable from a regression:

| theorem | line | fate |
| --- | --- | --- |
| `assembleGeneralReactor_inputPorts` | `1222` | **falsified**; restated as the §7.2 projection |
| `assembleGeneralReactor_outputPorts` | `1234` | **falsified**; restated as the `outputPortEnvOf` projection |
| `assembleGeneralProgram_connections` | `1511` | **falsified**; restated over `routesOf` |
| `compileGeneralReactiveClass_ports` | `1970` | **falsified**; restated |
| `compileGeneralReactiveClasses_ports` | `2031` | **falsified**; restated |
| `compileGeneralModel_connections` | `2097` | **falsified** — its docstring already names itself *"the theorem stage E has to break"* |
| `compileGeneralModel_ports` | `2146` | **falsified**; restated |
| `assembleGeneralMessageReaction_priority` | `850` | **stays true**; priority is stage G, and stage E multiplies the reactions it will attach to |
| `assembleGeneralStartupReaction_priority` | `985` | **stays true** |
| `compileGeneralModel_ok_iff_selfSendOnly` | `3181` | **deleted** |

The last one takes a great deal with it. The self-send predicate chain (`:449–:576`) and its
characterisation theorems (`:2679–:3204`) are roughly twenty-two declarations whose only consumer is
that biconditional. They are **deleted rather than retained**, because a predicate nothing consumes is
exactly the dead-code defect this project already found and criticised elsewhere in the repo, and
keeping a chain of correct theorems about a condition that no longer decides anything would be a
monument rather than a proof.

Two things about that deletion are worth stating precisely. First, the biconditional is falsified
**twice over**, and the second way is easy to miss: §9's well-formedness guard refuses some
self-send-only models — the `tick_action` class is self-send-only and now refused — so acceptance and
self-send-onlyness come apart even on inputs containing no external send at all. Second, and following
from that, **stage E is not conservative over stage D.** There exist models stage D accepted that stage
E refuses. Every one of them is a model whose LF output was ill formed, so the non-conservativity is a
bug fix, but it must be written as a finding and not discovered by a confused user later. All nine
committed positives are predicted unaffected, and the gate is what settles that.

### 10.2 Theorems owed

Beyond restating the seven falsified projections: the two statements of §8 (acceptance implies
well-formedness; a sufficient decidable condition for acceptance), the two one-sided port-name
injectivity lemmas of §4.3 sitting beside `actionNameFor_injective` in
`Relico/Translation/NameGeneration.lean`, `targetEndpointsUnique` of the emitted program from route-key
distinctness (§7.2), and an explicit statement of the **reaction declaration order** — that a
receiver's port reactions for one message server appear in main-block instance-declaration order —
paired with a docstring saying in as many words that this is *not* a priority result and that stage F
owns that claim.

And one more, which is the theorem the whole of §6 exists to make provable: **no reaction of an emitted
reactor sets one output port twice.** Stated over the compiled body of a single reaction — for any
class `C` accepted by the translation and any reaction of the emitted `reactor C`, the list of port names
appearing in that reaction's `setPort` statements is `Nodup`. It follows from the site being an address
(§7.1): two `setPort`s in one compiled body come from two statements at two indices of one body, so their
sites differ, so `outputPortEnvOf` gave them different port names or refused. This is the invariant that
under the pair-keyed design could not be stated at all, and it is worth writing as a theorem rather than
leaving implicit precisely because it is the guarantee that a message cannot be silently dropped. It
also has a reachability obligation of the same kind as §9's guard: a fixture whose class sends the same
message twice to the same rebec must exist, or the theorem is about a case nothing exercises (§10.3).

### 10.3 Fixtures, counts and the documents that must move together

- One **new positive**, carrying three things at once: an external send to a message server of arity ≥ 2,
  which is the only way the struct-typed port of §5.2 gets exercised; **two sends from one body to the
  same (rebec, message) pair**, which is the only way the site key, the ordinal suffix and the §10.2
  `Nodup` invariant get exercised; and **two different `after` values on those two sends**, which is the
  case the pair-keyed design refused and this one must translate. One fixture rather than three is
  chosen deliberately — it keeps positives at 9 → 10 and so leaves the advance prediction intact, and
  diagnosability lives in the assertion granularity rather than the fixture granularity, since each
  bridge assertion names the one property it checks. Positives 9 → 10 means `EXPECTED_ASSERTIONS` —
  computed at `frontend/check-general-lean.sh:132` as `POSITIVE_COUNT + LEAN_REJECT_COUNT` — moves on its
  own.
- Two **new `lean-reject`** documents for `sendTargetsDeclaredFailed` and
  `sendsResolveToMessageServersFailed` (§8), taking `lean-reject` 12 → 14 and reason coverage 9 → 11 of
  32. These are the first two reasons in the whole vocabulary that *require* a send to another actor to
  be reachable at all.
- `EXPECTED_PRINTER_ASSERTIONS` is the one hand-maintained literal, at
  `frontend/check-general-lean.sh:189`, currently 60. It must be recomputed, not guessed, and the new
  value stated before the gate runs.
- The assertion at `frontend/lean-bridge/GeneralLfPrinterTestMain.lean:1632–1633` asserts the
  external-send **refusal** text verbatim. It inverts: the same model must now compile, and the
  assertion becomes a statement about the emitted ports, connections and reaction order.
- `Relico/LF/GeneralWellFormed.lean:81` still says of a parameter/state name collision that *"whether
  `lfc` rejects that spelling is unverified"*. Probe `param_state_name_collision` verified it on
  2026-08-20 — the validator **accepts** it and the generated C++ then fails to build — so that
  sentence is stale, and §9 cites the line it sits in as support. It must be rewritten in the same
  commit that lands the guard, or the design will be resting on a docstring that contradicts it.
- Counts appear as **spelled-out English words in several files at once** —
  `frontend/fixtures/general/README.md`, `lean-reject/README.md`, and `docs/STAGE_B_FINDINGS.md`'s F20
  entry, whose "9 of 32" needs a second dated update. `frontend/test_validate_general_v1.py:774` reads
  the fixture README, so a markdown-only edit there is not gate-free. Four stale counts survived
  `b14809b` for exactly this reason; grep the words, not the numerals.

### 10.4 The gates

`GENERAL_LEAN_GATE_OK` runs as before. Job count is predicted **508**: one new module,
`Relico/Translation/GeneralRouting.lean`, carrying the routing table and its lemmas, imported into
`Relico.lean`; port naming goes into the existing `NameGeneration.lean` and adds no job. Everything else
is edits to `Relico/LF/GeneralSyntax.lean`, `GeneralWellFormed.lean`, `GeneralCppPrinter.lean` and
`Relico/Translation/GeneralBasic.lean`.

`GENERAL_LF_TARGET_OK` is where stage E is actually decided. It currently emits, compiles with real
`lfc` and runs two programs; stage E adds a **third**, and it is the first generated text in this
project's history to contain an output port, an input port and a connection. Everything it needs is
measured in isolation (§3) and nothing has yet been measured in *combination through the printer*,
which is exactly the difference that made the 2026-08-20 target gate worth running. The prediction to
state in advance: `lfc` exit 0, `SUCCESS`, binary exit 0, no `-Wunused-private-field`, and — for the
`fan-in` shape — three input ports and three connections on one `Gateway` instance.

## 11. What this design found, what it still owes, and what only you can decide

### 11.1 Findings this design produced

Numbers continue the single repo `F` series after F33 and are **provisional until the findings file
lands** — stage D's design taught this the hard way, when its own D1–D9 had to be renumbered to F21–F29
and the D-numbers became uncitable. Do not cite these elsewhere yet.

- **F34 — the readable port-naming rule is not injective.** `"reportTo"` with rebec `"hub"` and
  `"report"` with rebec `"toHub"` both produce `reportToToHub`, and every readable separator has this
  property, underscores included. Any implementation that claims unique port names from a
  concatenation rule without either escaping the separator or checking the result is wrong. Ledger P20
  stands independently: the paper's two figures disagree about port names, and neither offers a rule
  that survives this.
- **F35 — DTR delays a statement, LF delays a connection, and that is a naming problem rather than an
  expressiveness one.** *Weakened on 2026-08-20; the original claim was that two sends to one (known
  rebec, message) pair with different `after` values are **unrepresentable**, and it was wrong.* They are
  representable, by giving each send site its own port and its own connection (§6.2); what is true is
  only that the paper's figures place the delay on the arrow and never show two sends to one pair, so
  they never confront the choice, and an implementation that keys ports on the pair — the obvious
  reading of those figures — is forced either to lose messages or to refuse legal models. That is worth
  recording as a finding about the figures. Whether it is *also* a P-series correction depends on a
  paper reading that has not been done (§11.2).
- **F36 — the port layer still has the type erasure stage D removed from the action layer.**
  `LF.GeneralPortDecl.declaredType : LF.GeneralType` with `GeneralType = int | boolean` cannot type a
  port that carries two values, which is the same shape of gap as `initialValue : Int` and
  `msgsrv logic(boolean, boolean)`, surviving one layer further along.
- **F37 — a derived name becomes a stored one.** The payload struct's name is derived at exactly one
  site today; §5.2 stores it at both ends of a connection and *checks* agreement. Stage D's "cannot
  disagree" becomes stage E's "is checked", which is weaker, and the printer's own stated principle
  about deriving rather than storing is the reason to record it rather than let it pass.
- **F38 — hypothesis: the `_action` suffix is unreserved, and that is reachable from source.** A class
  with `statevars { int tick_action; }` and `msgsrv tick()` appears to be accepted by the exporter, the
  elaborator and DTR well-formedness, and to translate to a reactor declaring `tick_action` as both a
  state variable and a logical action. Unlike F32's witness, this one comes from a `.rebeca` file.
  Stated as a hypothesis with an experiment, deliberately, because F32's correction is the standing
  lesson about concluding across an unchecked layer. Stage E's own port names inherit the same
  exposure, and §9's guard is what contains both.
- **F39 — stage E is not conservative over stage D.** The well-formedness guard refuses models stage D
  accepted. Every such model had ill-formed LF output, so this is a bug fix, but a stage that removes
  inputs while adding capability should say so out loud.
- **F40 — a design document's own defect: one port per (rebec, message) silently drops messages, and
  the refusal that seems to fix it cannot.** This is recorded against §6 of this document as committed at
  `6298284`, not against the paper, because a design that was reviewed and landed is exactly the kind of
  artifact whose errors are worth keeping visible. Three parts, each independently reusable:
  1. **The blessed case was the broken one.** §6 said of two sends to one pair with the *same* delay:
     *"fine. They deduplicate to one connection, and the second statement is a second `set()` on the same
     port."* An LF port carries one value per
     tag, so `hub.report(1); hub.report(2);` — two Rebeca messages, two runs of `report` — becomes one
     reaction firing. A message is lost with no error anywhere, which is the worst possible failure mode
     for a translator that carries a preservation theorem.
  2. **A sound syntactic refusal refuses the wrong thing.** "Two sends arrive at one tag" is a property
     of executions. `report after 2` and `report after 5` in two message servers coincide whenever the
     first fires three units after the second, so any sound static rule must refuse *every* class with
     two sends to one pair, delay-independent — which refuses the differing-delay case that must work.
     There is no refusal that satisfies both requirements, and finding that out is what forced the
     redesign rather than a patch.
  3. **The key was the error.** Keying on (rebec, message) is the natural reading of the paper's figures
     and it is what makes the hazard exist at all. Keyed on the send site, the invariant is structural
     (§10.2) and the delay question dissolves (§6.2). Two Rebeca messages become two ports; the target
     model was never short of expressiveness.

  The user's requirement that drove the redesign is on the record in these terms: two sets on one output
  port at one time must not be allowed in LF, two invocations of the same action are acceptable, and DTR
  source that would produce the first must be rejected with the reason stated clearly — mechanism
  delegated. Making it structurally unreachable satisfies that requirement more strongly than rejecting
  it would, since there is no source program left to reject.

### 11.2 Owed measurements and readings

Each is stated with its prediction now, so the prediction cannot be adjusted afterwards.

1. **Is a payload-free port declaration legal?** Try a bare `input in` and an `input in: void`, plus the
   output side. *Prediction: the bare typeless form is rejected* — the probe log already contains
   `Input must have a type.` — *and `: void` is accepted and compiles*, on the expectation that
   reactor-cpp specialises a valueless port. Confidence high on the first, moderate on the second. If
   the second holds, §5.3's arity-zero refusal becomes a translation, in this stage or the next.
2. **Does `p.set({a, b, c})` compile without naming the struct?** Not needed by this design, but it
   would remove the printer's dependency on the port's stored payload. *Prediction: ambiguous overload
   resolution, so no.*
3. **What does the paper actually say about the send rule and where the delay goes?** This is what turns
   F35 into a P-series correction or leaves it a repo finding. The paper is a PDF **outside** the
   repository at `~/Desktop/LFStructuringNonDeterminism/DTR_LF__After_FMCAD_.pdf`, and it is never
   edited as a side effect of anything.
4. **Fig. 5's `ActionDecl` production**, owed since stage D to settle **F26**. Same document, same
   reading, so it costs nothing extra.
5. **F38's experiment**, which needs the Java exporter and therefore Maven on the Mac, through
   `frontend/java-bridge/check-general.sh`. It shares that requirement with pending task #36, the
   `reject/` fixture for a constructor formal shadowing a state variable, so the two should travel
   together.
6. **F32's own experiment**, already written down: rename one `Configured` constructor formal to
   `limit` or `enabled` in `widenedModel` and assert what `DTR.GeneralModel.wellFormed`,
   `compileGeneralModel` and `LF.GeneralProgram.wellFormed` each say. It now tells us whether §9's
   guard is reachable rather than whether a soundness gap exists.
7. **What does a second `schedule()` of one logical action at one tag do?** This one is owed by **stage
   D's landed self-send path**, not by stage E: `self.tick(); self.tick();` emits two
   `tick_action.schedule(0ms)` calls in one reaction, and no committed fixture exercises it —
   `priorities` self-sends twice from its constructor but to two *different* message servers, so nothing
   coincides. Probe the three candidate behaviours (the reaction fires twice at successive microsteps,
   fires once, or `lfc`/reactor-cpp errors) and probe `policy: defer` with a minimum spacing alongside,
   since deferring a coincident schedule to the next microstep is the mechanism that would reproduce
   Rebeca's queue faithfully and this design never considered it. *Prediction: the default policy fires
   the reaction twice at successive microsteps and neither the validator nor clang complains; `defer`
   changes the spacing but not the count.* Confidence moderate. Stage E's external-send path deliberately
   does not depend on the answer — §6.2 gives each site its own port — so this is a stage D debt being
   recorded rather than a stage E blocker. Note also what is **not** owed: the corresponding question for
   ports, what a second `set()` on one port at one tag does, is now unreachable by construction (§10.2),
   so it stays unmeasured on purpose.

### 11.3 Decisions this design cannot make for you — all four answered on 2026-08-20

The port-name **spelling** was never on this list: it was delegated with the criterion *readable and
unique*, and §4.2 exercises the delegation rather than re-asking. Four things genuinely were, and each
now records the answer given rather than the question asked, so that a later reader can tell a decision
from an assumption:

1. **Payload arity — ANSWERED: arity ≥ 1 now.** `GeneralPortDecl` is widened per §5.2 so a
   multi-parameter message server can be reached externally. The alternative was restricting stage E to
   arity 1, keeping the LF layer untouched, and deferring the struct-typed port to its own stage; the
   corpus needs only arity 1, so the narrow choice would have cost no fixture. The wide choice spends a
   measurement (`struct_as_port_type`) that is already paid for and avoids leaving `GeneralPortDecl`
   structurally unable to express a port the target demonstrably accepts. As designed.
2. **F32's resolution — ANSWERED: road (c), the translation validates its own output.** §9 stands. The
   F32 note had said to choose between an extra hypothesis and a cross-layer proof; the answer overrode
   that written instruction knowingly, after the three roads were compared on the `Ticker` witness
   (`statevars { int tick_action; }` with `msgsrv tick()`): road (a)'s hypothesis is true but
   undischargeable, since `GeneralDecoder` establishes only `DTR.wellFormed`, which relates state
   variables to nothing; road (b) reaches three quarters of the `Nodup` union and then sticks on actions
   versus state variables, with `Ticker` as the counterexample; road (c) needs no DTR import, which
   matters because the translator imports DTR syntax only.
3. **The delay conflict — ANSWERED, and the answer inverted the section.** The rule given was *implement
   it when the delays differ, refuse when they coincide*, which is the opposite of what §6 had written.
   Working out how to satisfy it produced the per-send-site design, and with that the "refuse when they
   coincide" half needs no refusal at all: coincidence on one port is structurally unreachable (§6.2,
   §10.2). Both halves of the answer are therefore honoured, one by translation and one by construction,
   and F40 records what was wrong.
4. **Non-conservativity — ANSWERED: keep the refusal.** §9's guard refuses rather than warns, so stage E
   refuses inputs stage D accepted (F39). The alternative would have kept every stage D input working and
   let ill-formed LF reach `lfc`. As designed.

Nothing on this list blocks implementation any longer. What remains open is measurement, not decision,
and §11.2 holds it.
