# Stage C design: concrete LF ports and connections

**Status: implemented and green.** All seven files of §4 exist;
`bash frontend/check-general-lean.sh` reports `GENERAL_LEAN_GATE_OK` with
`lake build` at 506 jobs and 45 assertions (20 frontend, 25 general-LF). Six
divergences from this document were found while implementing it and are recorded
in §9 rather than folded back into the sections above, so that the design and what
was actually built can still be compared.

Stage C gives the Lean LF layer the two constructs it has never had: ports and
connections. It is a representation and printing stage. Nothing in it translates
a DTR model — translation is stage D without external sends, stage E with them,
and stage F for the many-to-one case of paper section III-D.

## 1. Measured starting point

Every claim in this section was read out of the repository before the design was
written, and the file and line numbers are given so a reviewer can check them.

The repository names this stage itself. `Relico/LF/GlobalMultiStorePayload.lean`
lines 20-21 say, of the multi-actor program it defines: *"The topology is still
abstract at E2. Concrete LF ports and connections remain a later layer."* Stage C
is that layer.

**The abstract topology already exists and is already well-formed.**
`Relico/Common/ActorTopology.lean` (777 lines) defines
`KnownRebecName`, `KnownRebecBindings := Store KnownRebecName ActorName`,
`ActorTopology := Store ActorName KnownRebecBindings`, a `resolve` that maps a
sender and a known-rebec name to a target actor, and a two-level `wellFormed`
that requires unique keys at both levels, agreement between the actor keys and
the topology keys, non-empty actor names, non-empty known-rebec names, and every
bound target to be a declared actor. It also carries the reusable
`Store.mapValuesWithKey` / `Store.zipValuesWithKey` machinery and their lemmas.
Stage C does not re-derive any of this. A connection list is a *concrete
realization* of that abstract relation, and stage D/E is where the two are tied
together by a theorem; stage C only has to make the concrete form expressible and
checkable.

**The general model that stages C-F consume is already decoded.**
`Relico/DTR/GeneralSyntax.lean` gives `GeneralActorInstance` a real `bindings :
KnownRebecBindings` field and derives `def topology` (line 597) from the instance
list rather than storing it, with `lookup_topology`, `resolve_topology_of_actor`
and `resolve_topology_of_missing` proved. `Relico/Frontend/GeneralElaborator.lean`
line 937 builds those bindings from the bridge document
(`bindings := raw.bindings.map bindingOf`). This matters because the *old*
family's decoder hardwires `([] : KnownRebecBindings)` at
`Relico/Frontend/GlobalMultiStorePayloadDecoder.lean:184`, which is why no earlier
stage could have had a non-trivial connection list even in principle.

**The LF AST that stage C extends is small and complete.**
`Relico/LF/Syntax.lean` is 85 lines: `Expr` is `intLiteral | stateVar`; `Stmt` is
`assign | schedule`; `Trigger` is `startup | logicalAction`; a `Reaction` is a
name, a trigger and a body; a `Reactor` is a name plus exactly one state variable,
one logical action, one startup reaction and one message reaction; a `Program` is
one reactor and one instance. Everything derives
`Repr, DecidableEq, BEq, Inhabited`. There is no port anywhere in it, and there is
no connection anywhere in it.

**There is no `PortName`.** `Relico/Common/Name.lean` (104 lines) defines exactly
seven name types — `ClassName`, `ActorName`, `VarName`, `MsgName`, `ReactorName`,
`ReactionName`, `ActionName` — each as `structure X where value : String deriving
Repr, DecidableEq, BEq, Inhabited`, each with a `ToString` instance and a
`def isValid (name : X) : Prop := name.value ≠ ""`. Stage C adds an eighth in
that exact shape. This file is imported by every family, so touching it means the
gate is a full rebuild rather than an incremental one.

**Delay is already structurally static and nonnegative.**
`Relico/Common/Time.lean:15` is `structure Delay where value : Nat`. There is no
expression case and no negative case to exclude, so "LF delay has to be static"
needs no new check in stage C — it is a property of the type. `renderDelay delay
= toString delay.value ++ "ms"`, so one `Delay` unit is one millisecond.

**The printers establish the conventions the new printer must match.**
`Relico/LF/CppPrinter.lean` (183 lines) fixes `targetHeader := "target Cpp"`, the
`{= … =}` reaction body form, `renderEffects` as `" -> "` followed by a
comma-separated list, and a `renderMain` that emits `main reactor {` with a single
`<inst> = new <Reactor>()` and **no connections** — with a comment recording that
the main reactor is left unnamed so the generated source does not depend on its
filename. `Relico/LF/MultiStorePayloadCppPrinter.lean` (438 lines) is the most
advanced printer and its layer names are the template: `renderExpr`, `renderExprs`,
`renderStmt`, `scheduledActionNames`, `renderEffects`, `renderActionDecl(s)`,
`renderTrigger`, `renderParameterRead`, `renderBody`, `renderReaction`,
`renderMessageReactions`, `renderReactor`, `renderProgram`. It returns
`Except String String`.

**One printer limit is load-bearing and stage C inherits it rather than widening
it.** `MultiStorePayloadCppPrinter.lean:93-96` rejects an action carrying more
than one payload value, on the stated ground that *"the current C++ printer
foundation supports at most one integer payload"*; lines 144-145 map zero formal
parameters to `void` and one to `int`. Widening this would require introducing a
concrete generated product type, which that printer deliberately does not do.
Ports in stage C therefore carry at most one integer, exactly like actions.


**No Lean module in this repository emits a port declaration or a connection.**
Measured: `grep -rn '"input\|"output\|renderConnection\|renderPort' Relico/` returns
exactly one hit, `Relico/Frontend/MultiStorePayloadCppBackend.lean:78`, which is
the unrelated diagnostic string `"output="`. That is the gap stage C closes, and
it is worth stating as a number rather than a feeling.

**But three committed LF fixtures already have ports and connections, and they
have been through real `lfc`.** Of the 24 `tests/benchmarks/*/expected/lf-source/*.lf`
files, exactly 3 declare ports — the `global-multi-actor-payload` packages
`external-send--positive`, `external-send-frame--positive` and
`finite-execution--positive`. They are **hand-authored expected LF, not printer
output** (they contain `public preamble {= #include <cstdio> =}`, `std::printf`,
and the `timer` that P7 records — no printer emits any of those). That makes them
worthless as a model of what the translator should produce and extremely valuable
as evidence of what `lfc 0.11.0` accepts. The measured concrete syntax is:

```text
reactor Sender {
    output out: int

    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input in: int

    reaction(in) {=
        ...
    =}
}

main reactor {
    sender0 = new Sender()
    receiver0 = new Receiver()
    sender0.out -> receiver0.in after 0 msec
}
```

Four things in that block are decisions stage C would otherwise have had to guess:
port declarations are `output <name>: int` and `input <name>: int` with **no
terminating semicolon**; a port appears in a reaction's effect list exactly as an
action does; a connection is `<inst>.<port> -> <inst>.<port> after <n> msec` with
**no terminating semicolon**; and the accepted time unit is **`msec` with a
space**, not the `ms` the paper's figures print.

**That last point is a trap, and it is the reason stage C does not reuse
`renderDelay`.** `renderDelay` produces `1ms`, and every existing use of it is
*inside* a `{= … =}` body — `dispatch_action.schedule(1, 1ms);` in
`tests/benchmarks/bound-payload--dispatch--positive/expected/lf-source/V0Controller.lf`.
Inside `{= … =}` the text is **C++**, so `1ms` there is a `std::chrono` literal
and says nothing about LF's own time syntax. A connection's `after` clause is LF
syntax. The two languages happen to spell milliseconds similarly, which is
exactly how a printer ends up emitting something that has never been compiled.
Stage C therefore introduces a separate `renderLfTime` for the LF surface and
leaves `renderDelay` untouched for target-code bodies. Whether `after 0ms` is also
legal LF is unmeasured, and is listed as a probe in §8 rather than assumed either
way.


## 2. What the paper prescribes

Scope comes from the paper. Everything quoted here was read directly out of
`~/Desktop/LFStructuringNonDeterminism/DTR_LF__After_FMCAD_.pdf`, per the
provenance rule in [`PAPER_CORRECTIONS.md`](PAPER_CORRECTIONS.md); nothing in this
section is taken from a repository summary of the paper.

**Table III gives the mapping in one row.** `knownrebecs` ↦ *"port declarations and
connections in main"*. That row is the whole of stage C's mandate: the abstract
known-rebec relation, which `ActorTopology` already models, becomes concrete port
declarations on reactors plus a connection list in `main reactor`. The neighbouring
row, `r.m() after(t)` (external send without parameters) ↦ *"output/input ports and
a connection after t"*, is the stage D/E half.

**Fig. 5's relevant productions**, transcribed from page 13:

```text
Reactor      ::= reactor R (ParamList?) {PortDecl* StateDecl* ActionDecl* ReactionDecl*}
PortDecl     ::= input inPort ([intLiteral])? : Type ;
               | output outPort ([intLiteral])? : Type ;
ReactionDecl ::= reaction(TriggerList) (→ OutputList)? {= LFStmt* =}
TriggerList  ::= Trigger (, Trigger)*
Trigger      ::= startup | inPort ([Expr])? | act
OutTarget    ::= outPort ([Expr])? | act
OutputList   ::= OutTarget(, OutTarget)*
LFStmt       ::= outPort ([Expr])?.set(Expr) ; | act.schedule(delay) ; | …
MainReactor  ::= main reactor { InstDecl+ Connection* }
InstDecl     ::= ins = new R(ArgList?) ;
ArgList      ::= Expr (, Expr)*
Connection   ::= ins.outPort ([Expr])? → ins.inPort ([Expr])?(after delay)? ;
```

Four things follow that stage C takes as binding. Port declarations come **first**
inside a reactor, before state, actions and reactions — the existing printers emit
state, then actions, then reactions, so ports go at the top. A reaction's effect
list may name **ports and actions in the same list**; Fig. 1b line 8 is
`reaction(sendReading)->reading,sendReading {=`, which mixes them, so this is not a
grammar artefact. A port write is `port.set(e)` with exactly **one** expression,
which is the paper independently arriving at the printer's one-payload limit. And
`main reactor` takes **one or more** instances followed by **zero or more**
connections, so the single-instance `renderMain` is a special case of the general
form rather than a different shape.

**§III-B states the determinism property the well-formedness check exists to
protect:** *"LF guarantees determinism at each logical time instant: each input
port has a single source (outputs may broadcast). Reactions triggered at the same
time tag execute in lexical declaration order."*

**§III-D states the fan-in construction**, which stage C must be able to represent
even though stage F is what builds it: *"DTR allows multiple actors to send
identical messages to the same target. Since LF prohibits many-to-one port
connections, the translation assigns each sender a unique input port on the target
reactor."* And the ordering rule: *"To preserve determinism when both messages
arrive at the same logical time, reactions are ordered according to DTR actor
priorities. Because `temp` has higher priority than `smoke` (lines 36-38), the
`readingFromTemp` reaction is declared first, ensuring its message is processed
first."*

**§III-E states the delay rule, and it is unconditional:** *"An external send in
DTR with no explicit `after` is treated as delay 0. Our tool translates it to an LF
connection with `after 0ms`, scheduling at the next microstep within the same
logical tag. This avoids causality loops: LF connections without `after` are
instantaneous (same tag (t, m)), and cycles cause compiler rejection due to
non-deterministic execution order."* Every external send therefore yields a
connection carrying an `after`, with `0` as the floor. Stage C encodes that by
making the delay field non-optional rather than by checking it.

**§III-G lists the translation limitations**, and the one that touches ports is:
*"ReLico excludes multiple identical messages from one sender to one receiver at the
same logical time. DTR stores them separately, whereas LF retains only the last
same-time port write, losing multiplicity."*

## 3. What the research turned up before any Lean was written

Five paper divergences came out of reading Fig. 1, Fig. 2, Fig. 5, Table III and
§III-B/C/D/E/G against each other. They are filed as P18-P22 in
[`PAPER_CORRECTIONS.md`](PAPER_CORRECTIONS.md) with the quotations; only their
bearing on stage C is repeated here.

**P18 decides whether the other grammar findings are findings.** §II-B says *"the
complete LF syntax is provided in Appendix A"*, Appendix A is titled *"Complete
Syntax"* and opens *"we give the complete syntax for Deterministic Timed Rebeca and
Lingua Franca"* — but Fig. 5's own preamble says *"This fragment is not intended to
be the complete LF language syntax. It includes only the constructs needed by our
translation."* Under the first reading a production the translation never uses is
just an LF feature; under the second it is surplus in a figure that claims to have
none. P2 and P19 both need the second reading, so the contradiction is load-bearing
rather than cosmetic.

**P19 is the one that changes a type in this design.** `Connection ::= … (after
delay)? ;` makes `after` optional, while §III-E requires every external send to
become a connection carrying at least `after 0ms`, *"to avoid causality loops"*.
The optional form is precisely the one the paper's prose forbids the translator
from emitting. Stage C's connection therefore has `delay : Delay` as a
**non-optional field**: the dangerous form is unrepresentable rather than rejected.

**P20 is an open question, and it blocks stage E/F rather than C.** No rule for
naming a generated port appears anywhere in the paper, and the two figures cannot
both be instances of one rule: Fig. 1b names the receiver's input port
`receiveReading`, identical to the message server, while Fig. 2b names them
`readingFromTemp` and `readingFromSmoke`, which is the *output* port name plus
`"From"` plus the capitalized sender instance name. Where the output port name
`reading` comes from, given a message server called `receiveReading`, is stated
nowhere. Stage C does not need an answer — it takes port names as given — and the
design is deliberately arranged so that stage E/F can supply any naming function
without changing the AST.

**P21 explains an instantiation decision that would otherwise look arbitrary.**
Both figures render DTR `statevars` as LF reactor **parameters** —
`reactor TempSensor(v:int=0)` with `sensor = new TempSensor(v=1)` and no `state`
declaration anywhere — whereas Table III says `statevars` ↦ *"state variables"*, and
Fig. 5's `ArgList ::= Expr (, Expr)*` cannot derive the named argument `v=1` at all.
The repository follows Table III: `state x: int = 0`, constructor assignments inside
the startup reaction, and `new Controller()` with no arguments. Stage C keeps that,
so its `main reactor` printer emits argument-free instantiations. Constructor
arguments are a stage D/E question and widening them here would be scope creep on
top of an unresolved paper inconsistency.

**P22 is adjacent and needs no action here.** Fig. 5's `act.schedule(delay);` has
no payload slot, so §III-C's own `sendReading.schedule(v, 0ms)` is not derivable
even though `ActionDecl` admits a typed action. The payload-carrying printer
already emits the prose form. Ports are unaffected: `outPort.set(Expr)` takes
exactly one expression, which agrees with the printer's one-integer limit.

**One measurement was taken rather than assumed, and it came back permissive.** The
committed fixtures use `after 0 msec`; the paper prints `after 0ms`. Task #74 put all
three candidate spellings through `lfc 0.11.0` on 2026-08-19 as probe 10 of
[`lf_semantics_probe.sh`](../tools/paper-measurements/lf_semantics_probe.sh), and
`after 0 msec`, `after 0ms` and `after 0 ms` **all compile, run and deliver the
message** — one `RELICO_` line each, `lfc` exit 0, run exit 0. Two consequences. The
unit spelling is a free choice, so stage C's ` msec` is justified by byte-identity
with the 24 committed fixtures and not by scarcity of evidence; and the paper's `2ms`
in Fig. 1b line 22 and Fig. 2b lines 41-42 is **not** a compile error, so P19 stays a
finding about the optional `?` alone and no new grade-(a) finding is owed. The
printer still isolates the spelling in `renderLfTime` (§6.1), now for separation of
concerns rather than for hedging against an unknown.



## 4. The design

Seven files, three of them new Lean modules. Nothing existing changes shape: stage
C adds a family the way `MultiStorePayload*` was added, so no printer, semantics or
proof of any earlier family is touched. The one shared file that changes is
`Relico/Common/Name.lean`, and it changes by addition only.

| file | status | why |
|---|---|---|
| `Relico/Common/Name.lean` | modified | add `PortName`, the eighth name type |
| `Relico/LF/GeneralSyntax.lean` | new | ports, connections, multi-instance main |
| `Relico/LF/GeneralWellFormed.lean` | new | the checks of §5 |
| `Relico/LF/GeneralCppPrinter.lean` | new | the printer of §6 |
| `frontend/lean-bridge/GeneralLfPrinterTestMain.lean` | new | the assertions |
| `frontend/check-general-lean.sh` | modified | run them |
| `Relico.lean` | modified | three imports |

**Why the test main is not a `Relico/Tests/` module, which is the choice most
likely to be questioned.** `tests/benchmarks/registry/obligations.tsv` indexes
`Relico/Tests` and nothing else — measured: every one of its 2129 rows has a
`test_file` under `Relico/Tests/`, across the kinds `theorem` (855), `#check` (527),
`def` (516), `example` (142), `#print axioms` (63), `class` (23), `inductive` (2) and
`#guard` (1) — and `tools/relico_bench_registry.py:19` pins
`EXPECTED_OBLIGATIONS = 2129`. Adding a `Relico/Tests/` module therefore means
adding a registry row per declaration and bumping that constant, and each row
carries `final_benchmark_id` and `evidence_role` fields that would have to be
invented, because no benchmark exercises general LF printing yet. Stage B faced the
same choice and put its assertions in
`frontend/lean-bridge/GeneralFrontendTestMain.lean` behind
`frontend/check-general-lean.sh`. Stage C follows it. The registry keeps meaning
what it says, and the cost is that `lake build` alone does not run these
assertions — the gate script does.

### 4.1 `PortName`

```lean
structure PortName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

instance : ToString PortName where
  toString name := name.value

def PortName.isValid (name : PortName) : Prop :=
  name.value ≠ ""
```

Identical in shape to the seven that precede it. `Relico/Common/Name.lean` is
imported by every family, so this is the reason the gate is a full rebuild.

### 4.2 `Relico/LF/GeneralSyntax.lean`

Mirrors `Relico/LF/MultiStorePayloadSyntax.lean` — the same field-per-line style,
the same `deriving Repr, DecidableEq, BEq, Inhabited` on everything, the same
`set_option autoImplicit false` — and it reuses `LF.StateVariableDecl` from
`StoreSyntax.lean` (`name : VarName`, `initialValue : Int`) and `LF.ReactorInstance`
from `Syntax.lean` (`name : ActorName`, `reactorName : ReactorName`) rather than
redeclaring either.

```lean
inductive GeneralExpr where
  | intLiteral : Int → GeneralExpr
  | stateVar : VarName → GeneralExpr
  | parameterVar : VarName → GeneralExpr

inductive GeneralStmt where
  | assign : VarName → LF.GeneralExpr → GeneralStmt
  | schedule : ActionName → List LF.GeneralExpr → Delay → GeneralStmt
  | setPort : PortName → LF.GeneralExpr → GeneralStmt

abbrev GeneralBody := List LF.GeneralStmt

structure GeneralAction where
  name : ActionName
  parameters : List VarName

inductive GeneralTrigger where
  | startup
  | logicalAction : ActionName → GeneralTrigger
  | inputPort : PortName → GeneralTrigger

structure GeneralReaction where
  name : ReactionName
  trigger : LF.GeneralTrigger
  parameters : List VarName
  body : LF.GeneralBody
  priority : Option Nat := none

structure GeneralReactor where
  name : ReactorName
  inputPorts : List PortName
  outputPorts : List PortName
  stateVariables : List LF.StateVariableDecl
  logicalActions : List LF.GeneralAction
  startupReaction : LF.GeneralReaction
  messageReactions : List LF.GeneralReaction

structure GeneralConnection where
  sourceInstance : ActorName
  sourcePort : PortName
  targetInstance : ActorName
  targetPort : PortName
  delay : Delay

structure GeneralProgram where
  reactors : List LF.GeneralReactor
  instances : List LF.ReactorInstance
  connections : List LF.GeneralConnection
```

Eleven decisions in there are deliberate, and each has a reason that is not
aesthetic.

**Ports are `List PortName`, with no width and no payload field.** Fig. 5's
`PortDecl` admits a multiport width `([intLiteral])?`, but P2 measured that
`lfc 0.11.0` rejects `reaction(in[0])` and that a whole-multiport trigger fires once
per tag regardless of channel count, so **multiports cannot implement §III-D** and
named ports are forced. No width field means no indexing, which makes the rejected
construct unrepresentable rather than merely unused. No payload field because every
port in the paper and in the fixtures is `: int` carrying exactly one value — Fig. 1b
writes `reading.set(0)` for a *parameterless* message, and §II-B explains that *"the
value 0 is a dummy value used only to trigger the parameterless destination
reaction"*, so there is no zero-payload port to distinguish.

**`setPort` takes one expression; `schedule` takes a list.** That asymmetry is the
paper's: `LFStmt ::= outPort([Expr])?.set(Expr);` admits exactly one, while a typed
action's payload arity follows the source message server's parameter list. The
`List` also keeps the *translation* total and the *printer* partial, which is the
split the repository already has — `MultiStorePayloadCppPrinter.lean:93-96` is where
a two-payload action is refused, and stage E inherits that refusal site instead of
having to make `translate` return `Except`.

**`GeneralProgram` has a reactor list and an instance list, not one program per
actor.** `GlobalMultiStorePayloadProgram` is
`Store ActorName MultiStorePayloadProgram` plus a topology, i.e. one reactor per
*instance*. The paper maps a reactive **class** to a reactor (Table III,
`reactiveclass` ↦ `reactor`), and P3 is the finding that §III-F's cost bound is
unachievable under any per-instance reading. This shape makes the paper's mapping
the representable one: N instances share one reactor, and a reactor's port set is
the union over its instances, which is exactly what P3 says the honest bound has to
range over.

**`List` rather than `Store`, with explicit finders.** Stage B chose plain lists and
explicit recursion for `findKnownRebec?` deliberately, because deriving
`DecidableEq` and `BEq` independently gives no lawfulness bridge between them. The
stage D structural theorems will compare a DTR list against an LF list, and
list-to-list is the comparison those proofs want. `findReactor?` and `findInstance?`
mirror `findKnownRebec?`.

**`startupReaction` is mandatory, matching stage B's mandatory
`GeneralReactiveClass.constructor`.** The printer, not the AST, is where an absent
constructor is handled: see §6. Keeping the two sides shaped alike is what lets the
stage D translation be a total function on a well-formed model.

**`priority : Option Nat := none` is carried and never consulted.**
`MultiStorePayloadReaction` already has this field. Priority distinctness is a
theorem hypothesis, not a well-formedness conjunct — the settled option-D decision —
so `GeneralWellFormed` must not mention it, and neither may the printer, which
honours *order* rather than the field. It is here so that stage F/G attaches
priority to a reaction that already has somewhere to put it.

**There is no port-read expression, and that is a measured omission rather than an
oversight.** The paper never exhibits one: every receiving reaction in both figures
has an empty body — Fig. 1b line 16 and Fig. 2b lines 28 and 31 are all
`// Process received value`. Binding an arriving value to a message server's formal
parameter is the same problem `renderParameterRead` already solves for actions, and
it belongs with stage E's external-send translation, where there is a source
construct to bind.

**There is no `if` and no `for`.** Fig. 5's `LFStmt` has both. Control flow is stage
H on both sides at once; adding the LF half alone would create a construct nothing
can produce.

**There is no evaluator.** `MultiStorePayloadSyntax.lean` puts `evaluate` beside its
expression type, and stage C deliberately does not, because nothing in stage C
consults one: well-formedness is a name-resolution check and printing is syntactic.
The general family's semantics is stage D, and that is where an evaluator acquires a
caller. Shipping one now would be dead code, which is a thing this project has
already had to write findings about.

**`GeneralConnection` names endpoints by instance, not by reactor.** A connection in
LF lives in `main reactor` and connects *instances*; two instances of one reactor
have distinct connections through the same port names. Naming the reactor here would
make the illegal case representable.

**`delay : Delay` is not an `Option`.** This is P19 in the type system. §III-E
requires every external send to become a connection with at least `after 0ms`, so a
connection without a delay is not something the translator may emit, and `Delay`
being `structure Delay where value : Nat` (`Relico/Common/Time.lean:15`) means static
and non-negative come along structurally.

## 5. `Relico/LF/GeneralWellFormed.lean`

One decidable `Bool` predicate per layer, in the style of `ActorTopology.wellFormed`
and `MultiStoreModelWellFormed` — `decide (… .Nodup)` conjoined with `.all` over
lists, so the whole thing is executable and every conjunct is separately checkable.

```lean
def declaredNames (reactor : LF.GeneralReactor) : List String :=
  reactor.inputPorts.map (·.value) ++
    reactor.outputPorts.map (·.value) ++
    reactor.stateVariables.map (·.name.value) ++
    reactor.logicalActions.map (·.name.value)

def triggerWellFormed (reactor : LF.GeneralReactor) : LF.GeneralTrigger → Bool
  | .startup => true
  | .logicalAction action => reactor.logicalActions.any (·.name == action)
  | .inputPort port => reactor.inputPorts.contains port

def exprWellFormed
    (reactor : LF.GeneralReactor) (parameters : List VarName) :
    LF.GeneralExpr → Bool
  | .intLiteral _ => true
  | .stateVar name => reactor.stateVariables.any (·.name == name)
  | .parameterVar name => parameters.contains name

def stmtWellFormed
    (reactor : LF.GeneralReactor) (parameters : List VarName) :
    LF.GeneralStmt → Bool
  | .assign name value =>
      reactor.stateVariables.any (·.name == name) &&
        exprWellFormed reactor parameters value
  | .schedule action arguments _ =>
      reactor.logicalActions.any
        (fun declared =>
          declared.name == action &&
            declared.parameters.length == arguments.length) &&
        arguments.all (exprWellFormed reactor parameters)
  | .setPort port value =>
      reactor.outputPorts.contains port &&
        exprWellFormed reactor parameters value
```

At reactor level: the reactor name is non-empty; every declared name is non-empty;
`declaredNames` is `Nodup`; the startup reaction's trigger *is* `.startup` and no
message reaction's trigger is; and every reaction's trigger and body resolve against
the reactor.

The `Nodup` over `declaredNames` is one check rather than four because **an LF
reactor has a single name scope**: `input x`, `output x`, `state x` and `logical
action x` in the same reactor are four declarations of one name. Four per-list checks
would accept `input v` beside `state v`, which no LF compiler will.

At program level:

```lean
def wellFormed (program : LF.GeneralProgram) : Bool :=
  !program.reactors.isEmpty &&
    !program.instances.isEmpty &&
    program.reactors.all reactorWellFormed &&
    decide (program.reactors.map (·.name)).Nodup &&
    decide (program.instances.map (·.name)).Nodup &&
    program.instances.all
      (fun instance =>
        instance.name.value != "" &&
          (findReactor? program instance.reactorName).isSome) &&
    program.connections.all (connectionWellFormed program) &&
    decide
      (program.connections.map
        (fun connection =>
          (connection.targetInstance, connection.targetPort))).Nodup
```

Non-emptiness of both lists is Fig. 5, not taste: `LFProgram ::= target Cpp; Reactor+
MainReactor` and `MainReactor ::= main reactor { InstDecl+ Connection* }` put a `+` on
reactors and on instances and a `*` only on connections.

`connectionWellFormed` resolves both endpoints through the instance list and then
through the reactor list, and requires the source port to be one of the source
reactor's **outputs** and the target port one of the target reactor's **inputs**. A
connection naming a real port in the wrong direction is the mistake this check exists
for.

The `Nodup` over target endpoints is the enforceable form of §III-B's *"each input
port has a single source (outputs may broadcast)"*. Note the asymmetry: there is
deliberately **no** `Nodup` over source endpoints, because broadcasting one output to
several inputs is legal and nothing in §III-D needs it forbidden.

### 5.1 What stage C proves

Two lemmas, both extracting content that would otherwise only be executable:

```lean
theorem reactorOfInstance_isSome
    (program : LF.GeneralProgram) (instance : LF.ReactorInstance)
    (wf : wellFormed program = true)
    (member : instance ∈ program.instances) :
    (findReactor? program instance.reactorName).isSome

theorem connection_determined_by_target
    (program : LF.GeneralProgram) (c₁ c₂ : LF.GeneralConnection)
    (wf : wellFormed program = true)
    (m₁ : c₁ ∈ program.connections) (m₂ : c₂ ∈ program.connections)
    (sameInstance : c₁.targetInstance = c₂.targetInstance)
    (samePort : c₁.targetPort = c₂.targetPort) :
    c₁ = c₂
```

The second is the formal content of *"each input port has a single source"*, in a
stronger form than the phrase suggests: an input port does not merely have at most one
incoming connection, it *determines* that connection, so the source instance, the
source port and the delay of an arrival are all functions of where it arrived. Stage E
and stage F need exactly that to give a receiving reaction a well-defined sender.

Printer totality is **not** proved here, and the reason is worth stating rather than
leaving as a gap. The printer's only failure mode is the inherited refusal of an
action with more than one payload value, which `wellFormed` does not exclude — and
must not, because that limit belongs to the C++ printer foundation, not to LF. Making
it a well-formedness conjunct would mean weakening `wellFormed` later, when the
printer grows product payloads. So totality is a conditional theorem owed by the
stage that needs it, with the payload-arity bound as an explicit hypothesis.

### 5.2 Four things `wellFormed` deliberately does not check

**A declared port need not be connected.** Measured: probe 4 behind P3 compiled and
ran a model with an unconnected input port — exit 0, the reaction simply never fires.
This is not a tolerated gap, it is load-bearing. Because one reactor is shared by all
instances of its class, its input-port set is the union over instances, so some
instance of a shared reactor will always carry ports that nothing connects to.
Requiring connectedness would make the paper's own class-to-reactor mapping
unrepresentable.

**A connection may have the same source and target instance.** The tempting rule is to
forbid it, since §III-E sends a self-send to a logical action and only an external send
to a connection. But a DTR known rebec may be bound to the sending actor itself, and
§III-E maps `r.m()` by what the statement *is*, not by who `r` turns out to name. The
construct is also safe for exactly the reason P19 records: the paper's own sentence is
that *"LF connections **without** `after` are instantaneous … and cycles cause compiler
rejection"*, and a stage C connection always carries one. That is now **measured** and
not merely argued: probe 10's `self_acyclic` case compiles and runs, and its
`self_cyclic` case — `reaction(in) -> out` connected back to `in`, a genuine causality
loop broken only by `after 0 msec` — compiles, runs and prints three lines at increasing
microsteps. So a DTR actor that holds itself as a known rebec is translatable, and §III-E's
sentence about `after` breaking cycles is a paper claim confirmed rather than corrected.

**Priority is not mentioned.** Distinctness of priorities is a theorem hypothesis, per
the settled option-D decision. `wellFormed` stays silent about the field for the same
reason `GeneralModel.wellFormed` does.

**Reaction names need not be unique.** LF reactions are anonymous in concrete syntax —
`renderReaction` emits `reaction(<trigger>)` and never the name — so uniqueness would
constrain an identifier the target language never sees. The field exists to identify a
reaction inside Lean, and stage C says so instead of inventing a rule for it.

### 5.3 The order rule

**No function in this family sorts anything.** Reaction order, connection order,
instance order and port order are the order they arrive in. P2 measured two models
differing only in reaction declaration order printing `RELICO_A, RELICO_B` and
`RELICO_B, RELICO_A`, so declaration order is observable, and §III-D's entire mechanism
is that *"the `readingFromTemp` reaction is declared first, ensuring its message is
processed first."* A sort inserted anywhere in this pipeline would be a silent semantic
change, which is why the rule is written down here rather than left to be noticed.

## 6. `Relico/LF/GeneralCppPrinter.lean`

Layer-per-function, `Except String String` at every layer that can refuse, mirroring
`MultiStorePayloadCppPrinter`'s naming (`renderExpr`, `renderStmt`, `renderBody`,
`renderReaction`, `renderReactor`, `renderMain`, `renderProgram`) and its separator
discipline (`String.intercalate "\n"` over rendered pieces, never manual `++ "\n" ++`
chains).

Target shape:

```text
target Cpp

reactor <R> {
  input <p>: int
  output <q>: int
  state <v>: int = <n>
  logical action <a>: int

  reaction(startup) -> <effects> {=
    …
  =}

  reaction(<trigger>) -> <effects> {=
    …
  =}
}

main reactor {
  <inst> = new <R>()
  <inst>.<q> -> <inst2>.<p> after <n> msec
}
```

### 6.1 `renderLfTime` is a new function, and `renderDelay` is left alone

```lean
def renderLfTime (delay : Delay) : String :=
  toString delay.value ++ " msec"
```

This is the single most easily-botched line in stage C. `renderDelay` already exists
and produces `1ms`, and it is tempting to reuse it. Every existing call site is
*inside* a `{= … =}` block, where the text is C++ and `1ms` is a `std::chrono`
literal — which says nothing whatever about LF's own time syntax. The three committed
port-bearing fixtures, which `lfc` accepts, spell a connection delay `after 0 msec`.
So stage C introduces a separate function for the LF spelling and does not touch
`renderDelay`.

Probe 10 has since measured that `after 0ms` and `after 0 ms` compile too (§3), so the
spelling was never the risk it looked like. The separation stands anyway, and for a
better reason than hedging: `renderDelay` answers a C++ question and `renderLfTime`
answers an LF one, and now that both spellings are known-good, folding them together
would let a future change to one silently retarget the other. ` msec` is what gets
emitted, because that is what the 24 committed fixtures contain and byte-identity with
them is the property stage C's tests check.

`->` is emitted, not `→`. Fig. 5 and Fig. 1b both print the arrow as `->` in source
text; the `→` in the grammar's own metasyntax is typography.

### 6.2 Ports print first

`Reactor ::= reactor R (ParamList?) {PortDecl* StateDecl* ActionDecl* ReactionDecl*}`
fixes the order: ports, then state, then actions, then reactions. Inputs before
outputs within the port block, matching Fig. 1b's `Controller` and Fig. 2b. Existing
reactors printed state-then-action-then-reactions, so stage C is prepending a block,
not reordering one — the committed non-port families' output is unchanged, which the
gate checks by rebuilding them.

### 6.3 The effect list is derived from the body, not stored

`reaction(sendReading) -> reading,sendReading` in Fig. 1b line 8 lists both a port and
an action. Rather than adding an `effects` field to `GeneralReaction` — which would
then need a consistency check against the body, and could disagree with it — the
printer computes the list by walking the body and collecting, in **first-occurrence
order**, the target of every `setPort` and every `schedule`. This generalizes the
existing `scheduledActionNames` helper from one action kind to two, keeps the AST
smaller, and makes it impossible to print an effect the body does not produce or omit
one it does.

First-occurrence order rather than sorted order, per §5.3. Fig. 1b's
`-> reading,sendReading` matches the body's `reading.set(0); sendReading.schedule(5ms);`
in exactly that order, so the paper's own example is evidence for the rule and not
just consistent with it.

When the derived list is empty the whole `->` clause is omitted, and that case is
measured rather than assumed: the external-send fixture prints `reaction(in) {= … =}`
and `reaction(keepAlive) {= … =}` with no arrow at all, and `lfc` accepts and runs it.
Fig. 1b's `reaction(receiveReading) {= … =}` is the same shape. It arises for a real
model whenever a message server only assigns state variables.

### 6.4 An empty startup reaction is omitted

If the startup reaction's body is empty, no `reaction(startup)` is printed at all.
Fig. 1b's `Controller` and Fig. 2b's `Controller` each have no startup reaction, and a
DTR class whose constructor assigns nothing and sends nothing produces exactly that
case. The alternative — printing `reaction(startup) {= =}` — has no precedent to lean
on: all **24** committed `expected/lf-source/*.lf` files have a startup reaction with a
non-empty body *and* a non-empty effect list, so an empty one is untested territory, and
a stage about ports is not the place to explore it.

### 6.5 `renderMain` grows instances and connections

```text
main reactor {
  temp = new TempSensor()
  smoke = new SmokeSensor()
  controller = new Controller()
  temp.reading -> controller.readingFromTemp after 2 msec
  smoke.reading -> controller.readingFromSmoke after 2 msec
}
```

Instantiations stay argument-free. Fig. 1b and Fig. 2b both write `new TempSensor(v=1)`,
but that is P21: the figures render DTR state variables as LF *parameters*, contradicting
Table III's `statevars ↦ state variables` row, and `ArgList ::= Expr (, Expr)*` cannot
even derive the named form `v=1`. The repo's committed printer output initialises state
inside the reactor (`state x: int = 0`) and instantiates with `new Controller()`, and
that is what stage C keeps. Changing it would be a translation decision, which is stage
D's, not a printing decision, which is stage C's.

The main reactor stays unnamed, preserving `renderMain`'s existing documented reason:
generated source should not depend on its own filename.

### 6.6 The payload refusal is inherited, not widened

`schedule` with more than one payload expression still returns
`.error "… supports at most one integer payload"`, at the same layer and with the same
message as `MultiStorePayloadCppPrinter.lean:93-96`. Stage C is representation and
printing; loosening a C++-side limit is neither.

## 7. Out of scope for stage C

Each of these is deferred to a named later stage, not left vague.

**No translation.** Nothing in stage C consumes a `GeneralModel`. `knownrebecs ↦ port
declarations and connections in main` is Table III's mapping, and it is stage D and
stage E's to implement; stage C only makes its output expressible. The measured fact
that justifies the split is that all four existing exporters reject `r.m(...)`
outright, so there is no source-side input to translate yet.

**No control flow.** `if` and `for` are stage H. `GeneralStmt` has three constructors
and gains no `ite`, matching `MultiStorePayloadStmt`'s two.

**No semantics and no evaluator.** `MultiStorePayloadSyntax.lean` puts `evaluate`
beside its expression type; stage C's `GeneralExpr` gets none, because there is no
`GeneralLfState` to evaluate against, and inventing one now would fix the port-state
representation before stage F has shown what fan-in needs from it.

**No port read.** `Trigger ::= inPort([Expr])?` lets a reaction be *triggered* by a
port, which stage C represents, but Fig. 5's `LFStmt` has no `inPort.get()` production
at all — the reading in the committed fixtures is `auto payload = *action.get();`, on an
*action*. So a port-triggered reaction in stage C cannot yet name the value that
arrived. That is precisely the gap stage E has to close, and P22 is why it is a paper
question and not only an implementation one: §III-C's own `sendReading.schedule(v, 0ms)`
is already underivable from Fig. 5.

**No multiports and no indexing.** `input inPort([intLiteral])?` and `inPort([Expr])?`
are both in Fig. 5, and P2 measured that `lfc 0.11.0` **rejects** `reaction(in[0])`, so
a bank-indexed trigger cannot be printed into anything that compiles. `PortName` is a
plain string with no width and no index. §III-D's unique-port construction needs
neither.

**No constructor arguments.** Per §6.5 and P21.

**No port-naming rule.** P20 records that no rule exists and that the two figures
disagree — Fig. 1b names the input port after the msgsrv (`receiveReading`), Fig. 2b
after the output port plus `"From"` plus the capitalized sender instance
(`readingFromTemp`). Stage C never invents a name: every `PortName` it prints comes from
its input. Choosing the scheme belongs to stage E and stage F, and wants the paper
question settled first.

**No widening of the one-integer-payload limit.** Per §6.6.

## 8. How stage C gets verified

### 8.1 The probe ran first, alone, and is green

Task #74 went to the Mac **before** any Lean was written, as five tiny `lfc`
invocations added to `tools/paper-measurements/lf_semantics_probe.sh` as probe 10. It
needed no Lean and no benchmark. Measured 2026-08-19 against `lfc 0.11.0`; every case
gave `lfc` exit 0 and run exit 0:

| case | connection | `RELICO_` lines | verdict |
|---|---|---|---|
| `unit_msec` | `after 0 msec` | 1 | accepted — the committed spelling |
| `unit_ms_tight` | `after 0ms` | 1 | **accepted** — the paper's spelling compiles |
| `unit_ms_spaced` | `after 0 ms` | 1 | accepted — whitespace is not required |
| `self_acyclic` | `a.out -> a.in after 0 msec` | 1 | accepted — self-topology is legal |
| `self_cyclic` | same, plus `reaction(in) -> out` | 3 | accepted — the loop advances by microstep |

All five predictions held. Three things follow. Cases 2 and 3 were the reason the probe
preceded the code, and they came back permissive, so `renderLfTime` needs no revision and
the printer's expected strings can be written once. Case 4 closes the question §5.2 left
open. Case 5 is the one worth more than its cost: it builds a genuine causality loop —
`reaction(in)` writing `out`, connected back to `in` — that only the `after` delay makes
schedulable, and it printed `RELICO_SELF_CYCLIC 1`, `2`, `3` at increasing microsteps.
That confirms §III-E's sentence about `after` breaking cycles at grade (a). The ledger is
otherwise twenty-two corrections; a measured confirmation belongs on the record next to
them.

### 8.2 Then the Lean, written blind

Seven files per §4's table, written against named compiling precedents rather than
against guesses — `MultiStorePayloadSyntax.lean` for the AST shape,
`ActorTopology.wellFormed` for the predicate shape, `MultiStorePayloadCppPrinter.lean`
for the printer shape, `GeneralFrontendTestMain.lean` for the assertion harness. This
approach has now held three times, so it is the default rather than an experiment.

The test main asserts, on two hand-built programs:

- a single-reactor single-instance program with one input, one output, one connection —
  `wellFormed = true`, and `renderProgram` equal to an expected string, character for
  character;
- the Fig. 2b fan-in shape: three reactors, three instances, two connections into one
  `Controller` on two distinct input ports, `readingFromTemp` declared first —
  `wellFormed = true`, and the printed reaction order matching declaration order;
- rejection cases, one per §5 conjunct that can fail: empty port name, a port name
  colliding with a state variable, a duplicate instance name, an instance naming a
  reactor that does not exist, a connection whose source port is an input, a connection
  whose target port is an output, and two connections into one target endpoint.

The last of these is the one that matters most, because it is the check that stands in
for §III-B's determinism sentence.

### 8.3 One Mac gate, with a falsifiable prediction

A full rebuild, because `Relico/Common/Name.lean` is imported by every family and
`PortName` lands in it. The prediction is **506 jobs**: 503 at HEAD plus three new
modules, with no `lakefile.toml` change and no new executable target, since bridge mains
run under `lake env lean --run` and are not Lake targets. If the number comes out
differently the prediction was wrong and the reason gets recorded, per standing practice
— olean deletion plus job count is the measurement, never a touch-test, because Lake
hashes content.

`frontend/check-general-lean.sh` gains a block that runs the new main, counts its `PASS_`
lines against the expected total with the `grep -c … || true` idiom already used there,
and prints `GENERAL_LF_PRINTER_TESTS_OK` before the existing `GENERAL_LEAN_GATE_OK`. No
`obligations.tsv` row and no `EXPECTED_OBLIGATIONS` bump, per §4's registry reasoning.

### 8.4 Then three separated steps

Selection gate first: `git status --porcelain --untracked-files=all` must show only the
intended paths. Then commit, then push, then remote verification — each a **separate**
invocation on the Mac, never combined, with explicit `git add` of the seven paths and
never `git add -A`. Every git operation runs on the Mac because the sandbox has no git
identity and would forge the author.

The `.gitignore` `__pycache__/` line (task #49) is already in the working tree and is the
only other dirty path; it goes into this commit rather than being stranded.

## 9. What implementing it changed — six divergences and one process correction

Written after the gate went green, and kept as an appendix rather than folded back into
§4-§6, so that this document still records what was designed and this section records
what was built. Nothing below was discovered by reasoning about the design; each came
from a compiler, a keyword clash, or a missing dependency.

**9.1 The eight program-level conjuncts are named `def`s, not inlined.** §5 writes
`wellFormed` as one expression. Each conjunct is now its own `def` — `reactorsNonEmpty`,
`instancesNonEmpty`, `reactorsWellFormed`, `reactorNamesUnique`, `instanceNamesUnique`,
`instancesResolve`, `connectionsWellFormed`, `targetEndpointsUnique`. This is what makes
the two extraction lemmas independent of how `&&` associates: a proof by case analysis on
a *named* clause cannot silently retarget, whereas a projection chain into an anonymous
conjunction reads a fixed nesting shape and, under the other associativity, proves a
different clause while still compiling. §5's own stated intent — that every conjunct be
separately checkable — is better served this way, and the stage-B sibling already did it.

**9.2 §5's snippet applies a list-level finder to a program.** `findReactor? program
connection.sourceInstance` does not typecheck: §4.2's prose says the finders mirror
`findKnownRebec?`, and that is `List X → Name → Option X`. Resolved as the DTR side is
built — list-level `LF.findReactor?` and `LF.findInstance?`, plus `GeneralProgram.reactor?`
and `.instance?` wrappers mirroring `GeneralModel.class?` / `.actor?`, plus
`GeneralProgram.reactorOfInstance?`, the exact mirror of `GeneralModel.classOfActor?`,
which is also what makes the theorem name `reactorOfInstance_isSome` mean anything.

**9.3 `instance` cannot be a binder name.** It is a Lean command keyword, so §5's
`fun instance => instance.name.value != ""` will not parse. Every binder is
`reactorInstance`. A *trailing* `?` does make an identifier, so `def instance?` is fine —
precedent is `def class?` in `Relico/DTR/GeneralSyntax.lean`.

**9.4 Printer totality is deliberately not proved.** This looks like an omission and is
not. The printer's only failure mode is the inherited multi-value-payload refusal, and
well-formedness does not — and must not — exclude a multi-value payload: the refusal is a
limit of the current C++ foundation, not a property of a legal LF program. A totality
theorem would therefore have to assume away a case the AST is meant to keep representable.

**9.5 The two `GeneralExpr` types are asymmetric, and stage D inherits the debt.**
`DTR.GeneralExpr` carries `boolLiteral`, `binary` and `unary`; `LF.GeneralExpr` carries
only `intLiteral`, `stateVar` and `parameterVar`, exactly as §4.2 specifies. So a stage D
translation **cannot be total** on a well-formed general DTR model, which contradicts
§4.2's own "total function on a well-formed model" rationale. Not resolved here, because no
printer in this development can emit an operator and widening now would create an
unprintable construct. It is recorded in the `GeneralExpr` docstring as a choice stage D
has to make in the open rather than inside a default branch.

**9.6 File 5 carries the well-formedness assertions too.** §4 names it a printer test main.
It runs 25 assertions: 16 printing and 9 well-formedness. Both are pure total functions
over the same hand-built reactors, and a second main would double the gate's cost to assert
nothing the first could not. The alternative — `GeneralWellFormed.lean` with no executable
assertion at all, its two theorems only ever ranging over an arbitrary program — is worse.
Four of the nine are *accept* cases, and they are the point: an unconnected port, a
self-connection and one output feeding two inputs are each legal for a measured reason, and
each is easy to forbid by accident while strengthening something else.

**9.7 Process: `lake env lean <path>` reaches exactly one module past the build closure.**
§8.2's plan to typecheck each new file standalone works for the first one and fails for the
second, because `lake env lean` writes no `.olean` and requires one for every import. The
signature is a single diagnostic at position `1:0` saying *"object file … does not exist"* —
it points at the import, not at any code, and it is not a defect in the file being checked.
The procedure that works, and that was used for files 3 and 4: land each module's import in
`Relico.lean` as soon as that module is green, then use plain `lake build`, which gives the
olean, typechecks the new file, and yields a falsifiable job count in one command.
`lake build <Module.Name>` is not the fix — the default `Glob.one "Relico"` means a
non-globbed module is not a resolvable target.

### 9.8 The gate as measured

`bash frontend/check-general-lean.sh` → `GENERAL_LEAN_GATE_OK`, exit 0. `lake build` at
**506 jobs**, the predicted 503 + 3 new modules, with 0 error lines. 45 assertions: 20
frontend (9 positive documents + 11 lean-reject documents) and 25 general-LF. The
whole-program expected text, derived by hand from the printer source rather than measured,
matched on the first run.
