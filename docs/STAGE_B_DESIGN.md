# Stage B design — the general Lean layer

Status: **approved 2026-08-18, implemented, and graduated into the repository with the first
stage-B commit.** Written 2026-08-18, after stage A landed as `99dff97` / `153e634` / `a859bb0`.
The modules specified below are in `Relico/`, they compile, and the Lean-side gate is
`frontend/check-general-lean.sh`.

**This file is the design as approved, not a description of what was built.** It has
deliberately not been retrofitted, because a design document rewritten to agree with its own
implementation records nothing. Where the two differ, the difference is filed in
[`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md):

- **F1** - the operator set in section 4 is short by two.
- **F2** - well-formedness needed a fifth clause this document does not have.
- **F4** - five deviations in the state section, one of them forced: a design expression that
  does not typecheck.
- **F16** and **F19** - section 8's file list and its gate step 5 are void. It plans eleven
  modules, three of them under `Relico/Tests/` holding inlined JSON negatives checked by
  `lake build` itself. That is not possible: the decoder reads a file, so exercising it needs
  `IO`, and a `#guard` is pure (F16). Eight modules were written; the negatives are documents in
  `frontend/fixtures/general/lean-reject/`, run by
  `frontend/lean-bridge/GeneralFrontendTestMain.lean`; and because nothing was added under
  `Relico/Tests/`, there is no registry change to make, so gate step 5 does not apply (F19).

Reading the two files together is the point. It shows where a design reviewed on paper turned
out to be wrong, which is worth more than a document that appears to have been right all along.

It was written outside the repository deliberately, for the reason recorded as issue #33 - the
previous design document was stranded in a gitignored `tmp/` - and the promise made here was
that it would graduate into `docs/` in the same commit as the first Lean module. This is that
commit.

## 1. Scope, and the measured gap that defines it

Stage B adds a Lean source layer that can represent every model `general-v1` accepts.
It does **not** translate anything. No LF types, no `Translation/` module, no
correspondence proof. Those are stages C onward. Stage B ends when a `general-v1`
JSON file becomes a well-formed Lean term, or a named diagnostic explaining why not.

The gap is larger than "a few more constructors". Measured, the most general
*existing* source AST in the repo is `Relico/DTR/MultiStorePayloadSyntax.lean`:

```lean
inductive MultiStorePayloadExpr where
  | intLiteral    : Int → MultiStorePayloadExpr
  | stateVar      : VarName → MultiStorePayloadExpr
  | parameterVar  : VarName → MultiStorePayloadExpr

inductive MultiStorePayloadStmt where
  | assign   : VarName → DTR.MultiStorePayloadExpr → MultiStorePayloadStmt
  | selfSend : MsgName → List DTR.MultiStorePayloadExpr → Delay → MultiStorePayloadStmt
```

and its model has exactly one class and one actor:

```lean
structure MultiStorePayloadModel where
  reactiveClass : DTR.MultiStorePayloadReactiveClass
  actor         : DTR.ActorInstance
```

with a constructor that carries a body but **no parameters**. The v4 wrapper
(`GlobalMultiStorePayloadModel`) lifts this to `Store ActorName MultiStorePayloadModel`
plus an `ActorTopology`, which is the only place many actors exist at all.

What `general-v1` actually emits, measured from the committed fixture
`frontend/fixtures/general/two-instances.parser.json`: per-class `knownRebecs`,
per-instance `arguments` **and** `bindings` (`{"knownRebec": "hub", ...}`), a unified
`"kind": "send"` statement whose target is either `"kind": "self"` or
`"kind": "knownRebec"`, and expression kinds `intLiteral`, `boolLiteral`, `variable`,
`binary`, `unary`. Constructor parameters are real; instance arguments are real;
booleans are real.

So five things are missing from the Lean side, not one: constructor parameters,
known-rebec declarations, instance bindings, external sends as statements, and
boolean values. Stage B adds all five. Control flow is deliberately excluded — see §7.


## 2. Three findings from the measurement, all of which change the design

### B-1. No decoder in the repo can express topology, so the external-send layer is unreachable

`Relico/Frontend/GlobalMultiStorePayloadDecoder.lean:178-195` builds the topology like this:

```lean
  let topology : ActorTopology :=
    decodedActors.map (fun actorEntry => (actorEntry.2.actor.name, ([] : KnownRebecBindings)))
```

with the doc comment *"every actor receives a matching empty known-rebec binding store
in this additive phase."* Grepping `knownRebec|binding|topology|externalSend` across all
of `Relico/Frontend/` returns **only** these lines. No `Raw*` schema anywhere has a
knownRebecs or bindings field — `RawMultiStorePayloadModel` carries a single `className`
and `actorName`, and `RawGlobalMultiStorePayloadActor` adds only an `Option Nat` priority.

The consequence is mechanical. `ActorTopology.resolve` is

```lean
def resolve (topology : ActorTopology) (sender : ActorName) (knownRebec : KnownRebecName) :
    Option ActorName :=
  match Store.lookup topology sender with
  | none          => none
  | some bindings => Store.lookup bindings knownRebec
```

so with bindings always `[]` it always returns `none`. The first topology step of
`GlobalMultiStorePayloadExternalSend.attempt` is exactly that call, and its `none` branch
is `.error .receiverResolutionFailed`. **Every** external send reachable from decoded
input fails, always, on its first step.

That layer is not small. Files matching `ExternalSendStatement|ExternalSend\.`: 25,
spanning `DTR/`, `LF/`, `Translation/`, `Correctness/` and `Tests/`, including three
correspondence modules. All of it is exercised only by hand-constructed terms under
`Relico/Tests/`. This is the single most important thing stage B fixes: the decoder must
carry real bindings, or stages D–F have nothing underneath them.

Note also that external send is **not** a constructor of the statement inductive. It is a
standalone adapter record, `GlobalMultiStorePayloadExternalSendStatement.Statement`, with
`sender`/`knownRebec`/`messageName`/`payloadExpressions` fields, fed directly to `attempt`.
Nothing that walks a message-server body can produce one. Stage B therefore has to put
sends *into* the statement AST, and the existing `Statement` record becomes the shape the
elaborated AST projects onto rather than a parallel universe.

### B-2. `Value` has no boolean, and `Payload` must not be touched

`Relico/Common/Value.lean` is 40 lines and says `inductive Value where | int : Int → Value`,
with `abbrev Payload := List Int`. `general-v1` emits `boolLiteral`, boolean state
variables and boolean instance arguments (restriction D8 in the fragment doc), and three
of the nine positives use them: `constructor-arguments`, `control-flow`, `expressions`.

`Value` is cheap to widen — referenced in 3 files, imported by 3. `Payload` is mentioned
in **56**. Widening `Payload` would put every existing proof in the blast radius for no
gain. So stage B introduces its own value and payload types in the general namespace and
leaves `Common/Value.lean` alone. This matches how the repo has always grown: five source
ASTs related by explicit embedding functions, never by widening a shared type. It also
makes stage B *purely additive*, which in turn makes its gate cheap — see §8.

### B-3. Nothing derives readiness from a state

This is soundness defect 1 from the actor-priority audit, and it is now pinned. The
definitions exist — `ReadyActor`, `lookupReadyActor`, `simultaneouslyReady`, `earliestReady`,
`sameTimeReadyActors`, `requestCoversReadyActors` at
`Relico/DTR/GlobalMultiStorePayloadActorPriority.lean:24,49,66,77,90,102`, mirrored at
`Relico/LF/GlobalMultiStorePayloadActorOrder.lean:26,51,79,92,105` — but every function
that *produces* a `List ReadyActor` (`readyPair`, `sourceReadyA`, …) lives under
`Relico/Tests/`. No function anywhere computes readiness from a state. `ReadyActor` is an
unconstrained proof index: a caller can assert any cohort it likes, including cohorts the
state contradicts.

Related, and quotable from the decoder itself (`decodeActorPriorityRequest`):
*"Partial requests remain partial; the existing actor-priority semantics therefore impose
no filtering until the simultaneous-ready cohort is fully covered."* So a single
unannotated actor in a ready cohort switches actor priority off for that whole cohort —
`requestCoversReadyActors` fails and eligibility returns `true` unconditionally. That
behaviour interacts directly with the decision in §9.


## 3. Architecture: split reading from narrowing

Every existing decoder fuses three jobs — parse JSON, validate the schema, and narrow to
the verified fragment. That fusion is why each generalization step has meant editing the
reader. Stage B splits them:

**A faithful total reader.** `Relico/Frontend/GeneralSchema.lean` mirrors `general-v1`
*exactly*, including the constructs stage B will not accept: `if`, `for`, `declare`,
`binary`, `unary`, `boolLiteral`. `Raw*` types stay `deriving Repr, DecidableEq, FromJson,
ToJson` and the reader's only failure mode is malformed JSON or a schema mismatch. It never
rejects a model for being outside the fragment.

**A separate elaborator.** `Relico/Frontend/GeneralElaborator.lean` is
`RawGeneralModel → Except Diagnostic GeneralModel`, where `Diagnostic` is an inductive with
one constructor per narrowing reason. Every restriction the fragment imposes becomes a
*named* constructor, so a rejection says which rule fired rather than returning a string.

Stages C–H then widen the elaborator and never the reader. Concretely: when stage H adds
control flow, the reader does not change at all — only the `Diagnostic` constructors for
`if`/`for`/`declare` are removed and the corresponding AST constructors added.

`Failure`-inductive-plus-`Except` is already the repo's idiom (nine constructors on
`GlobalMultiStorePayloadExternalSend.Failure`: `senderModelMissing`, `senderStateMissing`,
`receiverResolutionFailed`, `selfSendNotExternal`, `receiverModelMissing`,
`receiverStateMissing`, `messageServerMissing`, `payloadArityMismatch`,
`duplicateSameEdgeTime`). `Diagnostic` follows it. The `Except String` decoders keep working
untouched; a thin `decodeGeneralModelText : String → Except String GeneralModel` wrapper
renders `Diagnostic` to text for the bridge-check entry point, which is the shape
`runMultiStorePayloadBridgeCheck` already expects.

## 4. The AST

Sketch, in the established style — `set_option autoImplicit false`, one argument per line
in the real file, `deriving Repr, DecidableEq, BEq, Inhabited` throughout. Namespace
`Relico.DTR`, module `Relico/DTR/GeneralSyntax.lean`.

```lean
inductive GeneralValue where
  | int  : Int  → GeneralValue
  | bool : Bool → GeneralValue

abbrev GeneralPayload := List DTR.GeneralValue      -- NOT Common.Payload; see B-2

inductive GeneralBinaryOp where
  | add | sub | mul | eq | ne | lt | le | gt | ge | and | or

inductive GeneralUnaryOp where
  | neg | not

inductive GeneralExpr where
  | intLiteral   : Int → GeneralExpr
  | boolLiteral  : Bool → GeneralExpr
  | stateVar     : VarName → GeneralExpr
  | parameterVar : VarName → GeneralExpr
  | binary       : GeneralBinaryOp → GeneralExpr → GeneralExpr → GeneralExpr
  | unary        : GeneralUnaryOp → GeneralExpr → GeneralExpr

inductive GeneralSendTarget where
  | selfTarget
  | knownRebec : KnownRebecName → GeneralSendTarget

inductive GeneralStmt where
  | assign : VarName → DTR.GeneralExpr → GeneralStmt
  | send   : DTR.GeneralSendTarget → MsgName → List DTR.GeneralExpr → Delay → GeneralStmt
```

Three decisions worth naming.

`variable` in the JSON is resolved by the elaborator into `stateVar` or `parameterVar` using
the enclosing scope, rather than carried through as one node. The exporter already resolves
scope and rejects undeclared names, so the elaborator is re-deriving a fact rather than
inventing one — and keeping the two-constructor split means the existing translation idiom
transfers unchanged.

`send` is **one** constructor with a target sum, mirroring the JSON's unified `"kind":
"send"`. A self-send is `send .selfTarget`. This is a change of posture from
`MultiStorePayloadStmt.selfSend`, and it is what makes `selfSendNotExternal` (an existing
`Failure` constructor) meaningful on a real traversal instead of on a hand-built record.

Statement bodies stay `List GeneralStmt` — flat, no nesting — precisely because control flow
is out of scope. Stage H changes this type, and that is the point (§5).

Classes, instances, model:

```lean
structure GeneralKnownRebecDecl where
  className   : ClassName
  name        : KnownRebecName

structure GeneralConstructor where
  parameters : List DTR.TypedParameter
  body       : List DTR.GeneralStmt

structure GeneralMessageServer where
  name       : MsgName
  parameters : List DTR.TypedParameter
  body       : List DTR.GeneralStmt
  priority   : Option Nat := none

structure GeneralReactiveClass where
  name           : ClassName
  knownRebecs    : List DTR.GeneralKnownRebecDecl
  stateVariables : List DTR.TypedStateVariableDecl
  constructor    : DTR.GeneralConstructor
  messageServers : List DTR.GeneralMessageServer

structure GeneralActorInstance where
  name      : ActorName
  className : ClassName
  bindings  : KnownRebecBindings        -- reused from Common/ActorTopology.lean
  arguments : List DTR.GeneralValue
  priority  : Option Nat := none

structure GeneralModel where
  classes   : List DTR.GeneralReactiveClass
  instances : List DTR.GeneralActorInstance
```

`bindings : KnownRebecBindings` is the fix for B-1: the topology is now *decoded*, and
`ActorTopology.resolve` can succeed. `GeneralModel.topology : ActorTopology` is derived as
a definition from `instances` rather than stored, so the two can never disagree — which
removes the `actorsMatchKeysAndClasses` class of well-formedness obligation by construction
instead of by check.

`TypedParameter` and `TypedStateVariableDecl` are new (name plus `int`/`boolean` type),
because `general-v1` reports declared types and a boolean-carrying AST needs them for
arity-and-type checking. The existing untyped `StateVariableDecl` stays where it is.


## 5. Well-formedness: the eight, plus the tie rule

`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md:314-336` already states the mandate, and
states it in the direction that is easy to get backwards: being enforced upstream makes a
restriction *less* covered downstream, not more, because there is no Rebeca parser and no
typechecker anywhere upstream of a Lean decoder. The eight are listed at line 323. Stage B
discharges them, but **not all eight are checks** — and the split matters, because a
restriction made unrepresentable is stronger than one that is tested.

Unrepresentable by construction, no clause needed:

- *an initialized state variable* — `TypedStateVariableDecl` has a name and a type and no
  initializer field, so the bad term does not typecheck.
- *a known rebec used as a value (A1)* — `GeneralExpr` has no constructor mentioning
  `KnownRebecName`. A known rebec can appear only as a `GeneralSendTarget`.

Falling out of scope resolution, provided the elaborator's scope is *exactly*
`stateVariables ∪ parameters` with no implicit names:

- *a read of the implicit `sender` (A4)* — `sender` resolves against nothing and yields
  `Diagnostic.unresolvedName`.
- *a send to the implicit `sender` (A4)* — `sender` is not in `knownRebecs` and yields
  `Diagnostic.undeclaredSendTarget`.

I am naming this because the coverage is conditional on a negative: the moment the
elaborator's scope gains implicit names, two of the eight silently stop being enforced. The
exporter has the analogous exposure and it is already visible there — `now`,
`currentMessageArrival`, `currentMessageDeadline` and `currentMessageWaitingTime` are
injected upstream into every message server's scope, and the exporter rejects three of them
as *undeclared* rather than as reserved. The Lean layer has no equivalent of those names,
so nothing is owed, but the mechanism is the same one and it should be documented at the
scope function rather than discovered later.

Real clauses, four of them, and the last is the deepest:

- `bindingsMatchDeclarations` — each instance's `bindings` has one entry per
  `knownRebecs` entry of its class, names agree, and each bound actor's class equals the
  declared class of that known rebec. This is the arity restriction, plus the class
  agreement the arity check alone would miss.
- `argumentsMatchConstructor` — each instance's `arguments` has the arity of its class's
  constructor parameters, and each literal's type matches the declared parameter type.
  This is the D8 check.
- `sendTargetsDeclared` — every `send .knownRebec r` inside class `C` has `r` in `C`'s
  `knownRebecs`. This is D6, and it is the restriction that makes a message server's sender
  set statically computable, so it is load-bearing for stages E–F rather than hygienic.
- `sendsResolveToMessageServers` — for every `send` in every body: resolve the target to a
  class (`self` to the enclosing class, `knownRebec r` to the declared class of `r`), then
  that class must declare a message server of that name, with matching parameter arity and
  matching parameter types. This is the one check that cannot be done class-locally, and it
  is only possible *because* B-1 is fixed — with empty bindings there is no receiving class
  to look at.

Then the two priority clauses, and here a measurement changed my view of what stage B is
doing. `PrioritiesDistinct` is **defined, tested, and never enforced**. Grepping
`PrioritiesDistinct|prioritiesDistinct` across every `.lean` file returns seven hits: its
own definition and `Decidable` instance in `MultiStorePayloadSyntax.lean`, one doc-comment
mention, and two examples in `Relico/Tests/MultiStorePayloadFoundation.lean` (one positive,
one negated). No decoder, no `wellFormed`, and no translation calls it.

That is not an oversight, and the source says so itself, at
`Relico/DTR/MultiStorePayloadPriority.lean:9-16`:

> Smaller explicit numbers have higher priority. Every explicit priority precedes `none`.
> Equal priorities are still representable in the raw AST, but Option-C correctness theorems
> will require `MultiStorePayloadMessageServers.PrioritiesDistinct`.

So two things are already settled by the repository and should not be re-litigated. `none`
is the **lowest** priority class, not an absence of ordering — `PrecedesOrEqual` is total,
with `some _` before `none` and `none` tying with `none`. And distinctness was deliberately
deferred to a later theorem set. Stage B is where it comes due, which is exactly what issue
#50 says.

The consequence is that `PrecedesOrEqual` is a total *preorder*, and it becomes a strict
total order — that is, selection becomes deterministic — precisely when the priority list is
`Nodup` over `Option Nat`. Distinctness and absence are therefore not two rules but one:
`Nodup` forbids repeated numbers *and* forbids a second unannotated member, because `none`
is itself a class. That single predicate is what the tie rule of #50 and the settled
"absent priority means reject" decision both reduce to. The remaining question is which
levels it applies to, and that is §9, because the answer decides whether five of the nine
stage-A positives elaborate.

Deliberately **not** stage B, recorded here so they are not silently lost:

- **R23, the single-port assumption** (at most one identical message from one sender to one
  receiver at one logical time) is a condition on a *state*, not on syntax. It is already
  represented as `duplicateSameEdgeTime` in the external-send `Failure` inductive, which is
  the right place. Stage B does not restate it.
- **R24, overflow-freedom** is a hypothesis on an execution and belongs to whichever stage
  states the bisimulation. The paper never discharges it either — it is the sole occurrence
  of "overflow" in the paper and is never related to the queue bound of R7.

Idiom: mirror what is already there rather than invent. `Prop` plus a hand-written
`Decidable` instance for the distinctness clauses, exactly as `PrioritiesDistinct` /
`prioritiesDistinctDecidable` do it; `Bool` for the four structural clauses, exactly as
`ActorTopology.wellFormed` and `GlobalMultiStorePayloadModel.wellFormed` do it; one
`GeneralModel.wellFormed : Bool` conjoining them; and a per-clause extraction lemma
(`wellFormed model = true → bindingsMatchDeclarations model = true`, four of them, each by
`simp`) so downstream stages consume a single clause instead of destructuring a conjunction.
No monolithic `wellFormed ↔ …` theorem — it buys nothing and costs a large proof.


## 6. The enabling condition, and a proof that it discriminates

This is the fix for B-3 and for soundness defect 1. Stage B adds the minimum state
representation needed to *compute* readiness, and stops there — no step relation, no
execution. Defining a step relation is what stage D onward needs, and bundling it here would
make stage B unreviewable.

```lean
structure GeneralMessage where
  sender      : ActorName
  messageName : MsgName
  payload     : DTR.GeneralPayload
  arrival     : Nat

structure GeneralActorState where
  valuation : Store VarName DTR.GeneralValue
  queue     : List DTR.GeneralMessage

structure GeneralConfiguration where
  now    : Nat
  actors : Store ActorName DTR.GeneralActorState
```

and then the function that does not currently exist anywhere in the repository:

```lean
def dueArrival (state : DTR.GeneralActorState) (now : Nat) : Option Nat :=
  (state.queue.filter (fun message => message.arrival ≤ now)).map (·.arrival) |>.min?

def readyActors (config : DTR.GeneralConfiguration) : List ReadyActor
```

walking `config.actors` in declaration order and emitting one `ReadyActor` per actor whose
`dueArrival` is `some`. Declaration order is not arbitrary — it is the order the exporter
emits and the order the LF-semantics probe measured to decide same-tag reaction order, so
keeping it is what lets stage G compare a DTR cohort against an LF reaction sequence.

Three lemmas, and the third is the one that earns the stage:

- **soundness** — every `a ∈ readyActors config` has an actor state in `config.actors` and a
  message in its queue with `arrival = a.time ≤ config.now`. No invented cohort members.
- **completeness** — if an actor's queue holds a message with `arrival ≤ config.now`, that
  actor appears in `readyActors config`. No omitted cohort members.
- **discrimination** — exhibit a concrete `model`, `config` and cohort `c` such that
  `simultaneouslyReady c` holds while `c ≠ readyActors config`. This is provable by `decide`
  on small closed terms, and it is the point: it demonstrates that the existing `ReadyActor`
  index admits cohorts the state contradicts, which is precisely defect 1. A stage that only
  proved soundness and completeness would be consistent with `readyActors` being vacuous.

The paper offers no help and should not be cited here. Priority appears in **neither** SOS
table, and `enabled_m` / `enabled_tr` are never defined anywhere in it. So this is a place
where the repository is strictly more specified than the paper, which under the standing
mandate makes it a ledger entry in `docs/PAPER_CORRECTIONS.md` rather than a silent
improvement. Number assigned when written; the existing entries already run past P9, since
the fragment doc cross-references P11 and reserves P15 for D9.


## 7. What stage B excludes, and why exclusion is the safe direction

Control flow — `if`, `for`, and the `for`-initializer declaration of D7 — is read faithfully
by the reader and rejected by the elaborator with `Diagnostic.controlFlowUnsupported`,
`Diagnostic.loopUnsupported` and `Diagnostic.localDeclarationUnsupported`.

The reason is asymmetry in how Lean fails. Adding a constructor to an inductive breaks every
exhaustive `match` on it, so when stage H adds `GeneralStmt.ifThenElse`, the compiler
enumerates every function that must now consider a branching body — the elaborator, the
translation, the semantics, each printer. Whereas if stage B admitted control flow with a
placeholder or a catch-all, stage H would consist of finding the places where a default
branch silently did the wrong thing. The first mode is a build error; the second is a
soundness bug. So statement bodies stay `List GeneralStmt`, flat, and stage H changes the
type on purpose.

The same argument is why `GeneralExpr` has no `ternary`, no cast, no call, and no
nondeterministic choice: all four are already rejected by the exporter under D5, and the
Lean AST should not be able to represent what the fragment excludes.

The cost is visible and must be recorded rather than hidden: `control-flow` is a `general-v1`
**positive** that stage B rejects. It stays a positive at the Java layer, where it belongs,
and gains a per-fixture expectation at the Lean layer. That is the same layer-pinning
discipline stage A established — a negative must assert *which* layer rejected it — applied
one layer down.

### Expected outcome per stage-A positive

Measured. Message-server column is per class; actor column is the main block. `Nodup?` is
over `Option Nat` with `none` counting as a class.

| fixture | msgsrv priorities | msgsrv Nodup? | instance priorities | actor Nodup? | stage B outcome |
|---|---|---|---|---|---|
| `minimal-class` | `Inert` — none at all | yes (empty) | 1 × none | yes | elaborates |
| `keep-alive` | `Ticker` [none] | yes | 1 × none | yes | elaborates |
| `priorities` | `Arbiter` [1, 2, none] | yes | [3, none] | yes | elaborates |
| `fan-in` | `Sensor` [none], `Gateway` [none] | yes | [1, 2, 3, none] | yes | elaborates |
| `two-instances` | `Worker` [none], `Collector` [none] | yes | [none, none, none] | **no** | actor tie |
| `two-classes` | `Producer` [none], `Consumer` [1] | yes | [none, none] | **no** | actor tie |
| `constructor-arguments` | `Configured` [none] | yes | [none, none] | **no** | actor tie |
| `expressions` | `Calculator` [none, none, none] | **no** | 1 × none | yes | msgsrv tie |
| `control-flow` | `Looper` [none, none] | **no** | 1 × none | yes | control flow **and** msgsrv tie |

So under the faithful reading, four elaborate and five do not: three fail the actor clause,
one fails the message-server clause, and `control-flow` fails both that and §7.

This is worth pausing on, because it is not a fixture problem. It says that **any Rebeca
class with two or more unannotated message servers is outside the fragment**, and that is
most Rebeca code. The upstream census is consistent: 19 of 49 models use actor priority, so
30 do not, and message-server annotation was never separately measured. Whatever is decided
in §9 propagates to stage G's benchmark corpus and to every model derived from upstream.


## 8. Files, obligations, and the gate

Eleven new Lean modules, one new script, one edited root. Nothing existing is modified apart
from `Relico.lean`, which is what makes the gate cheap.

```
Relico/DTR/GeneralSyntax.lean          AST of §4
Relico/DTR/GeneralWellFormed.lean      four Bool clauses, PrioritiesDistinct, wellFormed, extraction lemmas
Relico/DTR/GeneralState.lean           GeneralMessage / GeneralActorState / GeneralConfiguration / readyActors
Relico/Frontend/GeneralSchema.lean     Raw* mirroring general-v1 exactly, including what stage B rejects
Relico/Frontend/GeneralDiagnostic.lean Diagnostic inductive + renderer
Relico/Frontend/GeneralElaborator.lean Raw → Except Diagnostic GeneralModel
Relico/Frontend/GeneralDecoder.lean    text → Except String GeneralModel
Relico/Frontend/GeneralBridgeCheck.lean executable entry point
Relico/Tests/GeneralElaborator.lean    one inlined negative per Diagnostic constructor
Relico/Tests/GeneralWellFormed.lean    positive and negated example per clause
Relico/Tests/GeneralReady.lean         the three lemmas of §6
frontend/check-general-lean.sh         the new gate loop
```

`GeneralBridgeCheck.lean` stays **out** of the default build closure, matching its three
siblings — the measured non-closure set is `Relico/Benchmark/*` ×3 and
`Relico/Frontend/*BridgeCheck*` ×3. Everything else is imported from `Relico.lean` so
`lake build` covers it.

The positive/negative split for tests is deliberate. Positives run from the **real** committed
`.parser.json` files through the bridge-check executable, so the corpus is never duplicated
and can never drift from stage A. Negatives are small inlined JSON strings inside
`Relico/Tests/`, so they are checked by `lake build` itself and each one names the diagnostic
it expects. That last part is the stage-A discipline applied one layer down: a negative test
must assert *which* rule rejected the input, not merely that something did. This is also how
#50 is discharged — the contention and tie negatives live here, in Lean, not in the exporter,
which implements no contention rule at all.

Note that the Java `reject/` and `upstream-reject/` corpora **cannot** be reused here: both
are rejected before any JSON exists, so there is nothing for a Lean decoder to read. Stage B
needs its own negative corpus at the JSON level, and that corpus is the only evidence the
four structural clauses have teeth.

Gate, in the standing order, every step separate:

1. Sandbox: `check-general-lean.sh` against a stub, to prove each new branch can fail.
2. Mac: cold `lake build` **from a fresh clone**, not the working tree. Stage A's lesson —
   a gate that quietly depends on an uncommitted file or a stale `.lake/` artifact passes
   locally and fails for everyone else.
3. Mac: `check-general.sh` still 9/11/8, byte-identical.
4. Mac: `check-general-lean.sh` green, with the per-fixture expectations of §7.
5. Registry: regenerate `obligations.tsv` and bump the validator constants **in the same
   commit** — module count and obligation count move together or `REGISTRY_VALID` fails.
6. Then commit; then push; then verify the remote from a fresh clone.

Two known hazards, both already paid for once. Lake hashes file contents, so a touch-test
proves nothing — verify a rebuild by deleting oleans and counting jobs (closure + 2). And
`obligations.tsv` extraction does **no comment stripping** and matches on line-prefix
keywords, so a doc comment whose line begins with `theorem`, `def`, `lemma` or `example`
silently invents an obligation. This design is doc-comment heavy, so the prose in the new
modules must not start a line with a registry keyword.

## 9. The one decision I need

Everything above I can justify from measurement. This I cannot, because it changes what the
project admits, and because it touches a decision already settled at a different scope.

The settled decision is that **absent `@priority` means reject**, and that the alternative
— detecting whether priorities would change the observable behaviour — is off the table.
I read that decision as governing *benchmark admission*. It has never been applied to a Lean
predicate, because until stage B there was no Lean predicate to apply it to. Under the memory
system's own rule I must not extrapolate a decision's scope, so here are the three readings
with their measured cost.

**A — admission gate at both levels.** `wellFormed` conjoins message-server and actor
distinctness. Four of the nine positives elaborate; five are rejected. Remedy is to add
`@priority` to those five, which is already approved practice (decision #34, rewrite
rejected models with priorities). Cost: five `.rebeca` edits plus five `.parser.json`
regenerations on the Mac, and thereafter near-total priority annotation in every model the
project writes or imports.

**D — theorem-level hypothesis, which is what I recommend.** Define both distinctness
predicates in stage B, test them, and expose them as named conditions — but conjoin only the
four *structural* clauses into `wellFormed`. Correctness theorems from stage F onward take
distinctness as an explicit hypothesis. This is precisely what the repository already says it
intends: *"Equal priorities are still representable in the raw AST, but Option-C correctness
theorems will require PrioritiesDistinct."* All nine positives elaborate except
`control-flow`, which is rejected for control flow alone. No fixture churn. The predicate
stops being defined-but-never-applied at the moment a theorem consumes it, which is the only
form of "applied" that matters. Benchmark admission still enforces the settled rule, so
nothing is weakened where it was decided.

**C — defer entirely.** No distinctness predicate in stage B at all; revisit at stage G.
Eight of nine elaborate. Cheapest now, and it leaves stage G to discover which models it
cannot use, which is the failure mode this whole pivot exists to avoid.

I recommend **D**. It is the reading that matches the repository's stated intent, keeps
stage A's corpus untouched, and still ends with a rejection — just located at the theorem
that needs the hypothesis rather than at the front door.

### DECIDED 2026-08-18: **D**, theorem-level hypothesis

Approved. Consequences, which are now binding on stage B and on every later stage:

- `GeneralModel.wellFormed : Bool` conjoins **only** the four structural clauses of §5. It
  does **not** mention priority.
- `MessageServerPrioritiesDistinct` and `ActorPrioritiesDistinct` are defined in
  `Relico/DTR/GeneralWellFormed.lean` as `Prop` with hand-written `Decidable` instances,
  mirroring `PrioritiesDistinct` / `prioritiesDistinctDecidable` exactly, and each gets a
  positive and a negated example in `Relico/Tests/GeneralWellFormed.lean`.
- Every stage-F/G correctness theorem carries them as explicit hypotheses. A theorem that
  needs determinism and does not name them is a bug in that theorem.
- All nine stage-A positives elaborate except `control-flow`, which is rejected for control
  flow alone (§7). **No fixture is edited and no `.parser.json` is regenerated.**
- The settled "absent `@priority` means reject" rule keeps its original scope: benchmark
  admission. It is not an elaboration gate.
- The three actor-tie and two message-server-tie fixtures identified in §7's table are
  therefore *elaborable but not theorem-eligible*. That distinction has to be legible, so
  §7's table graduates into the tracked docs alongside this file rather than living only here.


