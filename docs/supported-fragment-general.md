# The General Family's Accepted Fragment

> **Status.** This is the authoritative declaration of what the general family's translator accepts,
> landed 2026-08-27 as G6 document 1 (`docs/STAGE_G_DESIGN.md` §11 item 1; audit item C9 in
> `RELICO_FORWARD_ROADMAP_AUDIT.md` §C). It exists because three sites quantify the project's claim
> over "the supported fragment" — `README.md`'s opening line, and `docs/trusted-boundary.md`'s
> verified-boundary and intended-claim sections — and until now the only document declaring a
> fragment was [`supported-fragment.md`](supported-fragment.md), which declares vertical slice v0 and
> is a historical record. That misresolution is finding **F63**; this document is its repair, first
> half. The second half — the theorem-eligibility table, naming what elaborates but is excluded from
> which theorems — landed 2026-08-28 as this document's final section, G6 document 2 (audit item
> C10).

## How to read this document

Every inclusion and exclusion below is derived from an **executable predicate**, named by its Lean
declaration — not from prose about what some stage intended. The precedence rule is one sentence:
where this document and a predicate disagree, the predicate wins and this document is defective.
The predicates, in the order a model meets them:

1. the frontend's refusal vocabulary, `Relico/Frontend/GeneralDiagnostic.lean`'s
   `GeneralDiagnosticReason`, applied while a JSON document becomes a model;
2. the source predicate `DTR.GeneralModel.wellFormed`, five clauses, in
   `Relico/DTR/GeneralWellFormed.lean`;
3. the translation guard `Translation.guardGeneralProgram`, which decides on
   `LF.GeneralProgram.wellFormed` — ten clauses — over the translator's own output.

A model is **accepted** when all three pass. Everything else is refused with a diagnostic, or — for
the two priority-distinctness predicates of §3 — accepted but not eligible for every theorem.

## The source surface

What a model **is**: `DTR.GeneralModel`, a list of `DTR.GeneralReactiveClass` declarations and a list
of `DTR.GeneralActorInstance` declarations. The topology is not a field; it is derived from the
instances, so a model cannot carry a topology that disagrees with the instances it describes.

A **reactive class** declares known rebecs (name plus class name), state variables (name plus type —
`int` or `boolean` are the only types the frontend admits), one constructor (typed formal parameters
plus a body), and message servers (name, typed formal parameters, body, optional `Nat` priority). A
class may declare no known rebecs, no state variables and no message servers; all three are needed
for the paper's own figures.

An **actor instance** declares a name, a class name, a known-rebec binding store (known-rebec name to
actor name), positional constructor arguments, and an optional priority. Arguments are literals —
integer or boolean — because the frontend refuses anything else (`nonLiteralInstanceArgument`).

**Expressions** (`DTR.GeneralExpr`): integer and boolean literals, state-variable reads,
parameter reads, thirteen binary operators (`add`, `sub`, `mul`, `div`, `mod`, `eq`, `ne`, `lt`,
`le`, `gt`, `ge`, `logicalAnd`, `logicalOr`) and two unary operators (`negate`, `logicalNot`). Two
absences are deliberate and load-bearing. There is no constructor mentioning `KnownRebecName`, which
makes "a known rebec used as a value" unrepresentable rather than merely checked. And there is no
typing judgement anywhere in this family: the upstream Timed Rebeca typechecker rejects ill-typed
expressions before a document is emitted, so typing is upstream's obligation, not a restriction this
fragment declares.

**Statements** (`DTR.GeneralStmt`), three constructors:

- `assign` — target state variable, expression;
- `trace` — a literal tag, the G5 observability instrument (§7);
- `send` — target (`self` or a declared known rebec), message-server name, payload expressions,
  delay.

**Delays** are `Delay`, a bare `Nat` — nonnegative by construction. Constantness (a literal, not an
expression) is a frontend refusal (`nonConstantDelay`), not an AST property, because the frontend is
where an `after` field is read.

## Source well-formedness: five clauses, priority absent by design

`DTR.GeneralModel.wellFormed` is the conjunction of exactly five clauses — **five**, not the four the
approved stage-B design named; the fifth was added when repeated names were measured as making a
model mean something the frontend did not say (recorded in `docs/STAGE_B_FINDINGS.md`):

1. `bindingsMatchDeclarations` — every instance's bindings name known rebecs its class declares;
2. `argumentsMatchConstructor` — every instance's arguments match the arity and types of its class's
   constructor formals;
3. `sendTargetsDeclared` — every send's target, when it is a known rebec, is declared by the sending
   class;
4. `sendsResolveToMessageServers` — every send names a message server the receiving class declares,
   with matching payload arity;
5. `namesUniqueAndValid` — topology keys unique; class names duplicate-free; class, instance and
   known-rebec names non-empty; known-rebec and message-server names duplicate-free per class.

Parameter and state-variable name uniqueness is deliberately **not** here — it is the elaborator's
concern, reported as a frontend diagnostic (`duplicateStateVariable`, `duplicateParameter`,
`parameterShadowsStateVariable`, `emptyName`).

**Priority is absent by decision.** Distinctness of priorities is a *hypothesis* of those correctness
theorems that need deterministic selection — `DTR.MessageServerPrioritiesDistinct` and
`DTR.ActorPrioritiesDistinct` — not a condition on being decodable at all. A model whose priorities
tie elaborates, translates and runs; which theorems it is eligible for is the question of the
theorem-eligibility table below.

## The frontend gate

`GeneralDiagnosticReason` is the refusal vocabulary, and it is part of the fragment declaration
because a construct the schema reads but the diagnostics refuse is *in the JSON grammar and out of
the fragment*. The refusals that bound the fragment, beyond the name and arity checks mirrored in
§3–§5:

- **Types**: `unknownDeclaredType` — `int` and `boolean` only.
- **Expressions**: `unsupportedExpressionKind`, `missingField`, literal-type checks, and the
  operator-count refusals `unknownBinaryOperator` / `unknownUnaryOperator` — thirteen and two,
  exactly the constructors of §2.
- **Statements**: `branchingNotSupported` (`if`), `iterationNotSupported` (`for`),
  `localDeclarationNotSupported` (`declare`) — read faithfully by the schema, admitted by no stage
  before H; `assignmentTargetNotStateVariable` — a write to a formal parameter has no state-semantics
  home; `nonConstantDelay` and `negativeDelay`.
- **Instances**: `nonLiteralInstanceArgument`.

## The translation guard: ten clauses on the target

`Translation.guardGeneralProgram` decides on `LF.GeneralProgram.wellFormed` — **ten** conjuncts, the
tenth added by G3 — and refuses the translation when any is false:

`reactorsNonEmpty`, `instancesNonEmpty`, `reactorsWellFormed`, `reactorNamesUnique`,
`instanceNamesUnique`, `instancesResolve`, `instanceArgumentsMatch`, `connectionsWellFormed`,
`targetEndpointsUnique`, `reactionPrioritiesAbsent`.

Two clauses deserve note here. `targetEndpointsUnique`: two connections may not target one input
port — `lfc` rejects many-to-one connections, so the guard refuses the source model rather than
emitting a program the target would reject. And `reactionPrioritiesAbsent`: no reaction carries an
LF `priority` attribute, because `lfc` rejects the attribute outright; precedence between one
reactor's reactions is carried by **declaration order**, which is the only realizable mechanism and
is what stages F and G order. This tenth clause is also the only one of the ten that refuses for
something the target cannot express rather than for an internal inconsistency — the distinction its
own docstring draws.

A refusal from this guard is a **translator defect, not a document defect**: the frontend has
already certified the model, so a model that reaches this point and is refused means the naming
rules collided or a projection is wrong. The refusal text comes from a mirror list
(`generalProgramClauses`) used for prose only; the decision itself is always on the predicate.

## The generated target subset

One LF reactor per class (named for the class), one instance per actor (named for the actor), one
connection per route with an explicit `after` delay. Per reactor: a state declaration per source
state variable with the type's initial value; a startup reaction compiled from the constructor; per
message server, one logical action and reaction per self-send site, plus one port reaction per route
into the server — per-site, because two sends of one message from one body at one tag must not
collapse (F56). Constructor formals become reactor parameters and the instance's arguments become
its parameter values. The printer emits C++ verbatim in `{= … =}` blocks, and includes `<cstdio>`
exactly when some body contains a `trace`.

## `trace`: in the syntax, τ in the semantics, no frontend spelling

`trace` is a statement constructor on both ASTs with **Option A** semantics: a τ-classified step on
both sides that consumes the statement and changes no modelled state. It exists to make behaviour
observable in generated output — the G5 witness (`priorityWitnessModel`) uses it, and the target
gate asserts on the observed order under `GENERAL_LF_PRIORITY_WITNESS_OK`.

Two boundaries it does not cross. The frontend has **no spelling** for it: nothing in
`Relico/Frontend/` reads a `trace` node, so a trace-carrying program can only be hand-built in Lean —
it is a witness instrument, not a source-language feature. And the bytes a generated program prints
are **target-runtime evidence outside the formal observable alphabet**: `GeneralLabel` does not
contain them, and no theorem quantifies over stdout.

## What this fragment excludes, and why

**By design, not by schedule.** Arbitrary LF programs. The LF subset is *generated* and never
parsed; a correctness theorem over it could only ever be a theorem about the translator's own
output. This is not a milestone exclusion and no later stage discharges it.

**Target-limited, with a guard still owed.** Division and modulo by zero. A literal zero divisor
(`.binary .div _ (.intLiteral 0)` and its `mod` counterpart) is syntactically visible and **should be
refused**; that guard is finding **F67** part 4's decidable half and is still open. The undecidable
residue — a divisor that is zero only on some execution — cannot be refused by any analysis here, so
it is declared as a restriction on transfer: the correctness result transfers to real target
behaviour only on executions in which no division or modulo by zero occurs. On the model sides such
a statement is stuck on both sides consistently; in generated C++ it is undefined behaviour, and the
theorem does not claim otherwise.

**Refused at the frontend, owed to later stages.** Conditionals, iteration, local declarations —
stage H's work, each with its refusal reason already in the vocabulary.

**Still excluded, no stage owner.** Arrays, inheritance, physical actions, environmental inputs,
broadcast. None is refused by name — they simply have no constructor in the AST — so they are
excluded by unrepresentability rather than by diagnostic.

## The theorem-eligibility table

> **G6 document 2**, landed 2026-08-28 (audit item C10). The binding 2026-08-18 decision
> (`docs/STAGE_B_DESIGN.md`, option **D**) put the two priority-distinctness predicates *outside*
> `wellFormed` and *inside* the theorems that need them, and its operative sentence is the rule this
> section operationalizes: *"A theorem that needs determinism and does not name them is a bug in that
> theorem."* The same decision required that the boundary between elaborable and theorem-eligible
> "has to be legible"; until now it lived only in the hypotheses of the theorems themselves. This is
> that table. The precedence rule of this document applies to it unchanged: where a row below and a
> theorem's actual signature disagree, the theorem wins and this table is defective.

### The rule, stated once

Elaboration and eligibility are **different predicates**, on purpose. A tie-carrying model is
accepted by the translator like any other, and remains eligible for every theorem whose statement
does not name a distinctness guard — translation preservation, the initial correspondence, Lemma 1.
What it loses is exactly the theorems that claim a *unique* selection or a *strict* order, because
those are false without distinctness and the paper supplies no tie rule (P4, F27). One consequence
worth stating because the decision's own prose blurs it: not every stage-F/G theorem carries the
guards — only the determinism-needing ones do, which is what the operative sentence says and what
the landed corpus does.

### The five tie fixtures, by name

The five fixtures of the committed corpus that elaborate and fail a distinctness guard, measured
2026-08-28 against `frontend/fixtures/general/`:

| fixture | instance priorities | per-class server priorities | fails |
|---|---|---|---|
| `two-instances` | none, none, none | — (all single) | `ActorPrioritiesDistinct` |
| `two-classes` | none, none | — (all single) | `ActorPrioritiesDistinct` |
| `constructor-arguments` | none, none | — (single) | `ActorPrioritiesDistinct` |
| `send-sites` | none, none | — (single) | `ActorPrioritiesDistinct` |
| `expressions` | none (single actor) | none, none, none | `MessageServerPrioritiesDistinct` |

Two notes the count alone cannot carry. First, **`control-flow` is not one of the five**: it carries
a message-server tie, but it is refused for control flow before eligibility is ever reached, so it
is not elaborable at all. Second, **the stage-B decision's count has drifted**: it named "three
actor-tie and two message-server-tie" fixtures, which described the nine-fixture corpus of that
date. Stage E added `send-sites` — a fourth actor tie — and `control-flow`, one of the decision's
two message-server ties, never elaborated. The names above, not the number five, are the durable
record.

The other four elaborable fixtures — `minimal-class`, `keep-alive`, `priorities`, `fan-in` — satisfy
both guards and are eligible for everything below.

### Theorem families and their hypotheses

Grouped by module; each row's "hypotheses" column lists everything beyond successful compilation
(or, for state-level theorems, beyond the state relation the statement already names).

| family | module | hypotheses | tie models |
|---|---|---|---|
| translation preservation (`compileGeneralModel_wellFormed`, `guardGeneralProgram_wellFormed`, the structural field lemmas) | `Relico/Translation/GeneralBasic.lean` | none | eligible |
| unconditional initial correspondence (`generalCorrespondence_initial`) | `Relico/Correctness/GeneralCorrespondence.lean` | none — successful compilation only | eligible |
| Lemma 1 (`generalTimeEquivalence_forward`, `_backward`, combined) | `Relico/Correctness/GeneralTimeEquivalence.lean` | run-state facts (quiescence, correspondence) — state facts, not model-class restrictions | eligible |
| selection, non-claiming (`selectMinimum_mem`, `selectedActor_isSome_iff`, `selectedActor_mem`, `selectedActor_minimal`, `selectedActor_ne_fabricated`) | `Relico/DTR/GeneralActorSelection.lean` | none — but `selectedActor_minimal` is non-strict and cannot see ties | eligible |
| selection uniqueness (`selectedActor_unique`) | `Relico/DTR/GeneralActorSelection.lean` | `model.actorPriorities.Nodup` (the raw spelling; the named predicate unfolds to it) | **excluded** |
| level-1 order, non-strict (`walkedInstances_precedes_of_split`) | `Relico/Correctness/GeneralPriorityOrder.lean` | none — cannot see ties | eligible |
| level-1 strict order (`walkedInstances_strict_of_split`, `portReactions_realizeActorPriority`) | `Relico/Correctness/GeneralPriorityOrder.lean` | `ActorPrioritiesDistinct` | **excluded** |
| level-2 order, non-strict (`walkedMessageServers_precedes_of_split`) | `Relico/Correctness/GeneralPriorityOrder.lean` | none | eligible |
| level-2 strict order (`walkedMessageServers_strict_of_split`, `messageServerReactions_realizeMessageServerPriority`) | `Relico/Correctness/GeneralPriorityOrder.lean` | `MessageServerPrioritiesDistinct` | **excluded** |
| τ-advance correspondence (`generalCorrespondence_retag`, `generalCorrespondence_microstepAdvance`, the trace-tail lemmas) | `Relico/Correctness/GeneralCorrespondence.lean` | the state relation | eligible |
| single-step advance (`generalCorrespondence_advance`) and quiescence (`generalQuiescent_of_earliestPendingEventFuture`) | `Relico/Correctness/GeneralWeakBisimulation.lean` | the state relation | eligible |
| weak transfer, `.timeAdvance` halves (`generalTimeAdvance_forward_weak`, `_backward_weak`) | `Relico/Correctness/GeneralWeakBisimulation.lean` | the state relation | eligible |

Two further rows belong to the table but have no theorem to name, and they are the table's most
important content:

* **The `.consume` transfer halves do not exist.** `generalTimeAdvance_forward_weak` and
  `_backward_weak` cover one label constructor of two; the `.consume` case is task `#129`, blocked on
  the F76 repair decision (a user decision; audit item C6). The consequence, per **F83**: the
  generic finite-trace agreement of row 9 (`weakBisimulation_traceAgreement_forward`/`_backward`)
  quantifies over *both* transfer conditions, so the general family cannot instantiate it — aims 8
  and 9 of `docs/trusted-boundary.md` are proved over an abstract LTS and **not yet for the general
  family**. No model, tie-carrying or not, is eligible for a theorem that does not exist.
* **Division and modulo by zero carry a transfer restriction.** The model-side correspondence holds
  unconditionally — `compileGeneralExpr_preserves_evaluation` and
  `compileGeneralExpr_evaluation_none_iff` make both sides stuck together — but generated C++ has
  undefined behaviour there, so the result transfers to real target behaviour only on executions in
  which no division or modulo by zero occurs (**F67** part 4). The decidable half — refusing a
  literal zero divisor — is still owed (audit item C11); the undecidable residue is a permanent
  restriction on transfer, not a pending task.

### `trace` eligibility, in one paragraph

The `trace` statement is theorem-eligible inside the formal semantics — it has a τ-classified step
on both sides (Option A), and `generalContinuationCompiles_trace_tail` /
`generalActorCorresponds_trace_tail` prove its correspondence — but the bytes a generated program
prints are **not** an observable of the theorem boundary: `GeneralLabel` does not contain them, no
theorem quantifies over stdout, and the G5 witness's observed output order is target-runtime
evidence owned by the gate, not by the semantics. A model is no more or less eligible for carrying a
`trace` than for carrying an `assign`.

## Relation to the earlier families

The singleton (v0), finite-store, multi-store, multi-store-payload and global-multi-store-payload
families remain in-tree, each with its own modules, theorems and — for the schema ones — bridge
paths. They are compatibility and regression surfaces, not part of this declaration: a claim true of
one family is not a claim about another. The singleton schema-version-1 path remains available for
regression. When this document and an earlier family's design disagree about "the supported
fragment", this document is the one the current toolchain answers to.

## Maintenance

This declaration moves with the predicates. A commit that adds, removes or changes the meaning of a
clause of `DTR.GeneralModel.wellFormed` or `LF.GeneralProgram.wellFormed`, a constructor of the
syntax types, or a reason in `GeneralDiagnosticReason`, changes this document in the same commit —
including the counts, which are the parts most likely to go stale silently. The theorem-eligibility
table carries the same obligation for its rows: a commit that adds a guard hypothesis to a theorem,
lands a previously missing transfer half, or changes the fixture corpus's tie census moves the table
in the same commit. The tie census in particular is coupled to the fixture directory, not to this
file — `send-sites` added a tie row that no edit here caused, and the next fixture addition can do
the same again.
