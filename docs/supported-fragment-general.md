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
declaration, not from prose about what some stage intended. The precedence rule is one sentence:
where this document and a predicate disagree, the predicate wins and this document is defective.
The predicates, in the order a model meets them:

1. the frontend's refusal vocabulary, `Relico/Frontend/GeneralDiagnostic.lean`'s
   `GeneralDiagnosticReason`, applied while a JSON document becomes a model;
2. the source predicate `DTR.GeneralModel.wellFormed`, five clauses, in
   `Relico/DTR/GeneralWellFormed.lean`;
3. the translation guard `Translation.guardGeneralProgram`, which decides on
   `LF.GeneralProgram.wellFormed` (ten clauses) over the translator's own output.

A model is **accepted** when all three pass. Everything else is refused with a diagnostic, or, for
the two priority-distinctness predicates of §3, accepted but not eligible for every theorem.

## The source surface

What a model **is**: `DTR.GeneralModel`, a list of `DTR.GeneralReactiveClass` declarations and a list
of `DTR.GeneralActorInstance` declarations. The topology is not a field; it is derived from the
instances, so a model cannot carry a topology that disagrees with the instances it describes.

A **reactive class** declares known rebecs (name plus class name), state variables (name plus type,
`int` or `boolean` are the only types the frontend admits), one constructor (typed formal parameters
plus a body), and message servers (name, typed formal parameters, body, optional `Nat` priority). A
class may declare no known rebecs, no state variables and no message servers; all three are needed
for the paper's own figures.

An **actor instance** declares a name, a class name, a known-rebec binding store (known-rebec name to
actor name), positional constructor arguments, and an optional priority. Arguments are literals,
integer or boolean, because the frontend refuses anything else (`nonLiteralInstanceArgument`).

**Expressions** (`DTR.GeneralExpr`): integer and boolean literals, state-variable reads,
parameter reads, thirteen binary operators (`add`, `sub`, `mul`, `div`, `mod`, `eq`, `ne`, `lt`,
`le`, `gt`, `ge`, `logicalAnd`, `logicalOr`) and two unary operators (`negate`, `logicalNot`). Two
absences are deliberate and load-bearing. There is no constructor mentioning `KnownRebecName`, which
makes "a known rebec used as a value" unrepresentable rather than merely checked. And there is no
typing judgement anywhere in this family: the upstream Timed Rebeca typechecker rejects ill-typed
expressions before a document is emitted, so typing is upstream's obligation, not a restriction this
fragment declares.

**Statements** (`DTR.GeneralStmt`), three constructors:

- `assign`, target state variable, expression;
- `trace`, a literal tag, the G5 observability instrument (§7);
- `send`, target (`self` or a declared known rebec), message-server name, payload expressions,
  delay.

**Delays** are `Delay`, a bare `Nat`, nonnegative by construction. Constantness (a literal, not an
expression) is a frontend refusal (`nonConstantDelay`), not an AST property, because the frontend is
where an `after` field is read.

## Source well-formedness: five clauses, priority absent by design

`DTR.GeneralModel.wellFormed` is the conjunction of exactly five clauses, **five**, not the four the
approved stage-B design named; the fifth was added when repeated names were measured as making a
model mean something the frontend did not say (recorded in `docs/STAGE_B_FINDINGS.md`):

1. `bindingsMatchDeclarations`; every instance's bindings name known rebecs its class declares;
2. `argumentsMatchConstructor`, every instance's arguments match the arity and types of its class's
   constructor formals;
3. `sendTargetsDeclared`; every send's target, when it is a known rebec, is declared by the sending
   class;
4. `sendsResolveToMessageServers`; every send names a message server the receiving class declares,
   with matching payload arity;
5. `namesUniqueAndValid`, topology keys unique; class names duplicate-free; class, instance and
   known-rebec names non-empty; known-rebec and message-server names duplicate-free per class.

Parameter and state-variable name uniqueness is deliberately **not** here; it is the elaborator's
concern, reported as a frontend diagnostic (`duplicateStateVariable`, `duplicateParameter`,
`parameterShadowsStateVariable`, `emptyName`).

**Priority is absent by decision.** Distinctness of priorities is a *hypothesis* of those correctness
theorems that need deterministic selection, `DTR.MessageServerPrioritiesDistinct` and
`DTR.ActorPrioritiesDistinct`, not a condition on being decodable at all. A model whose priorities
tie elaborates, translates and runs; which theorems it is eligible for is the question of the
theorem-eligibility table below.

## The frontend gate

`GeneralDiagnosticReason` is the refusal vocabulary, and it is part of the fragment declaration
because a construct the schema reads but the diagnostics refuse is *in the JSON grammar and out of
the fragment*. The refusals that bound the fragment, beyond the name and arity checks mirrored in
§3–§5:

- **Types**: `unknownDeclaredType`, `int` and `boolean` only.
- **Expressions**: `unsupportedExpressionKind`, `missingField`, literal-type checks, and the
  operator-count refusals `unknownBinaryOperator` / `unknownUnaryOperator`, thirteen and two,
  exactly the constructors of §2.
- **Statements**: `branchingNotSupported` (`if`), `iterationNotSupported` (`for`),
  `localDeclarationNotSupported` (`declare`), read faithfully by the schema, admitted by no stage
  before H; `assignmentTargetNotStateVariable`; a write to a formal parameter has no state-semantics
  home; `nonConstantDelay` and `negativeDelay`.
- **Instances**: `nonLiteralInstanceArgument`.

## The translation guard: ten clauses on the target

`Translation.guardGeneralProgram` decides on `LF.GeneralProgram.wellFormed`, **ten** conjuncts, the
tenth added by G3, and refuses the translation when any is false:

`reactorsNonEmpty`, `instancesNonEmpty`, `reactorsWellFormed`, `reactorNamesUnique`,
`instanceNamesUnique`, `instancesResolve`, `instanceArgumentsMatch`, `connectionsWellFormed`,
`targetEndpointsUnique`, `reactionPrioritiesAbsent`.

Two clauses deserve note here. `targetEndpointsUnique`: two connections may not target one input
port, `lfc` rejects many-to-one connections, so the guard refuses the source model rather than
emitting a program the target would reject. And `reactionPrioritiesAbsent`: no reaction carries an
LF `priority` attribute, because `lfc` rejects the attribute outright; precedence between one
reactor's reactions is carried by **declaration order**, which is the only realizable mechanism and
is what stages F and G order. This tenth clause is also the only one of the ten that refuses for
something the target cannot express rather than for an internal inconsistency, the distinction its
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
into the server, per-site, because two sends of one message from one body at one tag must not
collapse (F56). Constructor formals become reactor parameters and the instance's arguments become
its parameter values. The printer emits C++ verbatim in `{= … =}` blocks, and includes `<cstdio>`
exactly when some body contains a `trace`.

## `trace`: in the syntax, τ in the semantics, no frontend spelling

`trace` is a statement constructor on both ASTs with **Option A** semantics: a τ-classified step on
both sides that consumes the statement and changes no modelled state. It exists to make behaviour
observable in generated output, the G5 witness (`priorityWitnessModel`) uses it, and the target
gate asserts on the observed order under `GENERAL_LF_PRIORITY_WITNESS_OK`.

Two boundaries it does not cross. The frontend has **no spelling** for it: nothing in
`Relico/Frontend/` reads a `trace` node, so a trace-carrying program can only be hand-built in Lean,
it is a witness instrument, not a source-language feature. And the bytes a generated program prints
are **target-runtime evidence outside the formal observable alphabet**: `GeneralLabel` does not
contain them, and no theorem quantifies over stdout.

## What this fragment excludes, and why

**By design, not by schedule.** Arbitrary LF programs. The LF subset is *generated* and never
parsed; a correctness theorem over it could only ever be a theorem about the translator's own
output. This is not a milestone exclusion and no later stage discharges it.

**Target-limited, by ruling and permanently.** Division and modulo by zero. The correctness result transfers
to real target behaviour only on executions in which no division or modulo by zero occurs. On the model sides
such an expression is stuck on both sides consistently, `Correctness.compileGeneralExpr_evaluation_none_iff`
proves the target evaluator answers `none` **exactly** when the source one does, while in generated C++ it is
undefined behaviour, and the theorem does not claim otherwise. **No guard is owed.**
`docs/decisions/0045-divide-by-zero-restriction-only.md` closed audit item **C11** by choosing this restriction
over a well-formedness clause, so `DTR.GeneralModel.wellFormed` keeps its five clauses and this exclusion is not
a pending task. Two reasons, both from that record: `wellFormed` is a **name-resolution** predicate and a
zero-divisor test is a value-domain property of an operand; and a syntactic guard would not match this
restriction anyway, because refusing a literal `.intLiteral 0` divisor leaves `x / (-0)` (a `.unary` node),
`x / (1 - 1)` (a `.binary` node) and `x / y` (**F67** part 4's undecidable residue) all accepted. The
restriction sentence above would survive a guard verbatim, which is why the guard was rejected.

**Refused at the frontend, owed to later stages.** Conditionals, iteration, local declarations,
stage H's work, each with its refusal reason already in the vocabulary.

**Still excluded, no stage owner.** Arrays, inheritance, physical actions, environmental inputs,
broadcast. None is refused by name (they simply have no constructor in the AST) so they are
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
does not name a distinctness guard, translation preservation, the initial correspondence, Lemma 1.
What it loses is exactly the theorems that claim a *unique* selection or a *strict* order, because
those are false without distinctness and the paper supplies no tie rule (P4, F27). One consequence
worth stating because the decision's own prose blurs it: not every stage-F/G theorem carries the
guards, only the determinism-needing ones do, which is what the operative sentence says and what
the landed corpus does.

### The five tie fixtures, by name

The five fixtures of the committed corpus that elaborate and fail a distinctness guard, measured
2026-08-28 against `frontend/fixtures/general/`:

| fixture | instance priorities | per-class server priorities | fails |
|---|---|---|---|
| `two-instances` | none, none, none | none (all single) | `ActorPrioritiesDistinct` |
| `two-classes` | none, none | none (all single) | `ActorPrioritiesDistinct` |
| `constructor-arguments` | none, none | none (single) | `ActorPrioritiesDistinct` |
| `send-sites` | none, none | none (single) | `ActorPrioritiesDistinct` |
| `expressions` | none (single actor) | none, none, none | `MessageServerPrioritiesDistinct` |

Two notes the count alone cannot carry. First, **`control-flow` is not one of the five**: it carries
a message-server tie, but it is refused for control flow before eligibility is ever reached, so it
is not elaborable at all. Second, **the stage-B decision's count has drifted**: it named "three
actor-tie and two message-server-tie" fixtures, which described the nine-fixture corpus of that
date. Stage E added `send-sites` (a fourth actor tie) and `control-flow`, one of the decision's
two message-server ties, never elaborated. The names above, not the number five, are the durable
record.

The other four elaborable fixtures (`minimal-class`, `keep-alive`, `priorities`, `fan-in`) satisfy
both guards and are eligible for everything below.

### Theorem families and their hypotheses

Grouped by module; each row's "hypotheses" column lists everything beyond successful compilation
(or, for state-level theorems, beyond the state relation the statement already names).

| family | module | hypotheses | tie models |
|---|---|---|---|
| translation preservation (`compileGeneralModel_wellFormed`, `guardGeneralProgram_wellFormed`, the structural field lemmas) | `Relico/Translation/GeneralBasic.lean` | none | eligible |
| unconditional initial correspondence (`generalCorrespondence_initial`) | `Relico/Correctness/GeneralCorrespondence.lean` | none, successful compilation only | eligible |
| Lemma 1 (`generalTimeEquivalence_forward`, `_backward`, combined) | `Relico/Correctness/GeneralTimeEquivalence.lean` | run-state facts (quiescence, correspondence), state facts, not model-class restrictions | eligible |
| selection, non-claiming (`selectMinimum_mem`, `selectedActor_isSome_iff`, `selectedActor_mem`, `selectedActor_minimal`, `selectedActor_ne_fabricated`) | `Relico/DTR/GeneralActorSelection.lean` | none, but `selectedActor_minimal` is non-strict and cannot see ties | eligible |
| selection uniqueness (`selectedActor_unique`) | `Relico/DTR/GeneralActorSelection.lean` | `model.actorPriorities.Nodup` (the raw spelling; the named predicate unfolds to it) | **excluded** |
| level-1 order, non-strict (`walkedInstances_precedes_of_split`) | `Relico/Correctness/GeneralPriorityOrder.lean` | none, cannot see ties | eligible |
| level-1 strict order (`walkedInstances_strict_of_split`, `portReactions_realizeActorPriority`) | `Relico/Correctness/GeneralPriorityOrder.lean` | `ActorPrioritiesDistinct` | **excluded** |
| level-2 order, non-strict (`walkedMessageServers_precedes_of_split`) | `Relico/Correctness/GeneralPriorityOrder.lean` | none | eligible |
| level-2 strict order (`walkedMessageServers_strict_of_split`, `messageServerReactions_realizeMessageServerPriority`) | `Relico/Correctness/GeneralPriorityOrder.lean` | `MessageServerPrioritiesDistinct` | **excluded** |
| τ-advance correspondence (`generalCorrespondence_retag`, `generalCorrespondence_microstepAdvance`, the trace-tail lemmas) | `Relico/Correctness/GeneralCorrespondence.lean` | the state relation | eligible |
| single-step advance (`generalCorrespondence_advance`) and quiescence (`generalQuiescent_of_earliestPendingEventFuture`) | `Relico/Correctness/GeneralWeakBisimulation.lean` | the state relation | eligible |
| weak transfer, `.timeAdvance` halves (`generalTimeAdvance_forward_weak`, `_backward_weak`) | `Relico/Correctness/GeneralWeakBisimulation.lean` | the state relation | eligible |
| weak transfer, `.consume` halves (`generalConsume_forward_weak_of_fireRepresentative`; `generalConsume_backward_weak_of_takeRepresentative` and `generalConsume_backward_weakStep_of_takeRepresentative`) | `Relico/Correctness/GeneralWeakBisimulation.lean`, `Relico/Correctness/GeneralInstantBlockBackward.lean` | the state relation, plus a run-level residue per direction, the forward α-representative package, the backward `hName` | eligible |
| instant blocks, both directions (`generalInstantBlock_forward`, `_of_source`; `generalInstantBlock_backward`, `_of_target`) | `Relico/Correctness/GeneralInstantBlockForward.lean`, `Relico/Correctness/GeneralInstantBlockBackward.lean` | as the `.consume` row, carried as `hConsumeAnswer` / `hName` | eligible |
| the weak bisimulation interface and its consequences (`GeneralLabelWeakBisimulation`, `.forwardStep`, `.backwardStep`, `.traceAgreement_forward`, `.traceAgreement_backward`) | `Relico/Correctness/GeneralLabelWeakBisimulation.lean` | the interface itself, three of whose six fields carry residues; the two `traceAgreement_*` consequences add none | eligible |

Two further rows belong to the table, and they are the table's most important content. The first had no
theorem to name when this section landed on 2026-08-28 and now has the `.consume`, instant-block and
interface rows above, every one of them conditional; the second has no theorem and never will, because it
records a restriction rather than a missing result.

* **The `.consume` transfer halves have landed, and they are conditional.**
  `generalTimeAdvance_forward_weak` and
  `_backward_weak` cover one label constructor of two; the `.consume` case was task `#129`,
  commissioned by the partial within-tag quotient
  (`docs/decisions/0042-within-tag-partial-quotient.md`: free permutation among distinct reactors at
  one tag, order-preserving within one). `#129` closed with the C7 work. Its first half is what the
  rest of this row was originally written about, and that account still stands:
  `Store.lookup_update_commute` settles the commutation question F76 left open
  (disjoint updates commute observationally),
  `LF.GeneralStep.fire_execution_commute_of_adjacent_queue_swap` is an execution commutation
  across the adjacent same-tag distinct-target queue swap, both executions' steps constructed
  from the two queue-swap-related starting states (a common-start diamond is impossible under the
  head-seeded scheduler), the finals observationally equal, and
  `Correctness.GeneralConsumeMatch` fixes the label correspondence F78 measured as absent (target,
  logical time and compiled payload; the event kind deliberately left to the compiled program's
  answer); it lives in `Relico/Correctness/GeneralCorrespondence.lean`, where the multiplicity-aware
  `GeneralPendingAgrees` (β-(i), decided 2026-08-29) is stated through it. **F86** recorded why the
  first attempt stalled; `GeneralPendingAgrees` was
  non-multiplicity-aware, and consuming one message and one event preserved it only when the pair
  is matched, and that blocker is now discharged at the level of *representation*: the β-(i)
  repair replaces the two directional existentials with an occurrence pairing (permutation of the
  bag against the message projection, permutation of this actor's filtered pending events against
  the event projection), so consuming a matched pair removes one occurrence from each side and the
  relation survives. F86's other question, the scheduler-level
  reorder the per-step transfer condition could not express, was answered by the placement
  decision of 2026-08-30: the light within-tag quotient (`LF.GeneralStepModulo`, exact full
  superdense tags, distinct reactors only), against which the forward `.consume` **core lemma**
  (`Correctness.generalConsume_forward_weak_of_fireRepresentative`) is proved, the
  non-scheduler half: once an α-representative at which the raw `fire` premises hold is
  supplied, the target's modulo weak step at the matched event's `.consume` label and the full
  post-state correspondence are derived.

  **What has landed since, and on what premises.** The forward **wrapper** is
  `Correctness.generalInstantBlock_forward` and its source-predicate form
  `_of_source`: a source instant block is answered by a target execution of the quotient system with a
  per-reactor match. It is a **weak-step** theorem by decision
  (`docs/decisions/0043-forward-instant-block-weak-step.md`), internal τ decomposition stays inside the
  weak transitions rather than being exposed as a spine, and it carries the α-representative package as
  the premise `hConsumeAnswer`, so the representative question decision 0042 froze is answered by the
  caller, not by the theorem. The **backward** condition is
  `Correctness.generalInstantBlock_backward_of_target`, which concludes the whole source block predicate,
  against the per-occurrence actor agreement `hName`; its core is
  `generalConsume_backward_weak_of_takeRepresentative`. `hName` is a **measured** non-derivability, not an
  unfinished proof: `DTR.GeneralActorSelection.selectedActor` is a function of the source configuration
  alone, and `readyActors` / `earliestDueArrival` never mention the target program, its queue or its fire
  order (F76), which `selectedActor_unique` sharpens by proving the source schedule forced. The backward
  τ answer is likewise the premise `hTauAnswer`: five target τ constructors against three source ones,
  `microstepAdvance` has no source counterpart, and `LF.GeneralStepModulo.weakStep_of_raw`'s converse is
  deliberately absent.

  **Eligibility consequence, which is the only part of this row the table proper is about.** None of these
  theorems names `ActorPrioritiesDistinct` or `MessageServerPrioritiesDistinct`, verified by grep over
  every module they live in, zero occurrences, so **no model loses eligibility for them, tie-carrying or
  not**. Their conditionality is on *run-level* data supplied by a caller, not on a model class. The
  decision refuses nothing, exactly as this row said before: contention models are eligible for the
  quotient correspondence now that it has landed.

  **What this does to aims 8 and 9, stated precisely.** The general family has observable-trace agreement
  in both directions: `Correctness.GeneralLabelWeakBisimulation.traceAgreement_forward` and
  `.traceAgreement_backward`, each derived from the six-field label-level weak bisimulation interface
  `Correctness.GeneralLabelWeakBisimulation` **with no further premises**, over the alphabet
  `Correctness.GeneralObservable` (a consume observes the receiver only; a time advance observes both
  endpoints). So aims 8 and 9 of `docs/trusted-boundary.md` now hold **for this family** and not only over
  an abstract LTS, with three qualifications that are part of the claim rather than caveats on it. The
  interface is **conditional**: three of its six fields carry the residues named above (the forward
  `.consume` α-representative package, the backward `.consume` `hName`, the backward τ `hTauAnswer`), so
  an unconditional witness is impossible while any residue stands and the structure is consumed as a
  hypothesis. The agreement is stated over the **partial** within-tag quotient of decision 0042, not the
  paper's Definition 1 verbatim. And **F83**'s underlying observation is unchanged: the *generic*
  finite-trace theorem `weakBisimulation_traceAgreement_forward`/`_backward` still quantifies over both
  transfer conditions, and this family reaches its own agreement through
  `Correctness.generalTraceAgreement_forward`/`_backward` instantiated at the interface, the generic row
  is not discharged unconditionally for this family, and F83's correction of the design's
  *"outright"* stands as written. `docs/claims/general-family-correctness.md` rows 5–16 are the
  row-by-row record with instruments.
* **Division and modulo by zero carry a transfer restriction.** The model-side correspondence holds
  unconditionally, `compileGeneralExpr_preserves_evaluation` and
  `compileGeneralExpr_evaluation_none_iff` make both sides stuck together, but generated C++ has
  undefined behaviour there, so the result transfers to real target behaviour only on executions in
  which no division or modulo by zero occurs (**F67** part 4). **The whole restriction is permanent, and
  nothing about it is owed.** `docs/decisions/0045-divide-by-zero-restriction-only.md` closed audit item C11 by
  ruling against a well-formedness guard for the decidable half, on the ground that a syntactic guard does not
  match a semantic restriction: refusing a literal zero divisor still accepts `x / (-0)`, `x / (1 - 1)` and
  `x / y`, so this sentence would survive the guard verbatim. Eligibility is therefore unaffected in both
  directions; no model is refused for containing a division, and none becomes eligible for anything new.

### `trace` eligibility, in one paragraph

The `trace` statement is theorem-eligible inside the formal semantics; it has a τ-classified step
on both sides (Option A), and `generalContinuationCompiles_trace_tail` /
`generalActorCorresponds_trace_tail` prove its correspondence, but the bytes a generated program
prints are **not** an observable of the theorem boundary: `GeneralLabel` does not contain them, no
theorem quantifies over stdout, and the G5 witness's observed output order is target-runtime
evidence owned by the gate, not by the semantics. A model is no more or less eligible for carrying a
`trace` than for carrying an `assign`.

## Relation to the earlier families

The singleton (v0), finite-store, multi-store, multi-store-payload and global-multi-store-payload
families remain in-tree, each with its own modules, theorems and (for the schema ones) bridge
paths. They are compatibility and regression surfaces, not part of this declaration: a claim true of
one family is not a claim about another. The singleton schema-version-1 path remains available for
regression. When this document and an earlier family's design disagree about "the supported
fragment", this document is the one the current toolchain answers to.

## Maintenance

This declaration moves with the predicates. A commit that adds, removes or changes the meaning of a
clause of `DTR.GeneralModel.wellFormed` or `LF.GeneralProgram.wellFormed`, a constructor of the
syntax types, or a reason in `GeneralDiagnosticReason`, changes this document in the same commit,
including the counts, which are the parts most likely to go stale silently. The theorem-eligibility
table carries the same obligation for its rows: a commit that adds a guard hypothesis to a theorem,
lands a previously missing transfer half, or changes the fixture corpus's tie census moves the table
in the same commit. The tie census in particular is coupled to the fixture directory, not to this
file, `send-sites` added a tie row that no edit here caused, and the next fixture addition can do
the same again.
