# Stage B findings — what building the general Lean frontend turned up

**Why this file exists.** The same reason [`PAPER_CORRECTIONS.md`](PAPER_CORRECTIONS.md) exists, applied
one level down. That file records places where the *paper* says something the tool cannot accept. This
file records places where the *repository* — the exporter, the design document, or the earlier families'
Lean modules — says something the general frontend could not accept, or says nothing where it needed to
say something. Eighteen accumulated while writing the eight stage-B modules, and two more while writing the
stage-B tests, which is too many to relay in conversation and too many to leave in a gitignored scratch file.

**Provenance rule.** Every finding below states how it is known, in one of four grades:

- **measured** — produced by running something: `lake build`, a Lean probe file, the Java exporter over a
  real `.rebeca` model, or a script over the corpus. The run and its output are named.
- **read** — read directly out of a file in this repository, cited as `path:line`.
- **decided** — a design choice with a stated reason, where the alternative was live and is recorded.
- **inferred** — reasoned from the above without being run. Labelled as such, and none of the soundness
  claims rest on this grade.

**What is deliberately not here.** Divergences between the paper and the repository belong in
`PAPER_CORRECTIONS.md`, and two findings below are the repository-side halves of entries there: F18 pairs
with P14 (the queue bound), and F13 is the substance of P15 (static connection delays). Where a finding is
a Lean-mechanics measurement of no interest outside this codebase, it is stated in one paragraph rather
than three. The closing section discharges one further paper-side entry, P16, and records the second defect
that came out of writing it, P17.

**Scope rule this file operates under.** Scope comes from the paper; semantics comes from the repository;
where the two conflict the repository is definitive. So a finding never proposes changing the exporter's
*meaning* to match the paper — it records the divergence and, where the exporter is more restrictive than
it needs to be, proposes a change to the exporter with its own gate.

---

## F1 — the design document's operator set was short by two

**What it is.** The approved stage-B design listed eleven binary operators for the general expression
language. The exporter emits **thirteen**: `!=  %  &&  *  +  -  /  <  <=  ==  >  >=  ||`. Division and
modulo were missing from the design.

**How it is known.** Read, from `frontend/java-bridge/RebecaGeneralJsonExporter.java`'s operator table, and
recorded in `Relico/Frontend/GeneralSchema.lean:95-96` alongside the two unary operators `!` and `-`.

**Consequence.** `Relico/DTR/GeneralSyntax.lean` implements thirteen. Had the design been followed
literally, every model using `/` or `%` would have exported successfully and then failed to decode, which
is the worst failure shape available: the tool would have accepted the model at the boundary it advertises
and rejected it at a boundary the user cannot see.

---

## F2 — well-formedness needed a fifth clause the design did not have

**What it is.** The approved design gave `GeneralModel.wellFormed` four clauses. It has five; the addition
is `namesUniqueAndValid`.

**Why it was needed.** Deriving the actor topology from the model gives *agreement* between bindings and
declarations but not *uniqueness* of names. `Common/ActorTopology.lean` requires `Store.KeysUnique` and
non-empty names, and every `find*?` in the general well-formedness module returns the **first** match. So
without a uniqueness clause, two classes could share a name and the model would still be well formed,
while every lookup silently resolved to whichever one was written first.

**How it is known.** Read, `Relico/DTR/GeneralWellFormed.lean:323-349` for the clause and `359-366` for
the conjunction; `Relico/Common/ActorTopology.lean` for the topology's own requirements.

**Consequence.** Recorded here because the design is the artefact under review, not the code: a four-clause
`wellFormed` would have been a real soundness hole, and it was found by trying to write the fifth thing the
topology needed rather than by reviewing the design again.

---

## F3 — the five extraction lemmas are Bool case analyses, not projection chains

**What it is.** Each of the five clauses of `wellFormed` has an extraction lemma so a later stage can take
the clause it needs. They are proved by `revert`, `unfold`, then `cases <clause> <;> simp` — not by
projecting out of a conjunction.

**Why.** `&&` is not associative *as written*; it parses one way, and a proof written as a projection chain
would prove a subtly different clause under the other reading while still compiling. With no compiler
available at authoring time, a form whose correctness depends on an associativity convention was not
acceptable. The case analysis is insensitive to it.

**How it is known.** Decided, then **measured**: all five compiled on the first `lake build`, `exit=0`.

---

## F4 — five deviations from the design's state section, one of them forced

**What it is.** `Relico/DTR/GeneralState.lean` departs from design §6 in five ways. Four are naming or
efficiency choices: the message store is `bag`, not `queue`; time is `LogicalTime`, not `Nat`; arrival
selection is a single fused `earliestDueArrival` rather than `filter |>.min?`; and `readyActors` takes no
model witness, because it needs none.

The fifth was forced. The design wrote `simultaneouslyReady cohort`, but `simultaneouslyReady` is a
**pairwise** predicate, so that expression does not typecheck. `cohortSimultaneous` was added to lift it to
a cohort.

**How it is known.** Read, against the design; the type error is **inferred** from the predicate's arity as
written, and the replacement is **measured** — the module compiles and `readyActors_discriminates` closes
`by decide`.

**Consequence.** Worth recording because a design that does not typecheck cannot be reviewed as though it
does. The lift is the kind of thing a reader supplies mentally and a compiler does not.

---

## F5 — the obvious statement of `readyActors` soundness is false

**What it is.** Soundness and completeness of `readyActors` are stated through **list membership**, not
through `Store.lookup`. The `lookup` form is not merely harder to prove; it is **false**.

**The counterexample.** A message bag `[(a, due at 3), (a, due at 5)]` — duplicate keys — puts both
`⟨a, 3⟩` and `⟨a, 5⟩` in the ready cohort, while `Store.lookup a` answers only the first. Any statement
phrased as "the cohort contains exactly what `lookup` finds" is therefore refuted by a two-element store.

**How it is known.** Inferred from `Store`'s definition (`Common/Store.lean:13-16`,
`abbrev Store K V := List (K × V)`, so duplicate keys are representable) and confirmed by the membership
statements compiling while the `lookup` phrasing was abandoned before it was written.

**Consequence.** The `lookup` form becomes available as a corollary in stage D or G *under the additional
hypothesis* `Store.KeysUnique`. It is not available now, and a reviewer who expects the tidier statement
should know it was rejected on a counterexample rather than for convenience.

---

## F6 — "zero occurrences in the repository" is evidence of style, not of absence

**What it is.** While designing the DTR modules I treated `omega`, `Option.some.injEq`, `∃ x ∈ l` and
`split` as unavailable because they have zero occurrences repo-wide, and designed around all four —
splitting one lemma into `_le` and `_gt` halves specifically to avoid needing `omega`.

**The correction.** **Measured** by direct probe on 2026-08-18: `omega`, `Option.some.injEq` and `split`
are all **available**. Zero occurrences reflected the local proof style of whoever wrote the earlier
families, nothing more.

**Consequence.** Nothing is broken — the designed-around proofs compiled — but the extra labour was
unnecessary. The rule this yields, and the reason it is written down: absence of a construct from a
codebase is evidence about the codebase's authors, not about the toolchain. Probe before designing around
it. This cuts the other way too, which is why the one unprecedented construct in `GeneralDecoder.lean`
(prefix `!` on a `Bool`) was flagged for the gate rather than assumed safe — and then **measured** as fine:
`GeneralDecoder` compiled at the first attempt, so `!` on a `Bool` is available and its absence from the
repository was, once again, only a fact about the earlier authors.

---

## F7 — one tactic was eliminated because its two readings disagree

**What it is.** `cases h : <expr>` was removed entirely in favour of a helper,
`optionCases (value : Option α) : value = none ∨ ∃ content, value = some content`, proved by `cases` on a
bare variable.

**Why.** Whether `cases h : e` rewrites surrounding *hypotheses* as well as the goal could not be settled
without a compiler, and one branch of the inversion proof is ill-typed under one of the two readings. A
helper proved by a tactic with only one reading removes the question.

**How it is known.** Decided under uncertainty; the helper is **measured** (it compiles, and the inversion
proofs that use it compile).

---

## F8 — a real exporter/semantics divergence: writing to a parameter exports cleanly

**What it is.** `RebecaGeneralJsonExporter.renderAssign` gates an assignment target on
`scope.isValue(name)`, and that scope is locals ∪ state variables — where **locals includes formal
parameters**. So for a message server `msgsrv m(int p)`, the statement `p = 3;` **exports successfully**.

**Why that is a divergence.** `GeneralActorState.valuation : Store VarName GeneralValue` holds state
variables. There is no parameter environment in the DTR state at all, so an assignment to `p` has nowhere
to land. Nor does well-formedness catch it: `GeneralStmt.assign` carries a bare `VarName` and no clause of
`wellFormed` constrains it to be a declared state variable.

**How it is known.** Read, from the exporter's scope handling and from
`Relico/DTR/GeneralState.lean`'s state record.

**Consequence and the decision taken.** The Lean **elaborator** rejects it, with
`assignmentTargetNotStateVariable`, because the elaborator is the only layer positioned to notice: it sees
the enclosing declaration's state-variable and parameter lists at once, which neither the exporter's scope
object nor the assembled-model predicate does. This is a genuine three-layer boundary case and is the
clearest justification in the project for having the elaborator layer at all.

**Not fixed in the exporter, deliberately.** Making the exporter refuse it would be a second answer to a
question that now has one, and the exporter's answer would have to agree with the elaborator's forever.
The elaborator refuses; the exporter's permissiveness is harmless as long as nothing downstream of the
elaborator exists. That reasoning expires if a second consumer of `general-v1` is ever written.

---

## F9 — no negative integer literal can appear anywhere in a `general-v1` document, and the reason is not the one in the code

**What it is.** `integerLiteralText` explicitly refuses a value with `signum() < 0`. That refusal is
**never reached** for a negative literal written in Rebeca source.

**What actually happens.** RMC's parser reports `-5` as a `UnaryExpression` wrapping a positive `Literal`,
not as `Literal("-5")`. **Measured** 2026-08-19 by probe 5 (`tmp/probe5.sh`, three separate models so that
no single early rejection could hide the others): `limit = -5;` in a message server exports cleanly as

```json
{"kind":"unary","operator":"-","operand":{"kind":"intLiteral","value":5},"line":23}
```

So in ordinary expression position a negative integer is perfectly expressible — as a unary node. The
`signum` refusal guards only hand-built or computed text, and a source-level negative never meets it.

**Consequence.** Where the exporter admits *only* a literal — instance arguments (R4) and `after` delays
(D9) — a negative value is rejected as **"a non-literal"**, which is a true statement about the AST and a
misleading statement about the program. Both rejections were confirmed verbatim in the same run:

```
a non-literal constructor argument bound of instance configuredNegative (R4 admits a literal only) (line 28)
a non-literal after delay in message server Producer.tick (D9: a Lingua Franca connection delay is static) (line 26)
```

This is what F17 fixes, and knowing the mechanism is what determined the fix's shape: one level of constant
folding, not a relaxation of the `signum` check.

---

## F10 — two schema fields are fully redundant and are dropped rather than cross-checked

**What it is.** A send statement carries `targetClassName`, and each known-rebec binding carries a
`className`. Both are **dropped** by the elaborator.

**Why.** `receivingClass?` and `classOfActor?` already resolve both, from the model's own structure. Reading
the wire field as well would give one question two answers, with nothing keeping them in agreement — and
when they disagreed, no rule would say which one wins.

**How it is known.** Read, `Relico/DTR/GeneralWellFormed.lean:236-258` for `receivingClass?`.

**Consequence.** A hand-written document with a wrong `targetClassName` is accepted, because the field is
not consulted. That is the intended behaviour: the field is redundant, and the alternative was a
consistency check that could fail in a way the producer could not have caused.

---

## F11 — the exporter already type-checks constructor arguments, so the Lean clause is a cross-check

**What it is.** `renderInstanceArgument` checks each instance argument against the declared type of the
corresponding constructor parameter, at export time.

**Consequence.** `argumentsMatchConstructor` in Lean (design D8) is therefore not the first line of defence
against a mistyped argument; it is a check *of the exporter*. That is worth stating plainly, because a
reader could otherwise conclude the property is unverified upstream and be surprised at how thin the
exporter's own tests need to be. Both layers answering here is acceptable — and different from F10 —
because the exporter's answer is about one instance in isolation while Lean's is about the assembled model,
and the exporter's check can be deleted without the model's guarantee changing.

**How it is known.** Read, `frontend/java-bridge/RebecaGeneralJsonExporter.java:1399-1453`.

---

## F12 — one diagnostic is reachable only inside a construct this stage already rejects

**What it is.** `localDeclarationNotSupported` fires on a `declare` statement. But the exporter emits
`declare` in exactly one position: as a `for` loop's counter (`Scope.declare`, exporter line 1878). Stage B
rejects `for` outright, before descending into it.

**Consequence.** The diagnostic is unreachable through the exporter and is retained anyway, because a
hand-written document can carry a `declare` and because stage H (control flow) will make `for` legal, at
which point this becomes live. Recorded so that a coverage report showing it unexercised is understood as
expected rather than as a gap.

**How it is known.** Read, exporter line 1878 and the statement dispatch in
`Relico/Frontend/GeneralElaborator.lean` — then **measured** at the stage-B compile gate, 2026-08-19. The
committed fixture `frontend/fixtures/general/control-flow.parser.json` contains one `declare`, and it sits
inside a `for` initializer; running the bridge over it reports

```
general-v1: a loop statement, which this stage does not admit: `for` in Looper.scan at line 13
```

The loop is refused before the descent that would reach the `declare`, so the prediction is confirmed by
the only fixture in the repository able to test it.

---

## F13 — the static-delay premise, stated by the exporter and now confirmed

**What it is.** The exporter refuses a non-literal `after` delay, and justifies the refusal in its own
message: *"D9: a Lingua Franca connection delay is static"*. That is a claim about the target language,
asserted by this repository, that nothing in this repository verifies.

**How it is known.** **Confirmed by the project lead**, 2026-08-19: *"lf delay has to be static."* Recorded
as P15 in `PAPER_CORRECTIONS.md` on that basis — as a confirmed premise, not as an open question and not as
a measurement against `lfc`, which is the grade of evidence the rest of that file uses.

**Consequence.** D9 stands, and `GeneralStmt`'s `Delay : Nat` makes a non-constant delay unrepresentable in
any case, so nothing downstream changes. What remains is only that the *message* is wrong in the negative
case: `after(-2)` is perfectly static, and refusing it as "non-literal" reports the wrong objection
entirely. See F17.

---

## F14 — a decoding capability the repository had never used

**What it is.** The four earlier families decode `Int`, `Nat` and `String` from JSON. **Nothing in the
repository had ever decoded a boolean**, so whether `FromJson Bool` existed was an open question, with a
two-line hand-written `Json.bool` match as the fallback.

**How it is known.** **Measured** and closed: probe 4 (`tmp/probe_json4.lean`, 2026-08-19) reported
`bool=false` from a real decode. The instance exists; the fallback was not needed.

**Consequence.** `general-v1` is the first family whose expression language has boolean literals, which is
also why the question arose here and not earlier. Closed, and recorded only so that the fallback is not
reintroduced by someone who finds the same question open in an old design note.

---

## F15 — the repository had no recursive frontend elaborator, and the rule for writing one is narrow

**What it is.** All four earlier families elaborate flat structures: a field maps to a field. `general-v1`
has a recursive expression language, so `elaborateGeneralExpr` must recurse — and there was **no precedent
in the repository** for a recursive function over a JSON-derived schema record.

**The rule, measured.** Probe 4 (2026-08-19) settled it. A recursive function may descend through an
`Option Self` schema field *structurally*, but **only if the argument is destructured in the function's own
top-level pattern**. The projection form —

```lean
def f (raw : RawGeneralExpr) : ... :=
  match raw.operand with ...   -- ✗
```

— fails **both** as structural recursion and under well-founded recursion, because `raw.operand` is not a
subterm the equation compiler can see decreasing. Destructuring `raw` in the function's own `match` makes
the same field a visible subterm and it succeeds. Non-recursive functions may project freely, which is why
this rule bites exactly one function in the whole frontend.

**Consequence.** `elaborateGeneralExpr` is written in destructured form throughout, which is why it looks
stylistically unlike its four flat siblings. Recorded because the natural edit — "tidy this up to match the
others" — breaks the build, and the error message points at recursion rather than at the projection that
caused it.

---

## F16 — the frontend has no `#guard` tests, and could not have any

**What it is.** Frontend behaviour across all four earlier families is tested through `IO`: a shell script
runs a bridge check over a fixture and compares output. There are **zero** `#guard` or `#eval` assertions
about any decoder. The DTR-layer modules are the opposite — that is where `#check`, `#guard` and `decide`
live.

**Why it is structural, not an omission.** A decoder's input is a *file*. `#guard` evaluates at elaboration
time with no file system, so the only way to assert on a decode is to inline the JSON as a string literal in
Lean — which then duplicates the fixture, and the duplicate is what rots.

**Consequence.** Stage B's tests split along the same line: the obligations that live in `Relico/Tests/` are
about `GeneralModel` and its well-formedness lemmas, and everything about the decoder is asserted by
`frontend/check-general-lean.sh` against committed fixtures. A reviewer counting registry obligations per
module should expect the frontend modules to contribute few, and that is not a coverage gap.

**How it is known.** Read, across `Relico/Tests/` and `frontend/check-*.sh`.

---

## F17 — a negative constructor argument is rejected by a restriction no layer states, and this is a bug

**What it is.** `new Counter(-1)` is refused, with

```
a non-literal constructor argument bound of instance configuredNegative (R4 admits a literal only) (line 28)
```

R4 restricts instance arguments to **literals**, and `-1` is a literal in every sense the user cares about.
It is refused only because of the AST shape measured in F9: RMC hands back
`UnaryExpression(-, Literal("1"))`, and the gate at
`frontend/java-bridge/RebecaGeneralJsonExporter.java:1409` tests `candidate instanceof Literal`, which a
`UnaryExpression` is not.

**Why this is a bug and not a scope decision.** Every other restriction in the exporter refuses something
the tool genuinely cannot represent — a non-static delay, a multi-actor send, a `for` loop. This one refuses
something the tool represents perfectly well: `GeneralValue` carries an `Int`, the schema's `intLiteral`
carries an `Int`, and `-1` reaches the wire without difficulty in ordinary expression position. Nothing
downstream of the gate objects. The restriction exists nowhere except in an `instanceof` test, and its
message misdescribes the program it rejects.

**How it is known.** **Measured** by probe 5, and the rejection message above is quoted verbatim from that
run. The exporter lines are **read**.

**The fix, approved in scope by the project lead** (*"we must fix the negative ones… we should fix that"*)
and pending its own gate as task #66:

- add `signedLiteralText`, which peels a unary `-` off a `Literal` operand and otherwise returns the
  candidate unchanged — one level only, so `--1` stays rejected;
- use it at the `1409` gate, so a signed literal reaches the argument path;
- add `signedIntegerLiteralText`, which is `integerLiteralText` **minus the `signum() < 0` refusal**, called
  from that path *only* — that is, at `1449`, which is the `integerLiteralText` call inside
  `renderInstanceArgument` itself. The other three call sites — `1014` (`@priority`), `2169` (the `after`
  delay) and `2304` (a literal in ordinary expression position) — keep the
  unsigned function, so a negative priority stays refused and **no committed expected JSON changes**;
- at `2156`, use the peel only to make the *diagnostic* accurate. `after(-2)` remains rejected, because a
  negative delay is meaningless rather than merely unrepresentable — but it is now rejected as a negative
  delay instead of as a non-literal.

That last point is the whole shape of the fix: `signum` is not relaxed globally, it is bypassed on exactly
the one path where a negative value is legitimate, and the delay path gains an honest message without
gaining a permission.

Two details of `renderInstanceArgument` survive the change untouched, which is part of why the fix is small.
The two boolean branches compare the literal text against `BOOLEAN_LITERALS`, and no signed text is ever a
member, so `-true` falls through to the integer path and is rejected there — by digit validation, with a
message about an integer literal, which is the right complaint. And a declared `boolean` parameter given
`-1` still fails its own branch first. The one behaviour that changes is the one intended: an `int`
parameter given a negative literal now exports.

---

## F18 — the queue bound is decoded and then discarded

**What it is.** `RawGeneralModel` carries `queueBound`, the exporter emits it, and the elaborator **drops
it**. `DTR.GeneralModel` has no such field.

**Why.** Nothing in the DTR semantics bounds a message bag. `GeneralActorState.bag` is a `Store`, which is a
`List`, and no rule of the enabling condition or of well-formedness consults a capacity. A bound could only
be enforced by a transition relation that can refuse a send, and this repository has none.

**Consequence.** This is the repository-side half of **P14**: the paper's model is unbounded, RMC's is
bounded, and a model whose behaviour differs between the two would not be caught here — the field is carried
across the wire and then ignored. It is retained in the schema deliberately, because dropping it from the
exporter would destroy information the producer has and a future stage may need; the finding is that its
presence in the schema should not be read as evidence that anything enforces it.

**How it is known.** Read, `Relico/Frontend/GeneralSchema.lean` for the field and
`Relico/DTR/GeneralWellFormed.lean:137-160` for the model record that lacks it.

---

## F19 — the obligation registry cannot see the filesystem, so the "172 modules" figure is discipline and not a check

**What it is.** `tools/relico_bench_registry.py` **never reads `Relico/Tests/`**, or any Lean source. It locks
TSV against TSV: `obligations.tsv` row count against `EXPECTED_OBLIGATIONS`, every row's
`final_benchmark_id` against `benchmarks.tsv`, and the sum of `benchmarks.tsv`'s `obligation_count` against the
same constant. Three locks, all internal to the registry.

What ties the registry to the code is that `Relico.lean` has exactly 172 `import Relico.Tests` lines and
`Relico/Tests/` holds exactly 172 files. That correspondence is maintained by hand.

**Consequence, and it cuts both ways.** A new module under `Relico/Tests/` would make the project's own
"172 modules / 2129 obligations" narrative false, and **no gate would fail** — the validator would still pass,
because nothing it reads changed. Equally, a module deleted from `Relico/Tests/` would leave its obligations
counted.

**What was decided because of it.** Stage B adds **no module** to `Relico/Tests/`. That is not an evasion of the
registry; it is what the registry's own rule requires. Every obligation row must carry a `final_benchmark_id`
drawn from the 58 accepted benchmarks, and the general layer is evidence for none of them — it cannot translate
anything until stage D. Rows for it would have to be mapped to some other family's benchmark, which would make
the registry assert a relationship that does not exist. So the stage-B tests live in
`frontend/lean-bridge/GeneralFrontendTestMain.lean`, outside the directory the registry describes, and the
counters do not move. When the general family acquires a benchmark in stage G, that file is the natural thing to
move into `Relico/Tests/` and register in the same commit.

The mathematical content of the layer is not going untested by this choice: the three DTR modules carry 26
theorems that elaborate on every `lake build`, which is a stronger check than any `#guard` would be. It is only
the decoder, which needs `IO` and therefore cannot be `#guard`ed at all (**F16**), that depends on the runner.

**How it is known.** Read, `tools/relico_bench_registry.py:16-21` for the constants and `:355-378` for the
`unmapped` and `declared_total` checks; counted, the 172 imports and 172 files.

---

## F20 — the new negative corpus asserts 8 of the 32 diagnostic reasons, and the other 24 are unexercised

**What it is.** `GeneralDiagnosticReason` declares **32** reasons. After this stage's work — eleven fixtures in
`frontend/fixtures/general/lean-reject/` plus `control-flow` — the runner asserts **8**: `invalidJson`,
`schemaDecodeFailed`, `unexpectedFamily`, `unsupportedSchemaVersion`, `bindingsMatchDeclarationsFailed`,
`argumentsMatchConstructorFailed`, `namesUniqueAndValidFailed`, `iterationNotSupported`. Twenty-four are
asserted nowhere.

**Why it is worth writing down.** A directory of eleven negatives reads like coverage. It is not: it is four
decode steps and three of five well-formedness clauses. The project has been careful about this distinction
before — the eight fixtures relocated to `upstream-reject/` were moved precisely because a fixture that cannot
reach the code it claims to test "reads as coverage" while proving nothing about that code. The same standard
applied here gives 8 of 32.

**The split, because the three groups need different work.** Twenty-one are reachable from a hand-written
document, so a further fixture in the same directory would exercise them. One, `branchingNotSupported`, is
reachable only from a document the exporter really emits, and is currently shadowed: the exporter translates
`if` faithfully and this stage refuses it, but `control-flow.rebeca` contains a `for` and the elaborator stops
at the first statement it cannot admit, so reaching the `if` path needs a new `if`-only source model. One,
`localDeclarationNotSupported`, is shadowed until stage H for the same structural reason and is **F12**. One,
`modelNotWellFormed`, is unreachable by construction and documented as such.

**Consequence.** None of the twenty-four is thereby suspected of being wrong; the claim is only that they are
unexercised, which is smaller and true. The figure to watch is 8 of 32 — a later change to that directory that
does not move it has added fixtures rather than coverage.

**How it is known.** Measured this session by extracting the constructors of the inductive between
`inductive GeneralDiagnosticReason where` and `deriving Repr` in `Relico/Frontend/GeneralDiagnostic.lean:83-210`
and differencing them against the reasons the runner names.

**Update 2026-08-20 (stage E), and this supersedes every "8 of 32" in this file, including the one in
"What these findings ask for" below.** The count moved to **9 of 32** at `b14809b`, which added
`frontend/fixtures/general/lean-reject/invalid-parameter-shadows-state.json` and asserted
`parameterShadowsStateVariable`. The corpus is twelve fixtures, not eleven, and twenty-three reasons are
unexercised, not twenty-four. The finding's text above is left as written because it records what was true
at the end of stage B; only the live number has moved.

Two details of that move are worth carrying, because neither is what this finding's "twenty-one are reachable
from a hand-written document" phrasing would suggest. First, the fixture that closed it is **not** a mutation
of `minimal-class.parser.json` — that document has an empty `stateVariables` and an empty parameter list, so
the collision cannot be expressed there in one change. It mutates `constructor-arguments.parser.json` instead,
which preserves the one-mutation property by changing the base rather than growing the diff. Second, the reason
was picked ahead of the other nineteen on a criterion this finding does not state: `parameterShadowsStateVariable`
was the only unexercised reason that another predicate's correctness argument depended on, since
`DTR.GeneralModel.namesUniqueAndValid` (`Relico/DTR/GeneralWellFormed.lean:319-321`) and two docstrings
(`Relico/Frontend/GeneralElaborator.lean:820-823`, `Relico/Frontend/GeneralDecoder.lean:30`) justify **not**
checking parameter/state distinctness by naming the elaborator as the layer that does. Until `b14809b` that
delegation rested on a read of the source rather than on a green assertion. Prefer that criterion — an
unexercised reason some other layer is relying on — to working down the list in order.

**Second update 2026-08-21 (stage E), and this supersedes the "9 of 32" above.** The count moved again to
**11 of 32**, in the commit that added
`frontend/fixtures/general/lean-reject/invalid-send-target-undeclared.json` and
`invalid-send-message-server-unknown.json` and asserted `sendTargetsDeclaredFailed` and
`sendsResolveToMessageServersFailed`. The corpus is **fourteen** fixtures and **twenty-one** reasons are
unexercised. Both departures from this finding's list are still governed by the criterion the first update
added rather than by list order, but the criterion applied differently: these two were taken because the
clauses they name are reached only by a *send*, and the directory's original base contains none, so they were
the two entries on this finding's list that no amount of mutating `minimal-class.parser.json` could ever have
reached. They were also taken as a pair by necessity rather than convenience — an undeclared send target fails
clause four as well as clause three, so the fixture that names clause four has to be a different document with
a declared target, or clause four's assertion asserts nothing.

One residue is recorded rather than closed. `sendsResolveToMessageServers` has **two** ways to fail — an
unresolvable message-server name and a payload length that disagrees with the message server's parameter count
(`Relico/DTR/GeneralWellFormed.lean:282`) — and only the first is now exercised. So "11 of 32" counts *reasons*,
and one of the eleven is a reason with a tested channel and an untested one. That is a limit of counting
reasons, not a defect in the count, and it is the second time this finding has run into it: the four
`namesUniqueAndValid` fixtures share one reason across four requirements for the same structural cause.

---

## What these findings ask for

Most of the twenty are records, not requests. Five carry an action:

- **F17** — fix the exporter, task #66, designed above and awaiting its own gate.
- **F13** and **F18** — cross-referenced as P15 and P14 in `PAPER_CORRECTIONS.md`; P15 is added by this
  stage, recording the static-delay premise as confirmed rather than open.
- **F5** — the `Store.lookup` form of `readyActors` soundness is available as a corollary in stage D or G
  under `Store.KeysUnique`, and should be stated there rather than left as an absence.
- **F8** — the reason the exporter is left permissive expires the day a second consumer of `general-v1`
  exists. Whoever writes one should read that finding first.
- **F20** — twenty-one of the twenty-four unexercised reasons need only another fixture in
  `frontend/fixtures/general/lean-reject/`, and `branchingNotSupported` needs an `if`-only source model. Both
  are cheap and neither is done. The count to move is 8 of 32. *(Superseded twice — three of them are now done
  and the count is 11 of 32; see F20's two updates. The `if`-only source model is still owed.)*

**F19** asks for nothing now, and that is the point of recording it: the decision it documents — that stage B
adds no module under `Relico/Tests/` — looks like an omission from the outside, and a later session tidying up
would be within its rights to "fix" it. The finding is what makes that a decision rather than an oversight.

One further entry was owed to `PAPER_CORRECTIONS.md` independently of the list above, and is now **discharged
as P16**. Writing it changed it. The owed note said `readyActors` "commits to" a tie-breaking rule the paper
does not give; it does not — it returns the cohort and selects nothing, which makes it more specified than the
paper on *dueness* and exactly as unspecified on *ties*. Reading the PDF for the entry turned up the reason
the paper has nothing to compare against: both TAKE rules are guarded by an `enabled_m` / `enabled_tr`
predicate that occurs once each and **is never defined**, so `earliestDueArrival` is not a refinement of the
paper's condition but the only written form of it. P16 also shows the omission is fatal rather than cosmetic —
without a clock comparison inside `enabled_m`, TIME PROGRESS can never fire — and a second, smaller defect
found in the same pass is filed as **P17** (TIME PROGRESS transposes the message tuple's sender and
receiver). A divergence in the direction of precision is the easiest kind to leave unrecorded and the most
misleading to, and in this case looking at it properly was what found the underlying bug.




