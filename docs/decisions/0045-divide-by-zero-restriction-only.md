# C11: divide-by-zero stays a fragment restriction, with no well-formedness guard

Status: **APPROVED 2026-09-02**

Decision: **Option B.** Division and modulo by zero remain a **G6 fragment restriction** on transfer to real
target behaviour. `DTR.GeneralModel.wellFormed` keeps its five clauses and gains **no sixth**. No literal-zero
divisor guard is added, at the model predicate or anywhere else.

Decision: the restriction is **permanent**, not pending. Audit item C11 is closed by this ruling rather than by
an implementation, and the fragment declaration says so.

Decision: no Lean change. `Relico/DTR/GeneralWellFormed.lean`, `Relico/Frontend/GeneralDiagnostic.lean` and
`Relico/Frontend/GeneralDecoder.lean` are untouched, and prediction **F-7** of `docs/STAGE_F_DESIGN.md`
(*"`wellFormed` stays at five clauses"*) therefore stands.

## Context

`docs/STAGE_G_FINDINGS.md`'s **F67 part 4** established the defect: `x / 0` is well-formed, translated, printed,
and undefined behaviour in the generated C++. It then split the defect in two — a syntactically decidable half
(a literal zero divisor, which it argued *"should be refused"*) and an undecidable residue (a divisor zero only
on some execution, which it assigned to the fragment declaration) — and explicitly left the sequencing open:
*"Whether the divide-by-zero guard lands before G3, after it, or is folded into G6 as restriction-only is left
open here."* The acceptance ledger's C11 row repeated *"Confirm before implementing."*

This decision answers that question. It is the fold-into-G6 option.

## Why the restriction, and not the guard

**`wellFormed` is a name-resolution predicate, and all five clauses are of that one kind.** Measured: none of
`bindingsMatchDeclarations`, `argumentsMatchConstructor`, `sendTargetsDeclared`, `sendsResolveToMessageServers`
or `namesUniqueAndValid` inspects an expression at all — `statementTargetDeclared` returns `true` outright for
`.assign` and `.trace` without looking inside them. The predicate means *every name this model mentions
resolves, and the names that must be unique are*. A zero-divisor clause is a value-domain property of an
operand, so it would be the first clause of a different kind, and the predicate's meaning would change rather
than merely its arity.

**Divide-by-zero is a target-fidelity restriction, not a model property.** The two models already agree
perfectly: `DTR.GeneralBinaryOp.apply` returns `none` at a zero divisor for both `.div` and `.mod`, and
`Correctness.compileGeneralExpr_evaluation_none_iff` proves the target evaluator is `none` **exactly** when the
source is. `Correctness.compileGeneralExpr_preserves_evaluation` carries the agreeing case. The divergence is
between the *model* and the *emitted C++*, which prints `/` and `%` verbatim. Nothing in the mechanised
development is unsound, and the restriction is a statement about which executions the result transfers on.

**A syntactic guard would not match the semantic restriction.** This is the decisive reason. A literal-zero
guard refuses `.binary .div e (.intLiteral 0)` and its `.mod` counterpart. It does **not** refuse:

- `x / (-0)` — a negative literal reaches the AST as a `.unary` negate over `.intLiteral`, as
  `Relico/Frontend/GeneralElaborator.lean`'s `signedIntegerLiteral` shows, so `-0` is not an `.intLiteral 0`
  node;
- `x / (1 - 1)` — a `.binary` node, constant-folded by nothing, because the elaborator deliberately does not
  evaluate expressions (*"a folding pass that recursed would be an evaluator"*);
- `x / y` where `y` holds zero at run time — F67's own undecidable residue.

So the restriction sentence survives **verbatim** under a guard: the guard covers one of three syntactic shapes
and none of the semantic ones. Adding it would produce a claim that reads stronger while narrowing nothing, and
it invites the one-question refutation *"what about `1 - 1`?"*. The project's target-fault doctrine asks for a
guard that **corresponds to** the restriction it accompanies, and no decidable guard here does.

## What was rejected, and the argument for it

**Option A — a sixth `wellFormed` clause refusing a literal zero divisor.** Rejected. The argument for it is
real and is recorded rather than dismissed: every other target limitation since stage E has been given the
guard-plus-refusal-test shape; F67 says the decidable half *should* be refused; and refusing `x / 0` at the
boundary the user sees is better tooling than emitting undefined behaviour. Option A is also **cheap** — each
extraction lemma is a Bool case analysis on its own clause, written that way so an appended conjunct does not
break it, and `classifyGeneralWellFormedness`'s `modelNotWellFormed` branch exists precisely so that *"adding a
sixth conjunct without extending this function yields an honest 'not well formed'"*.

It was rejected on **claim strength**, not on cost: A buys no narrower fragment, and it would silently
strengthen what `hWellFormed : model.wellFormed = true` means at 44 source-side hypothesis sites whose text
would not change. A stronger hypothesis breaks no proof, but a theorem that reads the same while assuming more
is exactly the drift this project's documentation rules exist to prevent.

A also sits against a documented layering. `frontend/lean-bridge/GeneralLfPrinterTestMain.lean` argues, for the
F32 gap, that the repair is *"not a missing clause in `wellFormed`, which would duplicate the elaborator's check
and collapse a layering three docstrings agree on"*. The elaborator already walks every expression and already
refuses per-expression (`unknownBinaryOperator`, `unsupportedExpressionKind`, `undeclaredVariable`), so a
syntactic check in the model predicate would be the first of its kind there.

## One recorded cost of Option A that turned out not to exist

F67 part 4 argued A *"collides with **G3**, which is already scheduled to add a clause of its own"*, with both
clauses renumbering the same list and F49's positional prose as the hazard. **Measured, that collision is not
real:** G3's `reactionPrioritiesAbsent` is the tenth conjunct of `LF.GeneralProgram.wellFormed`, the *target*
predicate, while a divide-by-zero guard would join `DTR.GeneralModel.wellFormed`, the *source* predicate with
five. Two predicates, two sides of the translation, no shared list. This is finding **F88**, and it is recorded
because it argued **for** the option that was rejected: the ruling is made on the semantic mismatch above, not
on a renumbering cost that does not exist.

## Consequences

- `docs/supported-fragment-general.md`'s *"What this fragment excludes"* section states the restriction as
  **permanent and by decision**, and no longer says the guard *"is still owed (audit item C11)"*.
- The paper must state the restriction: the correctness result transfers to real target behaviour only on
  executions in which no division or modulo by zero occurs. It is a disclosed boundary in the same family as
  decision `0042`'s partial quotient and C7's three residues — part of the claim, not a caveat on it.
- No `lean-reject` fixture, no new diagnostic reason, no regression pin, and no gate total moves.
- `docs/claims/general-family-correctness.md` needs no new row: no claim changed. Row 20's fragment instrument
  continues to point at the fragment declaration, which now carries the ruling.
- **This does not license a quietly narrowed theorem.** No theorem statement moves, and none needed to: the
  model-side correspondence was already unconditional and two-sided before this decision.

## Scope

Applies to `.div` and `.mod` by zero in the general family's expression language. It rules on **where the
limitation is recorded**, not on the limitation itself, which is a property of C++ and is unchanged.

C7, C8, the α decisions, F27, `hConsumeAnswer`, the `GeneralInstantBlock` theorem shapes, `0042`'s quotient,
`0043`'s Option A and `0044`'s interface are all untouched. Nothing here reopens a closed decision.
