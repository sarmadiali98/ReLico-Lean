# Stage I: local variable declarations in the general fragment

Status: **APPROVED 2026-09-04, implemented S-I1 through S-I6, landed through `3efe334`**

Decision: **a local variable is a statement, a third kind of name in an existing flat store, read
through the existing `.parameterVar` constructor and assigned through the widened `assign` check.**
No new runtime environment, no store extension, no new expression constructor, no new correspondence
conjunct, and `DTR.GeneralModel.wellFormed` keeps its five clauses.

Decision: **five rulings, recorded here in full with the alternatives that were weighed.** They were
decided before implementation began, on a design analysis that validated the corpus census and read
every affected layer, and they held unchanged through six milestones. A later contributor is
entitled to see not only what was chosen but what was declined, because four of the five had a
cheaper-looking alternative.

Decision: **this record authorizes the landed design.** It is written after the fact, as the
as-implemented record of rulings that were made before the fact; where the implementation taught
something the ruling did not anticipate, the finding (`docs/STAGE_I_FINDINGS.md` F91), not this
record, is where the surprise lives.

## 1. Context

The 49-model Rebeca corpus census (recorded in `RELICO_AGENT_HANDOFF.md`, 2026-09-04) measured nine
models containing local variable declarations — and measured that **zero** models are unlocked by
locals alone: every one of the nine also needs `sender`, arrays, `while`, `deadline` or `env`.
Local declarations were therefore justified as a prerequisite the corpus needs in combination, not
as a delivery, and the stage was sequenced after the work that did move coverage — stage I0's
acceptance of conditionals, which took the fragment from 8 to 31 of 49 models.

The design constraint was set by the existing architecture: `DTR.GeneralActorRuntime`'s valuation
is a flat `Store VarName DTR.GeneralValue` that already holds state variables and bound message
parameters **indistinguishably** — `DTR.GeneralExpr.evaluate` resolves `.stateVar` and
`.parameterVar` through the same lookup, and `bindParameters` implements the paper's `e_x ∪ v⃗` as a
`Store.update` on that same store, never unbinding. The whole stage design follows from taking that
flatness as the thing to preserve rather than the thing to fix.

## 2. The five rulings

### Ruling 1: local reads are `.parameterVar`

**Decision:** a local variable is read through the existing `.parameterVar` constructor on both
sides. No `.localVar` expression constructor exists.

**Why:** the argument is about the target, not about cost. `renderGeneralParameterRead` in
`Relico/LF/GeneralCppPrinter.lean` emits, per source parameter, a block-scoped C++ binding under
the source name, so in the generated reaction body a parameter and a local are the same thing — a
declaration and a read of a bare identifier. A `.localVar` constructor would introduce a
source-level distinction the target does not make, which is the kind of divergence this development
exists to avoid. The constructor's meaning widens to **"a name that is not a reactor state
variable"**, and both `GeneralExpr` docstrings say so as of S-I7.

**The alternative declined:** a dedicated `.localVar`, costing arms in `compileGeneralExpr`,
`compileGeneralExpr_preserves_evaluation`, `renderGeneralExpr`, both `evaluate`s and both guards,
while still needing the LF scope threading — more work, and a distinction the emitted C++ cannot
express. The one scenario that would have favoured it, a future value-level `sender`
representation needing to tell a payload name from a local name, was judged unlikely because
`sender` is a per-message datum rather than a scope entry.

### Ruling 2: scope enforcement stays in the frontend elaborator

**Decision:** name scope is checked in `Relico/Frontend/GeneralElaborator.lean` and nowhere else in
Lean. `GeneralScope` gained a third `locals` list; `resolveVariable` gained a third branch; the
`"declare"` arm performs the shadowing check; `elaborateBody` became the scope-threading walk. No
scope-tracking clause was added to `DTR.GeneralModel.wellFormed`.

**Why:** the boundary was already drawn and documented. `namesUniqueAndValid`'s own docstring says
parameter and state-variable names are "deliberately absent: their uniqueness is what makes a scope
unambiguous, which is the elaborator's concern and is reported as a diagnostic there." Locals are
scope-only names, exactly like those two, and mirroring the check in Lean would have conflicted
with the standing five-clause constraint on `wellFormed`.

**The recorded cost, not hidden:** no Lean predicate refuses a hand-built ill-scoped `GeneralModel`,
and the flat-store soundness argument leans on an elaborator refusal that
`docs/STAGE_E_FINDINGS.md` already called untested. Stage I widened that reliance; F90 and the
ruling both say so.

### Ruling 3: local shadowing is rejected

**Decision:** a local declaration whose name is already in scope — as a state variable, a formal
parameter, or a live local of the same body — is refused, by the new `localShadowsDeclaredName`
diagnostic, mirroring the exporter's own shadowing checks on a `for` counter.

**Why:** the flat store physically cannot hold two bindings of one name, so admitting shadowing
means a scope-indexed store, which means a scope-aware `GeneralValuationAgrees`, which means
reproving every evaluation-agreement theorem. **Measured corpus cost of refusing: zero** — no local
in the 49 models shares a name with a state variable of the same file. Rejecting also keeps the
emitted C++ free of a source-level shadow of a parameter binder, and keeps the three scope lists
disjoint, which is what `resolveVariable`'s order-independence argument leans on.

**The future constraint recorded with it:** refusing shadowing constrains a future `for` unroller —
unrolling a body that declares a local produces N declarations of one name — so an unroller must
rename per iteration or treat each copy as its own scope. Deciding this at design time cost nothing;
discovering it after landing would have cost a scope-rule redesign.

### Ruling 4: an omitted initialiser takes `GeneralType.initialValue`

**Decision:** the AST constructor requires an initialiser by construction; the elaborator applies
the declared type's `initialValue` when the source omits one, exactly as it already applies the
zero default for an absent `after`.

**Why:** state variables already take their initial values from the same `initialValue`, and
`typeOf_initialValue` already proves the default has the declared type, so diverging for locals
would be an unexplained inconsistency between two kinds of declaration in one language. The census
measured 9 of 38 corpus declarations omitting an initialiser, and measured that all nine are
assigned before any read — the yarn `boolean deadline_miss;` idiom assigns in both branches — so
the default changes no model's behaviour. The more conservative alternative, refusing the bare
form, was defensible and was declined for the consistency argument alone.

### Ruling 5: stage I0 runs before local declarations

**Decision:** the milestone that accepted `if`/`else` in the frontend (`if` elaboration, nested-body
recursion, the two well-formedness arms) landed before any local-declaration work.

**Why:** I0 moved fragment coverage from 8 to 31 of 49 models while locals moved it by zero, and
the two changes to `elaborateBody` are separable — `"if"` needs the nested-body recursion but not
the scope-threading fold, so doing I0 first let locals inherit a working recursion instead of
introducing a recursion and a fold at once. It also decoupled I0 from four of the five rulings
above, allowing it to start while they were still open.

## 3. The milestone sequence that implemented these rulings

S-I1 the source constructor with refusals; S-I2 the target constructor, guard arm and printer arm;
S-I3 the translation with the head equation; S-I4a the LF step rule; S-I4b the DTR step rule and
`generalLocalDecl_forward` with the seventh τ case; S-I5 the elaborator acceptance, the guard
widening and the `locals` fixture; S-I6 the exporter widening, the fixture move and the `lfc`
witness; S-I7 this documentation. Each milestone landed as a measured-green commit, in the order
the stage H landing had validated: the translator compiles a construct **before** any guard admits
it, because admitting first is the shape that once made `exists_compileGeneralBody` false.

## 4. What the design did not need, and why that is the finding

No new runtime field: the state a declaration touches predates the constructor. No store extension:
`Store.update` replaces in place, so a re-executed declaration reuses its slot and the valuation
never grows. No new correspondence conjunct: `GeneralValuationAgrees` is total over names and
already preserved by `generalValuationAgrees_update`, which is why `generalLocalDecl_forward` is
`generalAssign_forward` with a different head. No `0046` path change: a declaration occupies a
statement position and shifts later ordinals, which the existing index arithmetic already handles.

The scope rule — a declaration is live for the rest of its body, a branch-local dies with its
branch — is enforced identically in three independent layers (the elaborator's threading, the
Python validator's depth discard, the exporter's `renderBranch` snapshot), none of which consult
the others. That redundancy is deliberate: each layer was written against the same ruling, and the
S-I6 witness's discovery of the `reactionWellFormed` duplication (F91) is the counterexample that
proves why the redundancy is worth its cost — the one traversal that *was* allowed to drift did.
