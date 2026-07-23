# Decision 0005: Finite runtime store

## Status

Accepted as the foundation of the multiple-state-variable extension.

## Representation

The shared store abstraction is:

```lean
Relico.Store Key Value

It is represented as an ordered association list.

Lookup observes the first binding for a key. Update replaces that first
binding when present and appends a new binding when the key is absent.

Established properties

The initial store module proves:

lookup in the empty store returns no value;
lookup after updating the same key returns the new value;
updating one key preserves lookup at a distinct key;
a second update of the same key supersedes the first;
an updated key is present in the store.
Migration strategy

This commit does not change the existing v0 source state, LF state,
semantics, translation, or correctness theorems.

The migration will proceed incrementally:

introduce the generic finite store;
define declared-variable store well-formedness;
add store-based expression evaluation;
migrate source runtime states;
migrate LF runtime states;
migrate assignment semantics;
generalize state correspondence and simulation proofs;
extend syntax and the parser bridge to multiple declarations.

The tagged milestone-v0-end-to-end baseline remains unchanged.

## Store-based expression evaluation

The second migration checkpoint adds partial store-based evaluation for
both DTR and generated LF expressions:

```lean
DTR.Expr.evaluateStore
LF.Expr.evaluateStore

A variable reference evaluates through its VarName binding. Missing
bindings produce none.

The compiler preserves store-based evaluation for every finite store:

Correctness.compileExpr_preserves_store_evaluation

Compatibility theorems show that store evaluation agrees with the
original single-value evaluator on well-formed expressions and singleton
stores.

The original runtime-state representation and operational semantics
remain unchanged at this checkpoint.

## Declared-variable coverage

The third migration checkpoint introduces:

```lean
StateStore.Covers declaredVariables store

Coverage means that every declared variable has an observable integer
binding in the runtime store.

The development proves:

the empty declaration list is covered by every store;
a singleton store covers its singleton declaration;
coverage provides a concrete lookup result for each declaration;
assignment-style store updates preserve coverage;
coverage is preserved when restricting to a declaration subset.

At this checkpoint, coverage deliberately permits additional store
bindings. Exact correspondence between the declared-variable list and
the store domain will be introduced together with multiple-variable
model syntax.

The existing DTR and LF runtime states still use the original single
integer value.

## Store-backed runtime-state views

The fourth migration checkpoint introduces parallel store-backed
runtime-state structures:

```lean
DTR.StoreState
LF.StoreState

They replace the single integer runtime field with:

stateStore : StateStore

The existing DTR.State and LF.State structures remain unchanged, so
the established v0 operational semantics and proofs continue to build.

Each legacy state has an embedding into its store-backed form:

DTR.State.toStoreState
LF.State.toStoreState

A partial projection recovers a legacy state when the requested v0
variable has a store binding:

DTR.StoreState.toLegacyState
LF.StoreState.toLegacyState

Round-trip theorems establish that embedding and then projecting through
the same declared variable returns the original legacy state.

The embedded stores also satisfy singleton declared-variable coverage.

## Store-based statement semantics

The fifth migration checkpoint introduces parallel statement
transition relations:

DTR.StoreStep
LF.StoreStep

Both relations are parameterized by a list of declared state variables.

An assignment step requires:

- membership of the target in the declaration list;
- successful store-based evaluation of the expression.

The resulting state updates the target binding through
StateStore.update.

The development proves that every DTR and LF store step preserves
declared-variable coverage. Tests exercise cross-variable assignment:
one variable is read while another variable is updated.

Self-send and action-scheduling steps retain their existing queue and
logical-time behavior while leaving the state store unchanged.

The legacy DTR.Step and LF.Step relations remain unchanged.

## Forward store simulation

The sixth migration checkpoint introduces store-backed runtime
correspondence:

```lean
Correctness.StoreStateCorresponds

The relation preserves the complete finite store rather than one
integer state value. It also preserves logical time, pending event
occurrences, and compiled active bodies.

The theorem:

Correctness.store_step_forward

establishes forward one-step simulation for the store-based DTR and LF
statement semantics.

The assignment case uses:

Correctness.compileExpr_preserves_store_evaluation

Consequently, an assignment may read one declared state variable and
update another while retaining the same full source/target store.

The self-send case retains occurrence-preserving queue correspondence
and logical-time label correspondence.

This theorem is parameterized by a declaration list and therefore is
not restricted to a singleton runtime store.

## Declaration-list structural well-formedness

The seventh migration checkpoint introduces declaration-list
well-formedness predicates for DTR and generated LF expressions,
statements, and bodies:

```lean
DTR.Expr.StoreWellFormed
DTR.Stmt.StoreWellFormed
DTR.Body.StoreWellFormed

LF.Expr.StoreWellFormed
LF.Stmt.StoreWellFormed
LF.Body.StoreWellFormed

Variable references and assignment targets must occur in the complete
declaration list.

A store-well-formed expression evaluates successfully whenever the
runtime store covers that declaration list.

The compiler preserves these predicates:

Correctness.compileExpr_storeWellFormed
Correctness.compileStmt_storeWellFormed
Correctness.compileBody_storeWellFormed

Singleton compatibility theorems establish equivalence with the
original v0 structural predicates. The tagged v0 result therefore
remains a specialization of the generalized definitions.

## Backward store simulation

The eighth migration checkpoint introduces:

```lean
Correctness.store_step_backward

Every generated-LF store statement step from a corresponding runtime
state has a matching DTR store statement step.

The proof recovers the source statement through the existing compiled
body inversion lemmas. Assignment evaluation is transferred back
through store-based expression-evaluation preservation.

Source-body declaration-list well-formedness is used to establish that
a recovered self-send targets the declared message server.

The theorem preserves:

the complete finite state-variable store;
logical time;
occurrence-preserving pending-event correspondence;
transition-label correspondence;
compiled active-body correspondence.

Together with Correctness.store_step_forward, this establishes
two-directional one-step correspondence for the parallel store-based
statement semantics.

## Finite store traces

The ninth migration checkpoint introduces finite statement traces:

```lean
DTR.StoreTrace
LF.StoreTrace

Trace label sequences are related pointwise through:

Correctness.LabelTraceCorresponds

The development establishes:

Correctness.store_trace_forward
Correctness.store_trace_backward

Forward simulation lifts the one-step store theorem to arbitrary finite
DTR statement executions.

Backward simulation repeatedly applies the one-step backward theorem.
Source-body declaration-list well-formedness is preserved as each
recovered source statement is removed.

Both trace theorems preserve correspondence of:

the complete finite state-variable store;
logical time;
pending event occurrences;
active translated bodies;
every transition label in execution order.

These are statement-level traces. Dispatch and combined machine
execution remain to be generalized separately.

## Store-based dispatch

The tenth migration checkpoint introduces parallel dispatch relations:

```lean
DTR.StoreDispatchStep
LF.StoreDispatchStep

Dispatch preserves the complete finite state store while removing one
concrete earliest pending occurrence, advancing logical time or the LF
tag, and loading the source or generated message body.

Both dispatch relations preserve declared-variable store coverage.

The correctness layer establishes:

Correctness.store_dispatch_forward_of_compatible
Correctness.store_dispatch_backward

Forward dispatch remains conditional through:

Correctness.StoreForwardDispatchCompatible

The compatibility condition is required because LF microsteps refine
equal-logical-time scheduling choices.

Backward dispatch is unconditional once the source pending-event target
invariant is supplied. It recovers the source occurrence at the same
queue position, proves source earliest-time eligibility, and preserves
the complete finite store and residual queue correspondence.

The regression test dispatches a message whose body performs a
cross-variable assignment.
