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
