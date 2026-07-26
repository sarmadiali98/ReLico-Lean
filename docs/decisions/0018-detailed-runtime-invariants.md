# Phase-aware detailed runtime invariants

Status: accepted

Date: 2026-07-27

## Problem

The existing finite detailed execution theorem requires a recursively supplied
phase-compatibility predicate.

Machine-level invariant preservation is already available, but the detailed
states contain intermediate dispatch phases. A finite chosen-match induction
therefore needs invariants indexed by detailed states rather than only stable
machine states.

## Source invariant

`ConcreteDetailedSourceRuntimeInvariant` carries:

- multi-store runtime well-formedness;
- positive-delay priority timing of the active body.

For a stable state, these properties apply to the stored source state.

For a dispatch-ready state, they apply to the post-dispatch state whose message
has been removed and whose selected message-server body has been loaded.

## Target invariant

`ConcreteDetailedTargetRuntimeInvariant` carries the full generated-LF
`PriorityRuntimeInvariant`.

It applies to stable states and to the post-dispatch state stored in an
`afterTime` phase.

A canonical positive-delay priority execution excludes `dispatchReady`.
Generated pending actions have microstep zero, so future dispatch proceeds from
`afterTime` directly to visible consumption. Same-time dispatch consumes
directly from the stable state.

## Preservation

Every exact detailed DTR transition preserves the source invariant.

The proof reuses the established combined-machine preservation theorems for:

- source runtime well-formedness;
- source priority timing.

The `consumeReady` transition changes only the detailed wrapper and leaves the
underlying post-dispatch state unchanged.

## Next checkpoint

The following checkpoint must construct invariant-carrying chosen weak matches.

Those richer one-step matches will provide the recursive data required by the
finite induction without quantifying over unrelated weak transitions.
