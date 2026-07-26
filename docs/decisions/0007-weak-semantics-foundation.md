# Weak-semantics foundation and semantic layers

Status: accepted

Date: 2026-07-26

## Purpose

The paper-level correctness result is weak bisimulation. The existing Lean
development does not yet mechanize that theorem.

The current DTR and generated-LF machine relations are retained as an
executable abstract or macro-step semantic layer. Existing one-step forward,
one-step backward, queue-correspondence, state-correspondence, and pointwise
trace theorems remain valid results about that layer.

They are not, by themselves, the final paper-level weak-bisimulation theorem.

## Semantic layers

The development will distinguish two layers.

### Executable macro layer

The current machine relations combine operations that may later be separated
in the detailed semantics.

In particular, dispatch currently:

- selects and removes a pending occurrence;
- advances logical time or the LF tag;
- loads the selected message-server or reaction body.

Current finite trace correspondence pairs these macro transitions
pointwise.

These definitions and proofs remain available for execution, regression
testing, and refinement lemmas.

### Detailed paper layer

The detailed layer will expose the transition granularity required by the
paper.

Its observable alphabet will be defined explicitly. The intended observable
classes are:

- message consumption or reaction firing;
- logical-time progression.

The intended internal classes include:

- assignments and local statement execution;
- send and schedule statement execution;
- payload evaluation and parameter binding;
- scheduler administration;
- LF microstep administration.

The exact classification remains subject to comparison with the final paper
SOS before the DTR- and LF-specific weak semantics are introduced.

## Generic infrastructure

`Relico.Common.WeakTransition` provides semantics-independent definitions for:

- reflexive-transitive internal closure through `TauSteps`;
- weak internal transitions through `WeakTauStep`;
- weak visible and internal transitions through `WeakStep`;
- raw-trace projection through `observableProjection`.

This checkpoint does not instantiate those definitions for DTR or LF.

It therefore makes no new behavioral-equivalence claim.

## Existing correspondence results

Current direct correspondence theorems will be reused as one or more of:

- exact executable-step correspondence lemmas;
- macro-step refinement lemmas;
- central visible-transition lemmas inside weak transitions;
- queue, state, payload, and parameter preservation lemmas.

Current pointwise trace relations will be described as macro-trace
correspondence. Final paper-level results will compare observable projections
rather than require equal raw trace lengths.

## Priority and timing scope

The verified priority-sensitive fragment supports local message-server
priority.

Actor-instance priority and global cross-actor priority are outside the
verified core.

The positive-delay restriction remains in force for local-priority execution
correspondence. The zero-delay priority mismatch is recorded in decision 0006
and in `Relico.Tests.ZeroDelayPriorityMismatch`.

Weak bisimulation does not remove that observable scheduling mismatch.

Zero-delay scheduling remains supported by the general semantics when no
priority-preservation claim requiring same-time overtaking is made.

## Equal-priority ties

Stable priority normalization currently retains declaration order for equal
explicit priorities and unannotated message servers.

No unrestricted execution-space result for equal-priority ties is claimed.
The final supported fragment must state and enforce a precise tie policy.

## Next steps

The next semantic checkpoints are:

1. define DTR and LF observable-label projections;
2. introduce detailed time-progression and consumption transitions;
3. prove refinement between the current macro semantics and the detailed
   semantics;
4. define the weak state relation;
5. prove forward and backward weak simulation;
6. derive weak bisimulation and observable trace correspondence.
