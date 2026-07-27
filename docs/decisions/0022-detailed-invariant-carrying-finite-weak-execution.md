# Detailed invariant-carrying finite weak execution

Status: accepted

Date: 2026-07-27

## Problem

The existing finite detailed correspondence theorems recurse through universal
continuation-compatibility predicates.

Those predicates require the recursive theorem to hold for every possible weak
match that preserves labels and states. This is stronger than necessary and is
poorly suited to nondeterministic semantics.

The invariant-carrying one-step theorems now select one concrete matching weak
transition and return the source and target runtime invariants at its selected
destination.

## Forward finite induction

`concreteDetailedSteps_forward_chosen` performs induction over an exact finite
DTR detailed execution.

For every exact head transition, it invokes
`concreteDetailedForwardInvariantMatch`, obtaining:

- one selected generated-LF weak transition;
- one representative generated-LF label;
- destination-state correspondence;
- the source runtime invariant at the DTR destination;
- the target runtime invariant at the generated-LF destination.

The induction hypothesis is applied only to that selected destination.

The head and tail weak executions are combined with `Common.WeakSteps.cons`.
Representative labels are combined pointwise, and observable-trace
correspondence follows from `observableProjection`.

## Backward finite induction

`concreteDetailedSteps_backward_chosen` performs the symmetric induction over
an exact finite generated-LF detailed execution.

Each exact target transition is matched using
`concreteDetailedBackwardInvariantMatch`. The selected DTR destination and its
carried invariants are used directly for recursive continuation.

## Result

Both directions return:

- a selected finite weak execution;
- pointwise representative-label correspondence;
- final detailed-state correspondence;
- final source and target runtime invariants;
- observable-trace correspondence.

Neither theorem requires
`ConcreteDetailedForwardStepsCompatible` or
`ConcreteDetailedBackwardStepsCompatible`.

The older conditional finite theorems remain available as compatibility and
regression results.

## Scope

These theorems still assume:

- initial detailed-state correspondence;
- the initial source runtime invariant;
- the initial target runtime invariant;
- model-wide message-body well-formedness;
- model-wide positive-delay priority timing.

Initial-state discharge is a separate checkpoint.

The result applies only to the current parameterless finite-store detailed
multi-store fragment and does not establish payload-aware, zero-delay
priority-sensitive, equal-priority, or complete multi-actor weak
bisimulation.
