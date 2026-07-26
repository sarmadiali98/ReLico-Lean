# Detailed invariant-carrying forward matches

Status: accepted

Date: 2026-07-27

## Problem

The invariant-driven forward matching theorem selected a corresponding
generated-LF weak transition, but its result did not retain the source and
target runtime invariants at the selected destination.

Finite chosen-match induction requires those destination invariants.

Generic target weak-step preservation is insufficient for this direction
because the earlier forward theorem admitted administrative microstep paths
that are outside the canonical positive-delay priority fragment.

## Canonical construction

`concreteDetailedForwardInvariantMatch` constructs the generated-LF match
directly for each exact DTR detailed transition.

The result packages:

- a selected generated-LF detailed label;
- a selected generated-LF destination;
- the generated-LF weak transition;
- detailed label correspondence;
- detailed destination-state correspondence;
- the source runtime invariant at the DTR destination;
- the target runtime invariant at the LF destination.

## Statement transition

A DTR internal statement is matched by the exact translated LF statement
transition.

The destination is stable on both sides. Existing exact source and target
invariant-preservation theorems establish the destination invariants.

## Future metric-time transition

A DTR future dispatch is matched by one exact LF time-advance transition.

The target destination is the canonical `afterTime` phase. The priority
runtime invariant proves that the selected generated action has microstep
zero, so no positive-microstep phase is required.

## Future consumption

Consumption from a DTR dispatch-ready state corresponding to LF `afterTime`
uses `consumeAfterTimeZero` directly.

The target invariant supplies the required zero-microstep equation. The LF
destination is stable and carries the same underlying priority runtime
invariant.

A persistent LF `dispatchReady` configuration is impossible under the
canonical target invariant.

## Same-time consumption

A same-metric-time DTR dispatch is matched by direct LF `consumeNow`.

The target runtime invariant gives current microstep zero. Preservation of
current-microstep zero across the generated dispatch gives destination
microstep zero. Therefore both LF tags have the same microstep, eliminating
the administrative same-time microstep branch.

## Scope

This theorem is restricted to the canonical positive-delay,
priority-sensitive runtime fragment.

It does not claim that arbitrary generated-LF weak transitions preserve the
canonical target invariant. It selects the canonical corresponding transition
constructed from the executable translation correctness theorems.
