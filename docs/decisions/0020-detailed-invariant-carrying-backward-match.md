# Detailed invariant-carrying backward matches

Status: accepted

Date: 2026-07-27

## Problem

The invariant-driven one-step matching theorems returned weak transitions and
state correspondence, but did not carry runtime invariants to the selected
destination states.

Finite chosen-match induction requires those invariants at every recursive
destination.

## Target exact-step preservation

`concreteDetailedTargetRuntimeInvariant_preserved` proves preservation of the
canonical generated-LF runtime invariant for one exact detailed transition.

Statement, time-advance, and direct-consumption transitions reuse preservation
of the underlying generated-LF machine invariant.

The canonical invariant excludes:

- positive microstep progression after metric-time advancement;
- same-time positive microstep progression;
- persistent target `dispatchReady` states.

These branches contradict current-microstep-zero preservation.

## Source weak-step preservation

`concreteDetailedSourceRuntimeInvariant_tauSteps` lifts the existing exact DTR
detailed-step preservation theorem to finite internal closures.

`concreteDetailedSourceRuntimeInvariant_weakStep` then covers both forms of
weak transition:

- a pure internal closure;
- an internal prefix, one visible exact step, and an internal suffix.

The theorem requires structural well-formedness and positive-delay timing for
every declared message-server body.

## Backward invariant match

`ConcreteDetailedBackwardInvariantMatch` extends the existing backward match
package with:

- final detailed state correspondence;
- the source runtime invariant at the selected source destination;
- the target runtime invariant at the exact generated-LF destination.

`concreteDetailedBackwardInvariantMatch` obtains the chosen source weak match
from the existing invariant-driven backward theorem and derives both final
invariants using the new preservation results.

## Scope

This result covers the backward one-step direction.

The forward direction remains separate because its chosen generated-LF weak
transition may contain hidden internal transitions. Its target destination
invariant must be established from the concrete canonical match construction,
not merely from one exact target transition.
