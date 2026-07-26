# Detailed backward weak simulation

Status: accepted

Date: 2026-07-26

## Purpose

This checkpoint proves phase-local backward weak-simulation matches for the
detailed finite-store, multiple-message-server semantic layer.

Each generated-LF detailed phase is reconstructed by a DTR weak transition
while preserving concrete detailed-state correspondence.

## Shared label relation

`ConcreteDetailedLabelCorresponds` now includes:

```text
DTR tau
LF microstepAdvance

This records that pure LF microstep progression is internal and may be matched
by DTR stuttering.

The existing statement, time-advance, and consumption constructors remain
unchanged.

Backward-match proposition

ConcreteDetailedBackwardMatch packages:

the matching DTR detailed label;
the DTR destination state;
the DTR weak transition;
shared detailed-label correspondence;
preservation of concrete detailed-state correspondence.
Statement reconstruction

One LF statement transition reconstructs one DTR statement transition.

The proof reuses concreteDetailed_statement_backward and retains the source
body well-formedness premise.

Metric-time reconstruction

An LF future metric-time transition reconstructs a DTR future dispatch and
visible DTR time advancement.

StoreStateCorresponds.currentTime identifies both visible time endpoints.

The established PendingMicrostepsZero premise is retained.

LF microstep stuttering

A future microstepAfterTime transition is matched by a reflexive DTR weak-τ
step while DTR remains dispatch-ready.

A same-time microstepSameTime transition is also matched by DTR stuttering.
The source dispatch is first reconstructed from the LF macro dispatch.

The same-time reconstruction retains PendingMicrostepsZero.

Consumption reconstruction

The checkpoint covers three phase forms:

consumption directly from afterTime at destination microstep zero;
consumption from future dispatch-ready states;
consumption from same-time dispatch-ready states.

The first two reconstruct DTR.consumeReady.

The same-time dispatch-ready case reconstructs DTR.consumeNow.

Direct LF consumeNow from stable states is reconstructed separately through
the executable backward dispatch theorem.

Conditionality

The backward executable dispatch theorem requires:

LF.StoreState.PendingMicrostepsZero targetBefore

This premise remains explicit for:

visible LF time advancement reconstructed from stable states;
same-time LF microstep advancement reconstructed from stable states;
direct LF consumption reconstructed from stable states.

The checkpoint does not claim unrestricted backward simulation beyond that
established scheduler premise.

Scope

The results are phase-local. They cover every generated-LF detailed
constructor in each state relation phase admitted by
ConcreteDetailedStateCorresponds.

They do not yet combine the forward and backward families into one
bisimulation record.

Payload boundary

The detailed semantic layer still uses:

DTR.StoreState
LF.StoreState

Payload-aware and parameter-bound machines remain outside this checkpoint.

Non-claims

This checkpoint does not prove:

unrestricted global backward simulation;
weak bisimulation;
observable finite-trace equivalence;
payload-aware weak simulation;
unrestricted zero-delay priority preservation;
unrestricted equal-priority preservation.
Next checkpoint

The next checkpoint packages the forward and backward phase-local results into
a concrete weak-bisimulation interface under their shared well-formedness,
scheduler-compatibility, and zero-microstep assumptions.
