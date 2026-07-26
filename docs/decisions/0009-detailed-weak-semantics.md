# Detailed weak semantics

Status: accepted

Date: 2026-07-26

## Purpose

This checkpoint instantiates the generic weak-transition infrastructure for
the detailed DTR and generated-LF transition systems introduced in decision
0008.

It does not yet define a cross-language relation or prove simulation.

## DTR

`DTR.DetailedTauSteps` is the reflexive-transitive closure of internal
detailed DTR transitions.

`DTR.DetailedWeakStep` is the corresponding weak transition relation.

The development proves that exact detailed transitions embed into weak
transitions, internal paths collapse to weak internal transitions, statement
execution is weakly internal, and time progression and message consumption
remain visible.

## Generated LF

`LF.DetailedTauSteps` is the reflexive-transitive closure of internal
generated-LF transitions.

`LF.DetailedWeakStep` is the corresponding weak transition relation.

Reaction-body statements and pure LF microstep progression are internal.
Metric-time progression and reaction firing remain visible.

## Observable traces

The DTR observable projection retains time progression and message
consumption.

The generated-LF observable projection retains metric-time progression and
reaction firing while removing statement execution and microstep
administration.

Therefore:

```text
timeAdvance ; microstepAdvance ; consume

and:

timeAdvance ; consume

have the same observable projection.

This abstraction does not hide different message-consumption or
reaction-firing orders.

Scope

The zero-delay priority mismatch remains observable and outside unrestricted
priority preservation.

The positive-delay restriction for priority-sensitive execution
correspondence remains unchanged.

No claim is made for actor-level priority, global priority, or unrestricted
equal-priority ties.

Next checkpoint

The next checkpoint defines the detailed cross-language state relation for
stable states and intermediate dispatch phases.
