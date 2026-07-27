# Detailed bound-payload weak-transition foundation

Status: accepted

Date: 2026-07-27

## Problem

The detailed bound-payload semantics introduced exact source and generated-LF
transitions, but weak simulation requires internal closure and weak labeled
steps.

Generated LF may perform a microstep transition that has no corresponding
source transition. This administrative transition must be abstracted as
internal behavior.

The correctness layer also requires a detailed label relation that preserves
the payload-bearing occurrence selected during consumption.

## Generic weak-transition machinery

The existing generic definitions are reused directly:

- `Common.TauSteps`;
- `Common.WeakStep`.

No new weak-transition kernel or duplicated closure relation is introduced.

Each language instantiates the generic machinery using:

- its detailed bound-payload transition relation;
- its detailed bound-payload `isTau` predicate.

## Source weak semantics

For DTR:

- statement execution is internal;
- time advancement is visible;
- payload-bearing message consumption is visible;
- every exact transition induces a weak transition;
- internal closure is reflexive and transitive.

## Generated-LF weak semantics

For generated LF:

- reaction-body statement execution is internal;
- microstep administration is internal;
- metric-time advancement is visible;
- payload-bearing reaction consumption is visible.

An exact LF microstep induces an internal closure and therefore a weak
transition labeled by canonical `tau`.

## Detailed label correspondence

`DetailedBoundPayloadLabelCorresponds` relates:

- source `tau` to target `tau`;
- source `tau` to an LF microstep label;
- equal metric-time advancement labels;
- payload-bearing consumption labels whose selected occurrences satisfy
  `PendingPayloadCorresponds`.

The consumption case preserves:

- translated action name;
- logical time;
- complete ordered payload.

## Internal-status preservation

Corresponding labels agree on whether they are internal. The LF microstep case
is related to source `tau`, so both sides remain internal under their respective
predicates.

## Scope

This checkpoint provides weak-transition and label-correspondence foundations
only. It does not yet prove:

- forward phase matches;
- backward phase matches;
- finite weak executions;
- observable-trace correspondence;
- initial-state or public translator theorems;
- multiple payload message servers.
