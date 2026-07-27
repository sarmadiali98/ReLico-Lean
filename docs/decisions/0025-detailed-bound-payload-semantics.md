# Detailed bound-payload semantic foundation

Status: accepted

Date: 2026-07-27

## Problem

The completed detailed multi-store correctness layer is parameterless. It
operates over ordinary `DTR.StoreState` and `LF.StoreState` values and does not
retain payload equality or activation-local parameter environments.

The repository already contains a separate parameter-aware vertical fragment:

- bound-payload source and generated-LF states;
- payload-aware statement semantics;
- payload-binding dispatch semantics;
- forward and backward statement correspondence;
- forward and backward dispatch correspondence.

These components lacked a detailed semantic layer exposing time advancement,
microstep administration, and payload-bearing consumption separately.

## Architectural choice

The development adds a parallel detailed bound-payload layer rather than
generalizing the completed ordinary detailed semantics.

This avoids destabilizing the Phase H result and keeps the parameter-aware
fragment explicit.

The initial layer remains specialized to one payload message server and one
compiled payload reaction because the existing bound-payload statement and
dispatch semantics have that scope.

## Source detailed semantics

`DTR.DetailedBoundPayloadState` contains:

- stable bound-payload runtime states;
- dispatch-ready states carrying an embedded
  `DTR.BoundPayloadDispatchStep` witness.

`DTR.DetailedBoundPayloadStep` separates:

- internal statement execution;
- observable metric-time advancement;
- observable payload-bearing message consumption.

Future dispatches use separate time-advance and consumption transitions.
Same-time dispatches consume directly.

## Generated-LF detailed semantics

`LF.DetailedBoundPayloadState` contains:

- stable bound-payload runtime states;
- the intermediate phase after metric-time advancement;
- dispatch-ready states after any required microstep advancement.

`LF.DetailedBoundPayloadStep` separates:

- internal statement execution;
- observable metric-time advancement;
- internal LF microstep advancement;
- observable payload-bearing reaction consumption.

## Observable alphabet

Consumption observables retain:

- the message or generated action name;
- logical time;
- the complete ordered payload.

Payload retention is required because dispatch subsequently binds these values
positionally to formal parameters.

Source statement execution, generated-LF statement execution, and LF
microstep administration are erased from observable traces.

## Scope

This checkpoint introduces semantic types and finite exact execution
relations. It does not yet prove:

- detailed phase-state correspondence;
- detailed forward or backward weak simulation;
- finite weak-execution correspondence;
- initial-state or public-translator packaging;
- multiple payload message servers;
- payload-aware actor-level or global priority correctness.
