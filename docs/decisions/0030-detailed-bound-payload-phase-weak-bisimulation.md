# Detailed bound-payload phase weak bisimulation

Status: accepted

Date: 2026-07-27

## Problem

The detailed bound-payload development had established all individual forward
and backward weak-simulation matches.

A reusable theorem interface was still needed to collect these phase-indexed
obligations in one object.

## Decision

Introduce:

`DetailedBoundPayloadPhaseWeakBisimulation`

for one source payload message server and its generated LF payload reaction.

The structure contains exactly thirteen fields:

- five forward matches;
- eight backward matches.

The theorem:

`detailedBoundPayload_phaseWeakBisimulation`

constructs the structure directly from the previously proved single-transition
theorems.

## Forward obligations

The forward portion contains:

1. statement execution;
2. future metric-time advancement;
3. consumption immediately after time advancement;
4. consumption from dispatch-ready;
5. same-time immediate consumption.

Future and same-time dispatch reconstruction retain the existing
`BoundPayloadForwardDispatchCompatible` premise.

No compatibility premise is added to consumption from already-corresponding
dispatch phases.

## Backward obligations

The backward portion contains:

1. statement reconstruction;
2. future metric-time reconstruction;
3. LF microstep after future time advancement;
4. same-time LF microstep progression;
5. consumption after future time advancement at microstep zero;
6. future dispatch-ready consumption;
7. same-time dispatch-ready consumption;
8. direct same-tag consumption.

Generated-LF microstep transitions correspond to reflexive source weak-`tau`
transitions.

## Payload-aware guarantees

Every field uses:

- `DetailedBoundPayloadForwardMatch`, or
- `DetailedBoundPayloadBackwardMatch`.

Those match packages preserve:

- exact ordered payloads;
- selected occurrence identity;
- logical arrival time;
- activation-local parameter stores;
- translated active bodies;
- phase-indexed runtime-state correspondence.

## Interpretation

The structure is a phase-indexed weak-bisimulation interface for the verified
single-server payload fragment.

It is not a premise-free global coinductive bisimulation over arbitrary states.
Each field retains the exact compatibility and phase premises required by its
underlying executable theorem.

## Proof content

This checkpoint introduces no new semantic argument.

It packages the already established forward and backward theorems and provides
a stable interface for finite weak-execution lifting.

## Scope

This checkpoint does not yet prove:

- finite detailed weak-execution correspondence;
- observable-trace correspondence;
- canonical initial-state correspondence;
- public translator execution theorems;
- multiple payload message servers.
