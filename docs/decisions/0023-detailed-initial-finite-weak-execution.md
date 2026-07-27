# Detailed finite weak execution from initial states

Status: accepted

Date: 2026-07-27

## Problem

The invariant-carrying finite execution theorems required callers to provide:

- initial detailed-state correspondence;
- the initial source runtime invariant;
- the initial target runtime invariant;
- structural validity of every message-server body;
- positive-delay timing for every message-server body.

For translated model executions, these premises should follow from model
construction and model-level assumptions rather than remain explicit at every
call site.

## Initial detailed-state correspondence

`concreteDetailedInitialStates_correspond` lifts the existing store-level
initial-state theorem through the stable-state constructor of the detailed
semantics.

The DTR constructor-entry state corresponds to the generated-LF startup-entry
state produced by `translateMultiStoreCore`.

## Initial source runtime invariant

`concreteDetailedInitialSourceRuntimeInvariant` derives the source invariant
from:

- `DTR.MultiStoreModel.WellFormed`;
- `DTR.MultiStoreModel.PriorityTimingWellFormed`.

Structural well-formedness establishes runtime well-formedness of the initial
DTR state. The timing structure supplies positive-delay timing for the active
constructor body.

## Initial target runtime invariant

`concreteDetailedInitialTargetRuntimeInvariant` uses the generic generated-LF
initial-state theorem.

The initial LF tag has microstep zero and the pending-action queue is empty.

## Finite execution results

`concreteDetailedSteps_forward_from_initial` and
`concreteDetailedSteps_backward_from_initial` instantiate the chosen-match
finite execution theorems at canonical translated initial states.

The model-level structures directly discharge:

- initial state correspondence;
- source and target initial invariants;
- message-server body structural well-formedness;
- message-server body positive-delay timing.

The results retain:

- a selected weak execution;
- representative-label trace correspondence;
- final detailed-state correspondence;
- observable-trace correspondence;
- final source and target runtime invariants.

## Scope

The result applies to the current parameterless finite-store detailed
multi-store fragment and the canonical positive-delay priority-sensitive
runtime.

It does not establish:

- payload-aware detailed correspondence;
- zero-delay priority-sensitive correctness;
- equal-priority execution-space preservation;
- actor-level or global priorities;
- complete multi-actor support.

Packaging through the public translator result and execution-space-level
paper-facing statements remains a subsequent checkpoint.
