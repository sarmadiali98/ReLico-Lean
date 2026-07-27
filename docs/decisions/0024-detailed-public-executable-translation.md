# Public detailed executable translation correctness

Status: accepted

Date: 2026-07-27

## Problem

The detailed finite weak-execution theorems were stated for
`Translation.translateMultiStoreCore model`.

The paper-facing interface must instead apply to the program returned by the
public executable translator:

```text
Translation.translateMultiStore model = .ok program
Packaging choice

The project exposes two public theorems:

translateMultiStore_initialDetailedSteps_forward;
translateMultiStore_initialDetailedSteps_backward.

This follows the established public executable-translation API used by the
existing machine-level multi-store correctness results.

A new bundled structure is unnecessary because the two directions quantify
over different exact executions, labels, and destination states.

Public translation bridge

The public translator currently returns:

.ok (Translation.translateMultiStoreCore model)

Each theorem derives:

Translation.translateMultiStoreCore model = program

from the successful translation equation, substitutes the returned program,
and invokes the corresponding initial finite weak-execution theorem.

Forward result

For every exact finite DTR detailed execution beginning at constructor entry,
the returned generated-LF program has a selected finite weak execution
beginning at startup entry.

The theorem returns:

representative-label correspondence;
final detailed-state correspondence;
observable-trace correspondence;
the final source runtime invariant;
the final target runtime invariant.
Backward result

For every exact finite generated-LF detailed execution beginning at startup
entry, there is a selected finite DTR weak execution beginning at constructor
entry.

The theorem returns the same correspondence and invariant package.

Paper-facing interpretation

Within the verified fragment, every finite exact execution selected on either
side has a finite weak match on the other side with corresponding paper-level
observables.

This is a bidirectional finite weak-execution correspondence result.

It is not stated as equality of raw exact-execution trace sets. The construction
starts from an exact execution in one semantics and returns a weak execution in
the other semantics. No weak-to-exact flattening theorem is currently part of
the development.

Assumptions and scope

Both public theorems require:

DTR.MultiStoreModel.WellFormed model;
DTR.MultiStoreModel.PriorityTimingWellFormed model;
successful execution of the public translator.

The result covers the current parameterless, one-actor, finite-store,
multiple-message-server fragment with strictly positive self-send delays and
priority-sensitive dispatch.

It does not establish:

payload-aware detailed correspondence;
zero-delay priority-sensitive correctness;
equality of equal-priority execution spaces;
actor-level or global priorities;
complete multi-actor semantics;
correctness of downstream C++ generation or deployment.
