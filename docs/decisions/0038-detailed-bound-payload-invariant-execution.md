# Detailed bound-payload invariant-carrying finite weak execution

Status: accepted

Date: 2026-07-27

## Context

The preceding checkpoints established:

- positive-delay timing well-formedness for internal source payload self-sends;
- the corresponding generated-LF runtime invariant;
- runtime-invariant preservation across source and target statement and dispatch
  transitions;
- phase-aware source and target invariants;
- canonical forward phase alignment;
- automatic one-step forward phase compatibility.

The remaining problem was recursive finite forward simulation. The existing
finite theorem required `DetailedBoundPayloadForwardStepsCompatible`, a
universal continuation predicate quantified over every possible corresponding
weak-match endpoint.

That predicate is stronger than necessary. Forward correctness needs only one
selected generated-LF match whose endpoint carries enough information for the
next recursive source transition.

## Declared server-body timing premise

`DetailedBoundPayloadSourceRuntimeInvariant` constrains the active body stored
in the current detailed source state.

A dispatch transition loads `server.body`. Consequently, preservation across
future or same-time dispatch requires:

`DTR.BoundPayloadBody.PriorityTimingWellFormed server.body`.

This premise is retained for the one-step invariant package and finite
execution theorem.

## Source phase-invariant preservation

`detailedBoundPayloadSourceRuntimeInvariant_preserved` proves preservation
across every exact detailed source transition.

- Statement execution uses
  `boundPayloadStep_preserves_priorityTimingWellFormed`.
- Future dispatch uses
  `boundPayloadDispatch_establishes_priorityTimingWellFormed`.
- Consumption from `dispatchReady` reuses the invariant of the already
  activated post-dispatch body.
- Same-time dispatch again establishes the invariant from `server.body`.

## Invariant-carrying one-step package

`DetailedBoundPayloadForwardInvariantMatch` contains:

- one generated-LF detailed weak step;
- detailed label correspondence;
- detailed endpoint state correspondence;
- the source phase invariant at the source endpoint;
- the target phase invariant at the target endpoint;
- canonical forward phase alignment at the endpoint.

## Canonical one-step construction

`detailedBoundPayloadForwardInvariantMatch` constructs the package by cases on
the exact source detailed transition and current state correspondence.

### Statement

The runtime-level matched statement theorem supplies:

- target statement execution;
- endpoint state correspondence;
- source active-body timing preservation;
- target runtime-invariant preservation.

The endpoint is stable/stable and therefore canonical.

### Future dispatch

The runtime-level matched dispatch theorem supplies:

- the selected LF action;
- LF dispatch;
- selected occurrence correspondence;
- endpoint state correspondence;
- source server-body timing;
- target runtime-invariant preservation.

The detailed target endpoint is `afterTime`; the source endpoint is
`dispatchReady`. This is a canonical future endpoint.

### Consumption after future time

If the dispatched LF state has microstep zero, LF consumes directly.

If the microstep is positive, LF performs one internal microstep transition
before consumption. Both cases form a single weak visible consumption step and
end in stable/stable states.

The concrete runtime state does not change during these administrative
transitions, so the embedded target invariant is transported directly.

### Same-time consumption

The runtime-level matched dispatch theorem establishes the post-dispatch
invariants.

If the target microstep increases, the microstep transition is absorbed into
the internal prefix of the generated-LF weak consumption step.

If the complete target tag is unchanged, LF consumes directly.

Both selected matches end in stable/stable states and therefore restore
canonical recursive alignment.

## Finite chosen-match recursion

`detailedBoundPayloadSteps_forward_with_invariants` performs induction over the
exact finite source execution.

For each head source transition, it selects
`detailedBoundPayloadForwardInvariantMatch`. The package supplies:

- the target middle state;
- middle-state correspondence;
- both middle invariants;
- canonical middle phase alignment.

These properties are passed directly to the induction hypothesis.

The theorem does not require or mention
`DetailedBoundPayloadForwardStepsCompatible`.

## Trace preservation

Head and tail detailed weak-label correspondences are combined with
`DetailedBoundPayloadWeakLabelTraceCorresponds.cons`.

The complete observable trace result follows from the trace correspondence's
`observableProjection` theorem. Statement and microstep administration remain
erased, while metric-time advancement and payload-bearing consumption remain
corresponding observables.

## Scope

This checkpoint establishes unconditional finite forward weak execution from
a corresponding, invariant-satisfying, canonically aligned initial phase,
subject only to timing well-formedness of the declared payload server body.

It does not yet package the canonical initialization and invocation-entry
states as top-level end-to-end translation correctness theorems.
