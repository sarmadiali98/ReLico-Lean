# Detailed forward weak simulation

Status: accepted

Date: 2026-07-26

## Purpose

This checkpoint proves the first concrete forward weak-simulation results for
the detailed finite-store, multiple-message-server semantic layer.

The proofs connect exact DTR detailed transitions to weak generated-LF
transitions while preserving the concrete detailed-state relation.

## Label correspondence

`ConcreteDetailedLabelCorresponds` relates:

- internal DTR statement execution to internal LF statement execution;
- DTR metric-time progression to LF metric-time progression;
- DTR message consumption to LF reaction firing.

For consumption, the relation records both:

- `PendingCorresponds` for the selected occurrence;
- exact equality with `Translation.compileMessageReaction` for the selected
  handler.

## Forward-match package

`ConcreteDetailedForwardMatch` packages:

- the matching generated-LF label;
- the resulting generated-LF detailed state;
- the generated-LF weak transition;
- detailed-label correspondence;
- preservation of concrete detailed-state correspondence.

## Internal statement execution

One DTR detailed statement transition is matched by one LF detailed statement
transition.

Both transitions are internal and use the detailed `tau` label.

The proof reuses `multiStore_step_forward` through the concrete wrapper
introduced in decision 0011.

## Future time progression

A future DTR dispatch first exposes a visible metric-time transition.

The conditional executable dispatch theorem constructs the corresponding LF
dispatch.

`StoreStateCorresponds.currentTime` proves equality of both time-transition
endpoints.

The destination states are related as:

```text
DTR dispatchReady
LF  afterTime
Consumption after future time progression

When the LF destination microstep is zero, LF fires the corresponding reaction
directly from afterTime.

When the destination microstep is positive, LF first performs:

microstepAdvance

This transition is internal.

The subsequent reaction firing is therefore a weak visible transition with an
internal prefix.

Consumption from dispatch-ready states

When both sides are dispatch-ready, DTR consumption is matched directly by LF
reaction firing.

The resulting stable states correspond through StoreStateCorresponds.

Same-time consumption

For a same-metric-time DTR dispatch, LF complete-tag monotonicity gives two
cases.

If the LF destination microstep is unchanged, LF fires directly.

If the destination microstep is later, LF performs an internal microstep
transition and then fires.

Both cases produce one weak visible consumption transition.

Scope

These are phase-local forward weak-simulation theorems covering every
detailed DTR constructor in its intended related phase.

This checkpoint does not yet define one unrestricted theorem over arbitrary
pairs admitted by the phase relation. Such a theorem requires an explicit
phase-coherence invariant preventing unrelated enabled transitions from being
combined across different dispatch witnesses.

The existing forward scheduler compatibility premise is retained.

Payload boundary

The detailed semantic layer still uses:

DTR.StoreState
LF.StoreState

Payload-aware and parameter-bound state machines are not covered by these
forward weak-simulation results.

Non-claims

This checkpoint does not prove:

backward weak simulation;
weak bisimulation;
observable finite-trace equivalence;
payload-aware weak simulation;
unrestricted zero-delay priority preservation;
unrestricted equal-priority preservation.
Next checkpoint

The next checkpoint proves the corresponding backward weak-simulation cases.

It will retain the established source-body well-formedness and
target-microstep-zero premises where required by the executable backward
theorems.
