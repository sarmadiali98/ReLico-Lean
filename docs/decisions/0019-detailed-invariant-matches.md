# Invariant-driven detailed one-step matches

Status: accepted

Date: 2026-07-27

## Problem

The detailed phase weak-bisimulation package previously required explicit
phase-compatibility premises for every exact step.

Those premises are unsuitable for finite chosen-match induction because the
caller must repeatedly reconstruct scheduler, structural, and microstep facts.

## Forward derivation

`concreteDetailedForwardPhaseCompatible_of_runtimeInvariants` derives every
forward phase premise from:

- one exact detailed DTR transition;
- detailed state correspondence;
- the target detailed priority runtime invariant.

For stable dispatch states, the target invariant provides:

- current microstep zero;
- zero microsteps for all pending actions.

Together with stable-state correspondence, these facts discharge
`StoreForwardDispatchCompatible`.

The target invariant excludes noncanonical target `dispatchReady` states.

## Backward derivation

`concreteDetailedBackwardPhaseCompatible_of_runtimeInvariants` derives every
backward phase premise from:

- one exact detailed generated-LF transition;
- detailed state correspondence;
- the source detailed runtime invariant;
- the target detailed priority runtime invariant.

The source invariant provides active-body well-formedness.

The target invariant provides the pending-action zero-microstep property.

The two generated-LF microstep transitions are impossible in the canonical
positive-delay priority fragment:

- `microstepAfterTime` contradicts the invariant of the embedded post-dispatch
  state;
- `microstepSameTime` contradicts preservation of current microstep zero across
  the embedded dispatch.

A direct transition from target `dispatchReady` is also excluded by the
canonical target invariant.

## Chosen matches

The new forward and backward match theorems invoke the existing phase weak
bisimulation after deriving compatibility automatically.

They return one particular corresponding weak transition and destination.
They do not quantify over all possible weak matches.

This is the one-step interface required by the next finite chosen-match
induction checkpoint.
