# Full target priority runtime invariant

Status: accepted

Date: 2026-07-27

## Problem

The existing generated-LF timing invariant,

```text
LF.StoreState.PendingMicrostepsZero

constrains only queued action occurrences.

That is sufficient for backward dispatch reconstruction and for transporting
source earliest-time selection to target earliest-tag selection. It is not
sufficient to derive the complete forward scheduler premise.

StoreForwardDispatchCompatible also requires:

LF.Tag.PrecedesOrEqual
  targetState.currentTag
  selectedAction.tag

When the metric times are equal and every queued action is at microstep zero,
this obligation additionally requires the current LF tag to be at microstep
zero.

Decision

Introduce:

LF.StoreState.PriorityRuntimeInvariant

with two fields:

current tag microstep zero;
every queued action microstep zero.
Initialization

Every generated multi-store program begins at the initial tag and with an
empty action queue, so the full invariant holds immediately.

Preservation

Generated statement steps leave the current tag unchanged.

Generated dispatch steps set the current tag to the selected queued action.
The selected occurrence belongs to the pre-state queue, so its microstep is
zero under the queue invariant.

Queued-action preservation continues to use the established positive-delay
timing theorem.

Forward dispatch consequence

A source dispatch and stable state correspondence now derive
StoreForwardDispatchCompatible automatically.

The proof uses:

occurrence-preserving queue removal;
source priority eligibility;
source-earliest to target-earliest transport under zero microsteps;
source not-past logical-time order;
current and selected target microstep zero at equal metric time.
Detailed consequence

The scheduler premises for detailed source timeAdvance and same-time
consume phases are derived from the full target invariant.

Remaining issue

This checkpoint does not yet derive the recursive finite compatibility
predicate from H2H-B1.

That predicate quantifies over every possible weak matching transition,
including unrelated internal LF microstep transitions. H2H-B2B must replace
or refine that universal continuation with a chosen-match execution strategy
before model invariants can yield an unconditional finite theorem.
