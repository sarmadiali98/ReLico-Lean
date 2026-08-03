# Phase 4D Production Integration Plan

## Starting point

Phase 4C proved that actor-ordering information must be preserved whenever
actor priority changes cross-actor selection.

The current production implementation does not yet contain that ordering
mechanism.

## Design decision

The existing actor-indexed dispatch relation remains unchanged.

A new actor-priority eligibility layer will constrain which actor-indexed
dispatches are globally permitted.

This avoids changing the meaning of existing chosen-dispatch theorems and
makes the additional scheduler-choice proof explicit.

## Integration surfaces

| ID | Layer | Missing capability | Planned module | Status |
|---|---|---|---|---|
| D1 | DTR source model | autonomous actor-level eligibility among simultaneously ready actors | `Relico/DTR/GlobalMultiStorePayloadActorPriority.lean` | planned |
| D2 | LF target model | compiled cross-actor ordering corresponding to source actor priority | `Relico/LF/GlobalMultiStorePayloadActorOrder.lean` | planned |
| D3 | translation | translation of actor-ordering information | `Relico/Translation/GlobalMultiStorePayloadActorPriority.lean` | planned |
| D4 | selection correctness | source/target cross-actor eligibility correspondence | `Relico/Correctness/GlobalMultiStorePayloadActorPriorityCorrespondence.lean` | planned |
| D5 | dispatch correctness | proof that the chosen actor is scheduler-eligible | `Relico/Correctness/GlobalMultiStorePayloadActorPriorityDispatch.lean` | planned |
| D6 | frontend | multi-actor actor-priority-bearing frontend model | `deferred until direct formal integration is stable` | deferred |
| D7 | tests | production source/target traces under actor ordering | `Relico/Tests/GlobalMultiStorePayloadActorPriority*.lean` | planned |
| D8 | final equivalence theorem | scheduler-choice correspondence for active actor-priority ordering | `new theorem; existing theorem remains unchanged` | planned |

## Implementation phases

| Phase | Name | Deliverable | Status |
|---|---|---|---|
| 4D0 | README and architecture | durable decision record, surface inventory, and implementation sequence | complete_after_this_run |
| 4D1 | source actor-priority semantics | production-layer source actor eligibility and actor-priority dispatch relation | next |
| 4D2 | target actor-order semantics | LF representation of equivalent cross-actor ordering | planned |
| 4D3 | translation | compile source priority assignment to target ordering | planned |
| 4D4 | selection correspondence | preservation and reflection of eligible actors | planned |
| 4D5 | dispatch correspondence | scheduler choice plus existing chosen-dispatch proof | planned |
| 4D6 | finite and weak behavior | trace-level theorem for actor-priority-bearing models | planned |
| 4D7 | benchmark and frontend | production benchmark and frontend extension or explicitly documented deferred frontend scope | planned |

## Phase 4D1 acceptance criteria

The source-semantics phase must provide:

1. an actor-priority assignment representation suitable for production use;
2. lookup semantics with lower natural number meaning higher priority;
3. simultaneous-ready actor representation;
4. eligibility that retains all actors tied at minimal priority;
5. absent priority metadata that imposes no additional ordering;
6. an explicit policy for incomplete assignments;
7. a dispatch relation that combines eligibility with the existing
   actor-indexed dispatch primitive;
8. base, reversed, tied, absent, incomplete, and inert tests;
9. no modification to the existing chosen-actor dispatch theorem;
10. a successful full baseline build.

## Phase 4D2 acceptance criteria

The target layer must represent equivalent ordering without presupposing a
literal priority field.

The representation must distinguish the base and reversed cases while
preserving ties and priority-inert behavior.

## Proof order

The correctness proof proceeds in this order:

1. source actor eligibility;
2. target actor eligibility;
3. translation preservation of actor ordering;
4. forward selection correspondence;
5. backward selection reflection;
6. scheduler-constrained dispatch correspondence;
7. finite-step lifting;
8. weak and observable trace correspondence.

## Non-regression requirements

Throughout Phase 4D:

- the original worktree remains untouched;
- existing actor-priority-excluded theorems remain valid;
- current parser rejection remains mechanically tested;
- production integration claims are made only after direct Lean tests;
- no staging, committing, or pushing occurs without a separate explicit step.

## Final completion condition

Phase 4D is complete only when a production theorem establishes bidirectional
behavioral correspondence for actor-priority-bearing multi-actor models, or
for a precisely declared subfragment with explicit remaining exclusions.

## Next phase

**phase4d1-source-global-actor-priority-semantics**
