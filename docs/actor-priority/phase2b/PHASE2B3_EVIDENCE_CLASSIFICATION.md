# Phase 2B3 Evidence Classification

## Status

Phase 2 evidence collection is complete.

This phase freezes the evidence classification before either production
approach is implemented.

## A–G classifications

- Claim A — **OUTSIDE CURRENT FRAGMENT**: The published correspondence result is scoped to explicit actor-indexed steps with no actor-priority request.
- Claim B — **NOT YET PROVED**: Observed current frontend behavior excludes actor-priority annotations and preserves local priority.
- Claim C — **CONDITIONAL**: Actor priority belongs to the upstream Timed Rebeca/RMC surface but not to the current ReLico frontend fragment.
- Claim D — **YES**: Actor priority is behaviorally relevant for at least one simultaneous-actor Timed Rebeca model.
- Claim E — **NOT YET PROVED**: The corpus contains explicit priority-selection obligations.
- Claim F — **NOT YET PROVED**: Paper references relevant to scheduling and priority have been inventoried.
- Claim G — **CONDITIONAL**: The current LF encoding can be claimed faithful only for the no-actor-priority explicit actor-indexed fragment.

## Load-bearing conclusions

Actor priority is behaviorally relevant for at least one tested
simultaneous-actor model.

The current published correspondence theorem does not model actor-priority
selection.

The current production frontend rejects actor-priority annotations before
JSON generation.

The current LF encoding is defensible only for the no-actor-priority,
explicit actor-indexed fragment.

## What is not established

The evidence does not establish that:

- every Timed Rebeca model needs actor priority;
- current ReLico equivalence depends on actor priority;
- actor priority can be omitted from full Timed Rebeca support;
- the current target already implements equivalent actor scheduling;
- the paper’s complete scope has been reconciled;
- every priority-named benchmark concerns actor priority.

## Implementation decision gate

Approach A:
**READY TO IMPLEMENT**

Approach B:
**READY AFTER THE APPROACH A BASELINE**

Implementation order:

1. Approach A exclusion;
2. Approach B inclusion;
3. direct comparison of test, proof, and maintenance obligations;
4. final necessity decision.

## Benchmark obligations

Total registered benchmarks:
**57**

Published accepted tracked benchmarks:
**1/57**

Priority-selection registry obligations:
**9**

Each priority-named obligation remains explicitly marked for semantic-level
classification.

## Next phase

**phase3-approach-a-exclusion-implementation-and-permanent-tests**
