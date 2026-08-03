# Phase 4D5C Dispatch Correspondence

## Result

**DISPATCH_CORRESPONDENCE_PRODUCTION_INSTALLED**

The source actor-priority wrapper and compiled target actor-order wrapper now
have production one-step dispatch correspondence.

## Production theorem package

1. `actorPriorityDispatchStep_forward_of_targetBase` — transport source eligibility and pair it with a matching target base dispatch.
2. `actorOrderDispatchStep_backward_of_sourceBase` — transport target eligibility and pair it with a reconstructed source base dispatch.
3. `synchronizedActorPriorityDispatch_forward` — forward one-step actor-priority dispatch correspondence.
4. `synchronizedActorPriorityDispatch_backward` — backward one-step actor-order dispatch correspondence.

## Regression repair

The failed untyped theorem aliases were replaced with direct root-qualified
`#check` assertions. This validates each theorem's exported API without asking
Lean to synthesize unconstrained implicit arguments.

## Validation

- Production theorems: **4/4 elaborated**
- Regression API checks: **4/4 passed**
- Full `lake build`: **passed**
- `sorryAx`: **absent**
- Original repository mutation: **none**
- Staging, commit, and push: **none**

The theorem package may depend on Lean's standard `propext` and `Quot.sound`
axioms. It has no admitted theorem dependency.

## Scope

One-step actor-priority dispatch correspondence is complete.

Finite execution correspondence, frontend integration, and final
actor-priority-bearing equivalence remain incomplete.

## Progress

- Before: **70%**
- After: **74%**
- Remaining: **26%**

## Next phase

**phase4d6a-finite-execution-correspondence-interface-audit**
