# Actor-Priority Proof Impact

## Current proof boundary

The current global source and target step relations receive an explicit
actor index. They do not autonomously select an enabled actor.

Actor-priority scheduling is therefore not a hidden premise of the current
correspondence proof. It is absent from the modeled transition relation.

## Approach A: explicit exclusion

Approach A preserves the existing semantic theorem domain.

Expected proof work:

1. expose the no-actor-priority requirement as a named supported-fragment
   predicate;
2. connect frontend rejection to that predicate;
3. retain the theorem that every `some assignment` request is outside the
   fragment, including `some []`;
4. prove or mechanically test that no source-to-LF path bypasses the
   boundary;
5. add negative and positive-control benchmarks.

Expected theorem impact:

- no redesign of the current one-step relation;
- no actor scheduler added to source or target semantics;
- theorem statements may acquire clearer fragment hypotheses;
- existing one-step and finite-execution proofs should remain structurally
  reusable.

This is a low-to-moderate proof impact, but it must be verified rather than
assumed.

## Approach B: semantic inclusion

Approach B enlarges the modeled language.

Required semantic additions include:

1. actor-priority assignments in the frontend and decoded AST;
2. a defined ordering convention and validation rules;
3. enabled-actor computation;
4. priority-based selection among simultaneous actors;
5. treatment of ties, absent assignments, partial assignments, and invalid
   assignments;
6. interaction with local message-server priority;
7. source-state or scheduler-state additions where required;
8. a faithful target representation or an equivalent LF scheduling
   mechanism.

Required correspondence work includes:

1. a priority-aware source one-step relation;
2. a priority-aware target one-step relation;
3. translation invariants for actor identity and priority assignment;
4. preservation of the selected actor;
5. one-step soundness and completeness;
6. finite-execution correspondence;
7. trace-order preservation against the RMC witness;
8. regression proofs for the no-priority fragment.

This is a high proof impact because actor selection becomes semantic rather
than externally supplied.

## Key proof distinction

Approach A proves that the existing theorem is intentionally restricted.

Approach B attempts to prove equivalence for a strictly larger transition
system.

Passing Approach A does not make Approach B unnecessary.

Passing Approach B does not invalidate Approach A; the exclusion path
remains a defensible smaller supported profile.

## Decision criterion

The final engineering decision must compare:

- semantic fidelity;
- theorem complexity;
- frontend and target implementation cost;
- benchmark coverage;
- diagnostic quality;
- maintainability;
- compatibility with the paper’s stated scope.

No final necessity claim is made before both approaches are implemented and
tested.
