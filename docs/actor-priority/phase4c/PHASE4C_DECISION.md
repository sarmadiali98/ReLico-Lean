# Phase 4C Actor-Priority Decision

## Final conclusion

**Conclusion 2 has been reached.**

When actor priority changes which actor is eligible to dispatch among
simultaneously ready actors, a faithful translation must preserve that
actor-ordering distinction.

## Formal result

The theorem proves that when two source observations differ, a translation
that preserves both observations must translate the two sources differently.

Equivalently, a translation that erases the distinction cannot preserve both
source behaviors.

## Concrete actor-priority instance

For `workera` and `workerb` at the same logical time:

- the base priority assignment selects `workera`;
- the reversed assignment selects `workerb`;
- complete priority erasure maps both assignments to the same target value;
- one target observation cannot equal both different source observations.

Therefore every faithful translation must distinguish the two assignments.

## Exact implementation requirement

A literal actor-priority field is not required.

The ordering may instead be represented by:

- precedence constraints;
- LF dependency edges;
- a coordinating scheduler;
- microstep ordering;
- any other behaviorally equivalent compiled mechanism.

## Priority-inert cases

Actor-priority information may be omitted when it is proved semantically
inert, including cases where:

- only one actor is eligible;
- actors are not simultaneously ready;
- priorities are tied;
- another causal constraint already forces the same order.

## Current ReLico status

The necessity theorem is proved in the isolated investigation layer.

Production DTR semantics, LF translation, and the correspondence theorem have
not yet been extended with the required actor-ordering mechanism.

## Next phase

**phase4d-integrate-actor-ordering-into-production-semantics-translation-and-proof**
