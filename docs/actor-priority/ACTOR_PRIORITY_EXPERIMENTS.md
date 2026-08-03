# Actor-Priority Experiments

## Experimental question

The investigation distinguishes two questions:

1. whether actor priority participates in the current published ReLico
   correspondence theorem;
2. whether actor priority is behaviorally relevant in the broader Timed
   Rebeca/RMC language.

These questions have different answers.

## Current theorem and frontend

The current theorem layer contains no actor-priority scheduler and accepts
only the no-request boundary.

The current production parser bridge:

- accepts the no-actor-priority control;
- accepts and preserves local message-server priority;
- rejects valid integer main-actor priority annotations;
- emits no JSON or downstream artifact for rejected actor priorities.

This supports an exclusion architecture but does not yet complete it.

## Official RMC acceptance

Official RMC executed actor-priority models successfully.

Four official example families accepted:

- original actor priorities;
- reversed actor priorities;
- actor priorities absent.

Those examples changed generated implementation artifacts but did not
supply a semantic discriminator.

## Systematic semantic witness

A purpose-built simultaneous-actor model was then tested.

Only the first two worker actor-priority values changed between the base
and reversed models.

The canonical graph analysis established:

- base first worker dispatch: `workerA`;
- reversed first worker dispatch: `workerB`;
- base worker order language: `workerA → workerB`;
- reversed worker order language: `workerB → workerA`;
- both languages were stable over three executions;
- the languages were disjoint;
- base and reversed property verdicts were both `deadlock`.

Therefore actor priority changes reachable dispatch behavior in the tested
model even though the final property verdict does not change.

## Evidence hierarchy

The accepted evidence hierarchy is:

1. source-delta audit;
2. successful official RMC execution;
3. stable canonical transition graphs;
4. actor-labeled dispatch traces;
5. property verdict differences where present.

Generated-code differences and raw transcript hashes are not treated as
semantic proof.

## Current conclusion

Actor priority is behaviorally relevant for at least one simultaneous-actor
Timed Rebeca model.

The current ReLico theorem does not model actor-priority scheduling.

It is not defensible to claim that actor priority is globally unnecessary.

It is defensible to claim that the current theorem is scoped to a fragment
where actor-priority requests are absent.

## Implementation sequence

Approach A is implemented first to make that existing exclusion boundary
explicit and permanent.

Approach B is then implemented against the confirmed RMC trace witness to
measure the semantic, translation, and proof cost of inclusion.
