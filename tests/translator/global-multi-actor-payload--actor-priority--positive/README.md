# `global-multi-actor-payload--actor-priority--positive`

A **global-multi-actor-payload**-family positive benchmark for actor priority. Two feeders are ready in the same round and both deliver to one collector; instance-level `@priority` decides which actor the scheduler selects first, and the collector's `last` records who was consumed most recently.

## Provenance

### 1. Original purpose

The row exists to carry this family's actor-selection evidence: 211 obligations across `ActorPriorityErasureImpossibility`, `ActorPriorityIsolatedScheduler`, `GlobalMultiStorePayloadActorDispatchCorrespondence`, `GlobalMultiStorePayloadActorFiniteExecution`, `GlobalMultiStorePayloadActorObservableProjection`, `GlobalMultiStorePayloadActorOrder`, `GlobalMultiStorePayloadActorOrderTranslation`, `GlobalMultiStorePayloadActorPriority`, `GlobalMultiStorePayloadActorPriorityBoundary`, `GlobalMultiStorePayloadActorSelectionCorrespondence`, `GlobalMultiStorePayloadFrontend`, the actor-order, actor-priority and selection-correspondence development of the global multi-store-payload family.

### 2. Removed features

None. This is a purpose-written source; its closest structural ancestor is the upstream CSMA idea of actors racing a shared sink, reduced to the fragment the way the tcsma-inspired general-family benchmark established.

### 3. Semantic changes made

One, forced by measurement: an earlier draft re-armed each feeder on its own timer, and RMC reported `queue overflow` because a starved collector cannot stop timer-driven producers at any bound. In this source each feeder re-arms only on the acknowledgement of its own delivery, so at most one unacknowledged message per feeder exists.

### 4. Preserved behavioural property

Two simultaneously-ready actors ranked by instance priority, with the resulting delivery order observable in the collector's state. Distinct from `general--actor-priority--positive`: no medium, no arbitration protocol, a different topology, and this family's own evidence modules.

## Stages

8 stages, terminal `lfc`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`.

The five gmap-family rows re-polarized in stage K run the same shape: `parser-json` through the `--family general` arm, with this family's Lean obligations carried by the formal witness. The dedicated gmap stage tool is pinned to the external-send model surface and is not used by this benchmark.

## Evidence

- source: two prioritized feeders and one collector, both priorities present in the decoded AST (`priority := some 1`, `priority := some 2`);
- RMC: `satisfied`;
- formal witness: 211 obligations;
- lfc: the generated LF compiles under `lfc 0.11.0`.

## Keep-alive

Recurrence is acknowledgement-coupled, so every producer is gated by its own consumption.
