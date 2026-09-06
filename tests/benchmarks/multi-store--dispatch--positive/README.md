# `multi-store--dispatch--positive`

A **multi-store**-family positive benchmark for dispatch: two message servers rotate the finite store in turns, each dispatch reading what the previous one wrote.

## Provenance

### 1. Original purpose

This row carries the multi-store family's dispatch evidence: 152 obligations across `ConcreteDetailedStateCorrespondence`, `DetailedBackwardWeakSimulation`, `DetailedForwardWeakSimulation`, `DetailedMultiStoreSemantics`, `DetailedPriorityRuntimeInvariant`, `DetailedRuntimeInvariants`, `DetailedStateCorrespondence`, `DirectLFBackwardDispatchRuntime`, `DirectLFDetailedRuntimeStateCorrespondence`, `DirectLFForwardDispatchRuntime`, `LFPendingNotPast`, `MultiStoreDispatch`, `MultiStoreMachine`, `MultiStoreMachineTrace`, `PriorityDispatchScheduling`, `PriorityMachineTiming`, `ZeroDelayPriorityMismatch`.

### 2. Removed features and semantic changes

None. A purpose-written single-class source inside the multi-store fragment: one actor, multiple message servers, a finite store, no message parameters (parameters are the payload family's extension) and no delayed external sends.

### 3. New pipeline surface

This benchmark is the first through the multi-store Lean exporter arm (`Relico/Benchmark/MultiStoreArtifactExporter.lean`, mirroring the payload exporter) and the multi-store parser bridge (`run-multistore-from-zip.sh`, already in the tree). The exporter composes existing verified entry points -- `Relico.Frontend.decodeMultiStoreModelText`, `Relico.Translation.translateMultiStoreCore` and `Relico.Translation.translateMultiStoreToCppSource` -- and adds no new obligations.

### 4. Preserved behavioural property

A dispatch chain whose store state depends on the order of server execution: `x = y` in the first server, `y = x` in the second, so the state observed at each dispatch is the previous server's write.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family multi-store` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 152 obligations across the family's pre-existing proof modules;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
