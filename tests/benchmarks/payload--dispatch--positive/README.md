# `payload--dispatch--positive`

A **payload**-family positive benchmark for dispatch: one message server swaps the store's carried payload with the next one on every dispatch.

## Provenance

### 1. Original purpose

This row carries the payload family's dispatch evidence: 46 obligations across `DirectLFPayloadDetailedRuntimeLabelCorrespondence`, `DirectLFPayloadRuntimeDispatch`, `PayloadDispatchQueue`.

### 2. Removed features and semantic changes

None. A purpose-written source inside the store fragment, the narrowest family: one actor, one message server, a finite store. The v0 `MessageServer` carries no parameters, so the payload is bound in the store rather than carried by the message -- this family's payload binding, distinct from the bound-payload family's message-carried payloads.

### 3. New pipeline surface

This benchmark is the first through the store Lean exporter arm (`Relico/Benchmark/StoreArtifactExporter.lean`, mirroring the multi-store exporter) and the store parser bridge (`run-store-from-zip.sh`, already in the tree). The exporter composes existing verified entry points -- `Relico.Frontend.decodeStoreModelText`, `Relico.Translation.translateStoreCore` and `Relico.Translation.translateStoreToCppSource` -- and adds no new obligations.

### 4. Preserved behavioural property

A recurring dispatch whose payload is the store: each execution swaps the held and next values, so what the server dispatches next is exactly what the previous execution stored.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family payload` arm.

## Evidence

- every pipeline stage exits 0 and RMC reports `satisfied`;
- formal witness: 46 obligations across the family's pre-existing proof modules;
- every recurrence is delayed by one period, so the runtime terminates within its budget.
