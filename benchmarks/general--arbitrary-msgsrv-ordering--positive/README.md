# `general--arbitrary-msgsrv-ordering--positive`

A **general**-family positive benchmark from the `examples2` corpus (`Aribitrary_Ordering_messageserver.rebeca`), integrated without adaptation.

## Provenance

### 1. Original purpose

Four message servers are armed together in the constructor and each recurs on its own one-period timer. The model fixes no order between them; which runs first is the scheduler's choice, which is the property under test.

### 2. Removed features

None. The model is inside the DTR fragment as written and was measured through the exporter, the Lean decoder, the verified translation and `lfc` with zero adaptation; the model checker reports `satisfied`.

### 3. Semantic changes made

None. Only a benchmark header comment was added, which shifts the parser document's `line` fields by the header height and nothing else.

### 4. Preserved behavioural property

The ordering or composition structure the model exists to demonstrate, unchanged. Where that structure is a zero-delay recurrence, the `runtime` stage is dropped from this row rather than distorting the model with delays: at logical time zero the structure is the point, and adding delays would test a different model.

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`. This row owns no Lean obligations, so it carries no formal-witness stage; its evidence is the pipeline artifacts themselves.

## Evidence

- source: the unmodified corpus model under a benchmark header;
- RMC: `satisfied`;
- parser JSON, decoded DTR AST, translated LF AST, LF source and `lfc`: the general pipeline end to end.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free under the model checker.
