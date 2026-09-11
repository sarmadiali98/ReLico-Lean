# `general--runtime-semantics--positive`

A **general**-family positive benchmark. Exercises runtime semantics: a token circulates a ring of actors,

## Provenance

### 1. Original purpose

Upstream corpus model `Ring/Ring`. A token circulates a ring of actors, each forwarding to its successor after a delay.

### 2. Removed features

None, and none needed: the model is inside the DTR fragment as written and clears the model checker unchanged. Only a benchmark header comment was added.

### 3. Semantic changes made

None.

### 4. Preserved behavioural property

Delayed message passing around a cycle, so runtime behaviour is the model's content rather than a side effect of it.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

The stage list is the one this benchmark's registry row already declared and is not widened here.

## Evidence

- source: the commented Timed Rebeca model;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness, not a claim about a particular selected ordering;
- parser JSON: produced through the `parser-json --family general` arm;
- decoded DTR AST, translated LF AST and LF source: the three `lean-export --family general` modes;
- formal witness: 34 obligations across `GeneralRuntime`;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free under the model checker. Execution is bounded by the harness.
