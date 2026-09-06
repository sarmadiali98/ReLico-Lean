# `general--trace-execution--positive`

A **general**-family positive benchmark. Exercises trace execution: a subway door sequence of delayed steps

## Provenance

### 1. Original purpose

Upstream corpus model `Subway/Subway`. A subway door sequence: request, wait, pass, and a timeout arm that fires if the sequence stalls.

### 2. Removed features

None. The model is inside the DTR fragment as written; the changes below are additive.

### 3. Semantic changes made

- msgsrv `arm()`, `doneIn()` and `start()` each gained an `int at` parameter, and their send sites gained literal arguments;

Each was forced by one measured refusal: the translator declines a parameterless message server that is the target of an external send, because the LF port carrying it would have no value type and whether the target accepts such a port is unmeasured. The added parameters are markers -- no branch reads them, so no behaviour changes and the model checker's verdict is unchanged.

### 4. Preserved behavioural property

A long observable sequence of delayed steps, with a timeout path reachable from it.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

The stage list is the one this benchmark's registry row already declared and is not widened here.

## Evidence

- source: the commented Timed Rebeca model;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness, not a claim about a particular selected ordering;
- parser JSON: produced through the `parser-json --family general` arm;
- decoded DTR AST, translated LF AST and LF source: the three `lean-export --family general` modes;
- formal witness: 10 obligations across `GeneralTraceTransfer`;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free under the model checker. Execution is bounded by the harness.
