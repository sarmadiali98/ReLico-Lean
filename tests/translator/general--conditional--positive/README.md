# `general--conditional--positive`

A **general**-family positive benchmark. Exercises the general fragment's conditional: four if/else

## Provenance

### 1. Original purpose

Upstream corpus model `Thermostat/Thermostat`. A thermostat regulates a room: the sensor reports, the controller compares against a setpoint and switches the heater, and a checker watches the outcome.

### 2. Removed features

None, and none needed: the model is inside the DTR fragment as written and clears the model checker unchanged. Only a benchmark header comment was added.

### 3. Semantic changes made

None.

### 4. Preserved behavioural property

Control decisions taken by branching on measured state, with both arms of each branch reachable.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

The stage list is the one this benchmark's registry row already declared and is not widened here.

## Evidence

- source: the commented Timed Rebeca model;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness, not a claim about a particular selected ordering;
- parser JSON: produced through the `parser-json --family general` arm;
- decoded DTR AST, translated LF AST and LF source: the three `lean-export --family general` modes;
- formal witness: 49 obligations across `GeneralConditional`;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free under the model checker. Execution is bounded by the harness.
