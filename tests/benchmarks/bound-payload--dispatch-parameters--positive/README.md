# `bound-payload--dispatch-parameters--positive`

A **bound-payload**-family positive benchmark for dispatch with a message-server parameter.

## Provenance

### 1. Original purpose

Formerly `bound-payload--dispatch--negative`, a negative benchmark. A bound-payload controller dispatches to itself on a one-period delay, carrying an int parameter that it stores into its state.

### 2. Why it was negative, and why that is obsolete

It was refused because the ReLico v0 parser bridge rejects message-server parameters (V0_PARSER_BRIDGE_MESSAGE_SERVER_PARAMETERS_UNSUPPORTED). That is a limitation of one family bridge, not a violation of the DTR subset: measured against the current verified fragment, this exact source passes the general parser bridge, the Lean decoder, the verified translation, LF compilation -- and the model checker reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`. Per the stage K rule, a negative benchmark must represent a genuine violation of the current supported semantics, so the row is re-polarized rather than kept as a historical limitation.

### 3. Semantic changes made

None. The source model is unchanged from its negative form; only the benchmark wrapper changed -- the stage list widened from a six-stage boundary check to the full nine-stage pipeline, through the `parser-json --family general` arm, and the expected artifacts were regenerated accordingly.

### 4. Preserved behavioural property

Dispatch with a message-server parameter, now as a positive witness end to end. The Lean obligation coverage the row already owned is preserved unchanged: 22 obligations across `DetailedBoundPayloadInvariantMatches`.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

## Evidence

- source: the unchanged model under a benchmark header;
- RMC: `satisfied`;
- parser JSON through the `parser-json --family general` arm;
- decoded DTR AST, translated LF AST and LF source: the three `lean-export --family general` modes;
- formal witness: 22 obligations;
- lfc and runtime: the generated LF compiles and runs under `lfc 0.11.0` with the C++ target.

## Keep-alive

Recurrence is delayed by one period where the model recurs, so the runtime terminates within its budget.
