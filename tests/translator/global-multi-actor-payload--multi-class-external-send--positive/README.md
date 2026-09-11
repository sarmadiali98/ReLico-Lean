# `global-multi-actor-payload--multi-class-external-send--positive`

A **global-multi-actor-payload**-family positive benchmark for an external send across two reactive classes.

## Provenance

### 1. Original purpose

Formerly `global-multi-actor-payload--external-send--negative`, a negative benchmark. A Sender forwards to a Receiver over an external send, kept alive by a one-period self-reschedule.

### 2. Why it was negative, and why that is obsolete

It was refused because the multi-store-payload bridge accepts exactly one reactive class, and this model declares two. That is a limitation of one family bridge, not a violation of the DTR subset: measured against the current verified fragment, this exact source passes the general parser bridge, the Lean decoder, the verified translation, LF compilation -- and the model checker reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`. Per the stage K rule, a negative benchmark must represent a genuine violation of the current supported semantics, so the row is re-polarized rather than kept as a historical limitation.

### 3. Semantic changes made

None. The source model is unchanged from its negative form; only the benchmark wrapper changed -- the stage list widened from a six-stage boundary check to the full nine-stage pipeline, through the `parser-json --family general` arm, and the expected artifacts were regenerated accordingly.

### 4. Preserved behavioural property

An external send across two reactive classes, now as a positive witness end to end. The Lean obligation coverage the row already owned is preserved unchanged: 56 obligations across `GlobalMultiStorePayloadExternalSend`.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

## Evidence

- source: the unchanged model under a benchmark header;
- RMC: `satisfied`;
- parser JSON through the `parser-json --family general` arm;
- decoded DTR AST, translated LF AST and LF source: the three `lean-export --family general` modes;
- formal witness: 56 obligations;
- lfc and runtime: the generated LF compiles and runs under `lfc 0.11.0` with the C++ target.

## Keep-alive

Recurrence is delayed by one period where the model recurs, so the runtime terminates within its budget.
