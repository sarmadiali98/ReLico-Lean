# `global-multi-actor-payload--keep-alive-external-send--positive`

A **global-multi-actor-payload**-family positive benchmark for a recurring external send kept alive by self-reschedule.

## Provenance

### 1. Original purpose

Formerly `global-multi-actor-payload--external-send-frame--negative`, a negative benchmark. A Sender forwards to a Receiver over an external send, kept alive by a one-period self-reschedule.

### 2. Why it was negative, and why that is obsolete

It was refused because the external-send-frame layer required a source-grounded frame transition witness this model does not provide. That is a limitation of one family bridge, not a violation of the DTR subset: measured against the current verified fragment, this exact source passes the general parser bridge, the Lean decoder, the verified translation, LF compilation -- and the model checker reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`. Per the stage K rule, a negative benchmark must represent a genuine violation of the current supported semantics, so the row is re-polarized rather than kept as a historical limitation.

This model is byte-identical to the source of `global-multi-actor-payload--multi-class-external-send--positive`. The former negative suite checked it twice, at two layers -- the parser's one-class limit and the frame transition witness -- and both rows own distinct Lean evidence modules, so both are kept, per the standing decision not to delete re-polarized rows.

### 3. Semantic changes made

None. The source model is unchanged from its negative form; only the benchmark wrapper changed -- the stage list widened from a six-stage boundary check to the full nine-stage pipeline, through the `parser-json --family general` arm, and the expected artifacts were regenerated accordingly.

### 4. Preserved behavioural property

A recurring external send kept alive by self-reschedule, now as a positive witness end to end. The Lean obligation coverage the row already owned is preserved unchanged: 27 obligations across `GlobalMultiStorePayloadExternalSendFrame`.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

## Evidence

- source: the unchanged model under a benchmark header;
- RMC: `satisfied`;
- parser JSON through the `parser-json --family general` arm;
- decoded DTR AST, translated LF AST and LF source: the three `lean-export --family general` modes;
- formal witness: 27 obligations;
- lfc and runtime: the generated LF compiles and runs under `lfc 0.11.0` with the C++ target.

## Keep-alive

Recurrence is delayed by one period where the model recurs, so the runtime terminates within its budget.
