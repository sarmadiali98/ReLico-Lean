# `global-multi-actor-payload--external-send--positive`

This positive benchmark is the successful acceptance counterpart to
`global-multi-actor-payload--external-send--negative`.

It reuses the exact committed 521-byte Timed Rebeca source with SHA-256
`fec649d657399aad3acfdb2e7904a1ff46b858cf9e8404f2a6158494785fc731`.

The source contains `Sender sender0` and `Receiver receiver0`. `sender0`
binds `receiver0` as a known rebec. Its constructor triggers
`sendMessage(1)` and separately schedules recurring `keepAlive` behavior.

`Sender.sendMessage` performs one actor-to-actor external payload send to
`receiver0.receiveMessage(data)`. For the constructor-triggered occurrence,
the bound payload is `1` and the external-send delay is zero.

The nine required stages are source, RMC, parser JSON, decoded DTR AST,
formal witness, translated LF AST, LF source, LFC, and runtime.

The source and RMC stages succeed. RMC reports `satisfied` for
`Deadlock-Freedom and No Deadline Missed`.

The additive `global-multi-store-payload` benchmark route preserves the two
actors, known-rebec topology, receiver identity, payload binding, zero
external-send delay, keepAlive delay, and source priority metadata. It does
not widen the legacy `multi-store-payload` parser route used by the negative
counterpart.

The formal witness covers exactly 35 accepted source-capability obligations
in:

- `Relico/Tests/GlobalMultiStorePayloadDeclaredFragment.lean`
- `Relico/Tests/GlobalMultiStorePayloadDispatch.lean`

For this frozen executable witness, the single external-send occurrence is
represented by a startup output connected from `sender0` to `receiver0` with
`after 0 msec`. Recurring keepAlive behavior is represented separately by a
1 msec periodic timer and does not repeatedly emit the external payload.

The LF C++ target uses `public preamble`. Runtime executes in fast mode with
a 5 msec logical timeout. `runtime/result.json` records the observation marker
`RELICO_EXTERNAL_SEND_RECEIVED` with `marker_count` equal to 1 before the
runtime stage records `status` equal to `pass`.

This benchmark does not claim unrestricted environmental input, universal
multi-actor correctness, global irrelevance of priorities, or source
self-termination. The canonical paper is not modified.
