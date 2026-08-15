# `global-multi-actor-payload--external-send-frame--positive`

This positive benchmark isolates the **external-send frame** capability: an
actor-to-actor external send followed by installation of the sender's
remaining continuation into the sender's own active body.

Unlike `global-multi-actor-payload--external-send--positive`, which reuses the
521-byte shared source, this benchmark carries its **own distinct** Timed
Rebeca source (608 bytes, SHA-256
`dd3966919fcabdc179f76f719f90bce75442e97652dab5a90d1d6b42278f06a9`). The
source extends the external-send shape with a Sender state variable
`continuationValue` and a post-send continuation statement
`continuationValue = 11;` inside `sendMessage`. The external send
`receiver0.receiveMessage(data)` is preserved verbatim; the continuation is the
distinguishing content.

The source contains `Sender sender0` and `Receiver receiver0`. `sender0` binds
`receiver0` as a known rebec. Its constructor triggers `sendMessage(1)` and
separately schedules recurring `keepAlive` behavior. `Sender.sendMessage`
performs one external payload send to `receiver0.receiveMessage(data)` and then
installs its continuation by assigning the state variable `continuationValue`.

The nine required stages are source, RMC, parser JSON, decoded DTR AST, formal
witness, translated LF AST, LF source, LFC, and runtime. The source and RMC
stages succeed; RMC reports `satisfied` for `Deadlock-Freedom and No Deadline
Missed`.

Because the continuation is a pure internal state update, six pipeline stages
genuinely individuate this benchmark from the external-send counterpart: the
`source`, `parser-json`, `decoded-dtr-ast`, `formal-witness`,
`translated-lf-ast`, and `lf-source` artifacts each differ. The
`parser-json` model records the assignment as a second `sendMessage` statement;
the `decoded-dtr-ast` and `translated-lf-ast` models carry a
`sender_continuation` block whose `produces_external_output` is `false`; and the
`lf-source` declares `state continuationValue: int = 0` and updates it in the
startup reaction.

The continuation deliberately produces **no external runtime observable**. The
translated model marks `produces_external_output` as `false`, matching the Lean
frame theorems, which characterize the continuation entirely as sender-local
state and never as emitted output. Consequently the `runtime`, `lfc`, and `rmc`
stage results are content-identical to the external-send counterpart: the
runtime still records the observation marker `RELICO_EXTERNAL_SEND_RECEIVED`
with `marker_count` equal to 1. Fabricating a distinct runtime observable for
the continuation would be construct-invalid, since the formal model exposes no
such observable.

The formal witness covers exactly 10 accepted source-capability obligations in:

- `Relico/Tests/GlobalMultiStorePayloadOneStep.lean` (6 obligations)
- `Relico/Tests/GlobalMultiStorePayloadOneStepCorrespondence.lean` (4 obligations)

These are the externalSendFrame-versus-dispatch step constructors, the one-step
inversion theorems, and the frame-step forward and backward correspondence
regressions. This obligation set is disjoint from both the external-send
positive witness (DeclaredFragment plus Dispatch) and the external-send-frame
negative witness (the Frame boundary module), so the frame capability is
witnessed by its own prescribed theorems.

The LF C++ target uses `public preamble`. Runtime executes in fast mode with a
5 msec logical timeout.

This benchmark does not claim unrestricted environmental input, universal
multi-actor correctness, global irrelevance of priorities, or source
self-termination. It does not widen the legacy `multi-store-payload` parser
route. The canonical paper is not modified.
