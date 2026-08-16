# `global-multi-actor-payload--finite-execution--positive`

This positive benchmark isolates the **finite multi-step execution** capability:
translation correctness verified not for a single step but across a whole finite
run, characterized as the reflexive-transitive `Steps` closure with
bidirectional forward and backward simulation.

Unlike `global-multi-actor-payload--external-send--positive`, which reuses the
521-byte shared source, and unlike
`global-multi-actor-payload--external-send-frame--positive`, which carries a
single-store continuation (`continuationValue = 11`), this benchmark carries its
**own distinct** Timed Rebeca source (647 bytes, SHA-256
`bdc06512c25597a5b176c00db3632dbb815a8dfa50d03e9e3cfd8e0e9aea3d03`). The source
extends the external-send shape with **two** Sender state variables,
`completedSteps` and `finalStep`, and a two-statement post-send continuation
`completedSteps = 2; finalStep = 1;` inside `sendMessage`. The external send
`receiver0.receiveMessage(data)` is preserved verbatim; the two-store
continuation is the distinguishing source content and matches the family's
multi-store payload theme.

The source contains `Sender sender0` and `Receiver receiver0`. `sender0` binds
`receiver0` as a known rebec. Its constructor triggers `sendMessage(1)` and
separately schedules recurring `keepAlive` behavior. `Sender.sendMessage`
performs one external payload send to `receiver0.receiveMessage(data)` and then
installs its two-store continuation by assigning `completedSteps` and
`finalStep`. The recurring `keepAlive` supplies the successive dispatch steps
that make the execution genuinely multi-step.

The nine required stages are source, RMC, parser JSON, decoded DTR AST, formal
witness, translated LF AST, LF source, LFC, and runtime. The source and RMC
stages succeed; RMC reports `satisfied` for `Deadlock-Freedom and No Deadline
Missed`.

Six pipeline stages genuinely individuate this benchmark from both the
external-send counterpart and the single-store frame counterpart: the `source`,
`parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, and
`lf-source` artifacts each differ. The `parser-json` model records the two
assignments as the second and third `sendMessage` statements; the
`decoded-dtr-ast` and `translated-lf-ast` models carry a `sender_continuation`
block with two assignments whose `produces_external_output` is `false`; and the
`lf-source` declares `state completedSteps: int = 0` and `state finalStep: int
= 0` and updates both in the startup reaction.

The finite-execution capability is **not** isolated at the runtime level. Like
the two other positives, the continuation is pure internal state and produces no
external runtime observable, so the `runtime`, `lfc`, and `rmc` stage results are
content-identical to the counterparts: the runtime still records the observation
marker `RELICO_EXTERNAL_SEND_RECEIVED` with `marker_count` equal to 1 and
terminates cleanly (`external_timeout` is `false`). The integers `2` and `1` are
static illustrative stores; this benchmark makes **no** claim that the runtime
observably counts execution steps. Fabricating a distinct runtime observable for
finite execution would be construct-invalid, since the operational model exposes
no such observable.

The capability is isolated at the **formal** level, which is where finite
execution genuinely lives. The formal witness covers exactly 4 accepted
source-capability obligations in a single distinct module:

- `Relico/Tests/GlobalMultiStorePayloadFiniteExecution.lean` (4 obligations)

These are `sourceStep_toOneStep_regression` and
`sourceStep_exists_of_oneStep_regression` (each single multi-step `Steps`
constructor reduces to and is recovered from the underlying one-step relation)
together with `finite_forward_regression` and `finite_backward_regression` (the
whole finite `Steps` closure corresponds forward and backward under bidirectional
simulation). This module is built on the same external-send frame concept as the
frame positive, but verified over the multi-step reflexive-transitive closure
rather than a single step, so the obligation set is disjoint from the
external-send positive witness (DeclaredFragment plus Dispatch), the frame
positive witness (the OneStep and OneStepCorrespondence modules), and every
negative witness. The finite-execution capability is therefore witnessed by its
own prescribed multi-step theorems, which `formal-witness` genuinely elaborates
with `lake env lean`.

The LF C++ target uses `public preamble`. Runtime executes in fast mode with a
5 msec logical timeout.

This benchmark does not claim unrestricted environmental input, universal
multi-actor correctness, global irrelevance of priorities, or source
self-termination. It does not widen the legacy `multi-store-payload` parser
route. The canonical paper is not modified.
