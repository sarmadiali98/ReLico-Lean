# Election - adaptation record

Status: **complete** - the unmodified model semantics pass the full benchmark pipeline.

Source: `examples.zip:ReLico-main/Election/Election.rebeca`, with six reactive classes
(`Checker`, `Node1`, `Router`, `Node0`, `Source`, and `KeepAlive`).

## Property boundary

The original `Election.property` file is intentionally excluded. This benchmark checks translation
and runtime behavior only; the `Election_NoViolation` property is not translated or encoded as an
assertion. No semantic correction was applied to make the property hold.

## Applied adaptation

No semantic adaptation was applied. The source preserves the actors, state, integer message
payloads, message and instance priorities, routing order, and the 100-unit KeepAlive delay. Only a
benchmark provenance header was added.

The independent KeepAlive self-rearming loop remains. RMC 2.14 reports `satisfied` without queue
growth, and the generated LF executable terminates successfully under the runtime stage, so no
timing redesign is justified.
