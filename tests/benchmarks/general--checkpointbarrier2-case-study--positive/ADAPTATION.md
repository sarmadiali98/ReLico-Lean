# CheckpointBarrier2 — adaptation record

Status: **complete** - the preserved model semantics pass the full benchmark pipeline.

Source: `examples.zip:ReLico-main/CheckpointBarrier2/CheckpointBarrier2.rebeca`, 71 lines,
with two reactive classes (`Coordinator` and `KeepAlive`).

## Property boundary

The original `CheckpointBarrier2.property` file is intentionally excluded. This benchmark checks
translation and runtime behavior only; the property is not translated or encoded as an assertion.
No semantic correction was applied to the source.

## Applied adaptation

No semantic adaptation was applied. The bounded eight-epoch coordinator, two delayed arrivals per
epoch, one-unit dispatch delay, priorities, and the 100000-unit KeepAlive timing are preserved.
The KeepAlive self-rearming loop remains because RMC 2.14 reports `satisfied` without queue growth;
it is independent background activity and does not communicate with the Coordinator. The generated
LF executable also terminates successfully under the runtime stage.
