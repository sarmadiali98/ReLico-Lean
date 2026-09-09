# Fibonacci — adaptation record

Status: **complete** - the preserved model semantics pass the full benchmark pipeline.

Source: `examples.zip:ReLico-main/Fibonacci/Fibonacci.rebeca`, 79 lines, with four reactive
classes (`Source`, `FibCore`, `Checker`, and `KeepAlive`).

## Property boundary

The original `Fibonacci.property` file is intentionally excluded. This benchmark checks translation
and runtime behavior only; the property is not translated or encoded as an assertion. No semantic
correction was applied to the source.

## Applied adaptation

No semantic adaptation was applied. The source preserves the original Fibonacci result selection,
integer payloads, priorities, `after(10)`, and `after(100)` delays. The KeepAlive self-rearming loop
remains because RMC 2.14 reports `satisfied` without queue growth; it is independent background
activity. The generated LF executable also terminates successfully under the runtime stage.
