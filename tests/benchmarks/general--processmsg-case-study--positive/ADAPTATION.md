# ProcessMsg - adaptation record

Status: **complete** - the literal source passes all eight pipeline stages.

Source: `examples.zip:ReLico-main/ProcessMsg/ProcessMsg.rebeca`, 86 lines, with four reactive
classes (`Source`, `Task`, `Checker`, and `KeepAlive`).

## Property boundary

The original corpus `ProcessMsg.property` file is intentionally excluded and is not part of this
benchmark. It asserts `chk.violation == 0`; this fixture checks executable translation and runtime
behavior only and does not translate or encode that assertion.

## Applied adaptation

No source adaptation is applied. `source/model.rebeca` preserves the archived model byte-for-byte,
including actors, state variables, message payloads, priorities, the 10-unit processing delay, and
the 100-unit KeepAlive period.

All parameterless messages are self-send targets, so they require no marker payload. The external
sends `task.msg(0)` and `chk.complete(ok)` already carry integer payloads.

## KeepAlive and RMC

The periodic `KeepAlive.tick()` self-rearming loop remains unchanged. Each execution schedules one
successor after 100 time units and does not send to another actor. No queue-control redesign is
introduced.

RMC 2.14 reports `satisfied`, reaching 6 states and 7 transitions. The source, parser, Lean/LF,
`lfc 0.11.0`, and runtime stages all pass without a source adaptation.
