# PingPong - adaptation record

Status: **complete** - the literal source passes all eight pipeline stages.

Source: `examples.zip:ReLico-main/PingPong/PingPong.rebeca`, 97 lines, with four reactive
classes (`Checker`, `Ping`, `Pong`, and `KeepAlive`).

## Property boundary

The original corpus `PingPong.property` file is intentionally excluded and is not part of this
benchmark. It asserts `chk.violation == 0`; this fixture checks executable translation and runtime
behavior only and does not translate or encode that assertion.

## Applied adaptation

No source adaptation is applied. `source/model.rebeca` preserves the archived model byte-for-byte,
including actors, state variables, message payloads, priorities, both 10-unit protocol delays, and
the 100-unit KeepAlive period.

All parameterless messages are self-send targets. Every external send carries an integer payload,
so no marker parameter is required.

## Protocol and RMC

The Ping/Pong exchange is a finite one-shot request and reply. The independent periodic
`KeepAlive.tick()` loop schedules one successor after 100 time units and sends nothing to another
actor. No queue-control redesign is introduced.

RMC 2.14 reports `satisfied`, reaching 20 states and 43 transitions. The source, parser, Lean/LF,
`lfc 0.11.0`, and runtime stages all pass without a source adaptation.
