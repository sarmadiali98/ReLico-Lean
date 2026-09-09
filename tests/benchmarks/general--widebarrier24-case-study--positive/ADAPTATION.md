# WideBarrier24 - adaptation record

Status: **complete** - the literal source passes all eight pipeline stages.

Source: `examples.zip:ReLico-main/WideBarrier24/WideBarrier24.rebeca`, 93 lines, with two
reactive classes (`Coordinator` and `KeepAlive`).

## Property boundary

The original corpus `WideBarrier24.property` file is intentionally excluded and is not part of
this benchmark. It asserts `coord.violation == 0`; this fixture checks executable translation and
runtime behavior only and does not translate or encode that assertion.

## Applied adaptation

No source adaptation is applied. `source/model.rebeca` preserves the archived model byte-for-byte,
including 40 rounds, 24 tokens per round, queue bounds, priorities, one-unit delays, and the
100000-unit KeepAlive period.

All messages are self-send targets, so no marker parameter or external routing adaptation is
required.

## Queue behavior

Each dispatch creates exactly 24 delayed tokens, below the coordinator's queue bound of 50. The
24th token alone schedules the next round, preventing overlapping bursts. KeepAlive retains one
delayed successor. No queue-control redesign is introduced.

RMC 2.14 reports `satisfied`, reaching 3,006 states and 39,130 transitions. The source, parser,
Lean/LF, `lfc 0.11.0`, and runtime stages all pass without a source adaptation.
