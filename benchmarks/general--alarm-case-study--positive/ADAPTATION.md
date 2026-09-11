# Alarm — adaptation record

Status: **in progress** — source validation and RMC 2.14 pass with the original model semantics.

Source: `examples.zip:ReLico-main/Alarm/Alarm.rebeca`, 70 lines, with three reactive classes
(`Checker`, `Controller`, and `KeepAlive`).

## Property boundary

The original corpus `Alarm.property` file is intentionally discarded and is not part of this
benchmark. This benchmark checks translation and runtime behavior only. The property is not
translated or encoded as an assertion, and no source correction was applied to make the property
hold: `turnOff(0)` remains unchanged.

## Applied adaptation

No semantic adaptation was required. The source preserves the original actors, state variables,
message servers, priorities, `after(1000)`, `after(2000)`, and Controller/Checker behavior. The
source only carries a benchmark header comment.

The parameterized external send `chk.observeStopResult(fault)` already carries an integer payload,
so no marker-parameter adaptation is needed. Parameterless self-sends remain local actions.

## KeepAlive and RMC

The periodic `KeepAlive.tick()` self-rearming loop remains unchanged. It is independent background
activity and does not send to another actor. RMC 2.14 reports `satisfied` without queue growth, so
no demand-driven or completion-coupled redesign is justified.
