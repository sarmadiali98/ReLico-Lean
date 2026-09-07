# TinyOSPV6-MACB — redesign record

Status: **implemented** as `general--tinyosmacb-case-study--positive`,
all eight stages green including `rmc`, after the maintainer-approved
category-3 redesign.

Source: `examples.zip:ReLico-main/tinyos-prop/TinyOSPV6-MACB.rebeca`,
215 lines, 5 classes (CPU, Sensor, Misc, WirelessMedium,
CommunicationDevice), 6 instances. The redesigned source is 196 lines;
the instance inventory is unchanged.

## Original blockers, measured

1. `environment variable` (10 declarations; two — `tmdaSlotSize`,
   `packetMaximumSize` — are never used and drop out with the fold).
2. Rebec-typed message parameters: `send(CommunicationDevice receiver,
   ...)`, `broadcast(CommunicationDevice receiver, ...)`,
   `receiveData(CommunicationDevice receiver, ...)` carry rebec values.
3. Rebec-typed state variables, runtime-reassigned with `null`:
   `medium.senderDevice`, `medium.receiverDevice`, `CD.receiverDevice`
   (the category-3 case of the ROUTING_COMPARISON ruling — no static
   referent to substitute).
4. Sender capture: `((CommunicationDevice)sender).receiveStatus(...)` /
   `.receiveResult(...)` in the medium.
5. Nondeterministic first-tick delays: `after(?(10, 20, 30))` x2.
6. Computed delays: `after(packetsNumber * OnePacketTransmissionTime)`,
   `delay((numberOfNodes / 2) * (OnePacketTransmissionTime + 1))`.
7. `currentMessageWaitingTime` — a Rebeca built-in.
8. `assertion(false)` x4; `delay` statements x4; `byte`; `+=`.

## Applied mechanical adaptations

- **env folded**: samplingRate 25 → period 1000/25 = **40**;
  sensorTaskDelay **2**; miscPeriod **120**; miscTaskDelay **10**;
  OnePacketTransmissionTime **7**; numberOfNodes/2*(7+1) = **24**;
  bufferSize **1** (so each sample is a packet and `packetsNumber` is
  1, making every remaining delay a literal by constant propagation);
  `data` is the constant 0, never read, and folds away with it.
- **`byte` → `int`**; the `(byte)1` cast → the literal.
- **`+=` → `v = v + 1`** (R16).
- **`delay` statements → delayed sends**: sensor/misc task lengths
  become `self.sensorTask() after(2)` / `self.miscTaskComplete()
  after(10)`; the status-check backoff becomes the literal
  `after(24)`-equivalent (folded away entirely — see below); the
  receive-time delay is a no-op (see below).
- **Marker parameters** on the parameterless external-send targets
  (`sensorEvent`, `miscEvent`, `sampleTaken`, `miscDone`,
  `radioCycleDone`, `radioDataDelivered`), each passing `0`.

## Applied redesign

### Rebec-typed values → int device tags

The two `CommunicationDevice` instances are named by their existing
`id` (0 = receiver, 1 = sensor node's sender). Every rebec-typed
message parameter becomes an int tag (`send(receiverTag)`,
`broadcast(receiverTag, senderTag)`, `receiveData(receiverTag)`); every
rebec-typed state variable becomes an int tag with **-1 = none** as the
null encoding; `receiver == self` becomes `receiverTag == id`; CPU's
static device references stay knownrebecs, with the call argument
becoming the tag.

### Sender capture → tag dispatch over static bindings

The medium binds both devices (`cd0`, `cd1`, matching id 0/1);
`getStatus(senderTag)` and `broadcast(receiverTag, senderTag)` carry
the asker's id as a literal (each device→medium pair is fixed), and
both medium replies route through the matching binding — the same
shape as the approved AutonomousVehicles and LeasingNRPFD tag routing.

### Nondeterministic first-tick delays → fixed literals

`after(?(10, 20, 30))` → `after(10)` in both drivers (the approved
TinyOS ruling). **Semantic boundary:** the original explores three
first-tick timings; the redesign fixes the earliest. Steady-state
periodicity (40/120) is untouched.

### `currentMessageWaitingTime` — semantic boundary, no replacement

The original's deadline check is `assertion(period - lag -
currentMessageWaitingTime >= 0)` in `sensorTask`, where
`currentMessageWaitingTime` is a **Rebeca built-in**: the time the
executing message spent waiting in its rebec's queue before dispatch.
The assertion checks that a sensor interrupt is handled within its
sampling period even under queueing delay — a schedulability claim
about the node's interrupt latency.

**It cannot be represented in the DTR fragment.** DTR has no message
waiting-time metadata: a message server cannot observe how long its own
message waited, and no state variable can record it because the wait
happens before the server runs. No latch, tag, or restructuring
preserves the condition, because its subject does not exist in the
target semantics. Per the maintainer ruling, the check is **dropped
without an invented replacement** — the `period`/`lag` parameters fold
away with it (their only use was the assertion). What remains of the
sensor pipeline — the task delay, the buffering, the radio send — is
fully preserved.

### Assertions → observable latches

The other three assertions become persistent boolean latches on the
`CommunicationDevice` (the UnsafeSend/AutonomousVehicles pattern):
`assertion(receiverDevice == null)` in `send` → **`sendWhileBusy`**
(set when a send starts while a cycle is still open);
`assertion(!result)` in `receiveStatus` → **`mediumBusyAtStatusCheck`**
(set when the medium reports busy at the status check);
`assertion(result)` in `receiveResult` → **`failedTransmission`** (set
on a collision result). The latches never gate any behaviour, so they
cannot mask a deadlock or shorten an execution; RMC explores whether
the corresponding bad states are reachable. Under the completion
coupling below, `sendWhileBusy` is unreachable by construction — the
redesign enforces the very invariant the original asserted.

### Completion-coupled drivers (boundedness)

The original re-arms its drivers unconditionally
(`self.sensorLoop() after(period)` next to the send). Under the gate's
zero-delay exploration this overflows (measured on the first redesign
draft: the sensor's `sensorEvent`s piled into a starved CPU). The fix
is the established pattern, applied to every loop:

- **Sensor loop**: re-armed by `sampleTaken` — the CPU's ack that the
  sample was processed.
- **Misc loop**: re-armed by `miscDone` — the CPU's ack.
- **Radio round**: the CPU closes a round only when **both** consumers
  have consumed — the sender's `receiveResult` (success or collision)
  **and**, on success, the receiver's `receiveData` consumption ack
  (`radioDataDelivered`; a collision delivers no data, so the result
  alone closes that round). This is the tcsma two-copy lesson: the
  first draft gated only on the sender's result, and the receiver's
  `receiveData`s accumulated without bound (measured: 10 x
  `receiveData(0)` on a starved receiver).

This enforces the model's own no-overlap assumption — the original's
`assertion(receiverDevice == null)` presumes the radio cycle (33 time
units) completes within the sampling period (40); the redesign makes
the next round wait for the cycle instead of assuming the timing.

Also removed, as write-only: `maxTraffic` (set, never read),
`sendingData` / `sendingPacketsNumber` (carry the folded constants 0/1,
never read), and the receive-time `delay(7)` no-op task (timing-only,
empty resumed body, nothing observes it — the receive itself is the
observable, and its consumption now carries the delivery ack).

## Result

No rebec-typed values, no `sender`, no `instanceof`, no `null`, no
nondet, no computed delays, no assertions, no built-ins — and the node
samples, buffers, transmits, and handles collisions periodically, every
queue bounded. RMC reports **`satisfied`** for `Deadlock-Freedom and
No Deadline Missed`.
