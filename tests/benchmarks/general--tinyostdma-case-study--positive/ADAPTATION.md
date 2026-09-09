# TinyOSPV6-TDMA — blocker record and redesign decision

Status: **in progress** — four redesign attempts measured and refused by RMC; the maintainer
approved option A (demand-driven slot clock) on 2026-09-09. This file records the evidence that
motivated the decision, so the probes do not have to be re-run to justify it.

Source: `examples.zip:ReLico-main/tinyos-prop/TinyOSPV6-TDMA.rebeca`, 253 lines. TDMA is MACB plus
one rebuilt class: the corpus diff shows `CPU`, `Sensor`, `Misc`, `WirelessMedium` and `main`
effectively identical, with every difference confined to `CommunicationDevice` — the TDMA slot
machine (slot clock, deferred sending, busy retry, in-flight guard).

## The RMC 2.14 measurement that explains every failure

**The `after(d)` delay value appears nowhere in RMC's generated C++.** Verified by grep across
every generated file of every probe and of the landed, `satisfied` MACB tree: every `_timed_msg_*`
call site passes `_ref_now` unmodified; the literals 10/40/100 are absent. RMC 2.14 under this
pipeline's invocation (`-v 2.1`, no mode flag) is a **causality-only model checker**: `satisfied`
means deadlock-freedom with bounded queues under *collapsed* (zero-delay) time.

Probe campaign (each a minimal `.rebeca` run through the same rmc stage):

| probe | shape | verdict |
|---|---|---|
| pa1 | one naked self-loop, `after(100)` | **satisfied** (one message at a time) |
| pa7 | self re-arm in mutually exclusive branches | **satisfied** |
| pa4 | self re-arm + zero-delay self companion | **queue overflow** |
| pa6 | self re-arm + delayed self companion | **queue overflow** |
| pa8 | self re-arm + zero-delay *cross-actor* companion | **queue overflow** on the companion's queue |

**The precise rule: an unconditionally self-re-arming message server (a naked clock) that also sends
to any other actor on the same path overflows that actor's queue under collapsed time.** MACB
passed because it contains zero naked clocks — every loop is ack-coupled through another actor.

Also measured: RMC rejects `after` on cross-actor sends from constructors outright ("Direct sending
to self is allowed in constructors"), and enqueues constructor self-sends at `_ref_now` = 0
regardless of any `after`.

## The four refused redesign attempts

1. **Original shape** — clock re-arms (`after(10)`/`after(50)`) and self-sends a `checkPendingData`
   companion each active entry. Overflow on the sender device's queue: 18 `HANDLETDMASLOT`
   transitions at execution time 0, one `checkPendingData` accumulating per step. The pa4/pa8 rule
   exactly.
2. **Constructor delay `after(1)`** — no effect; the trace still opens at time 0 (constructor sends
   are enqueued at `_ref_now`).
3. **Inline the poll on the clock** (no self-sent companion; `send()` still polls via
   `checkPendingData`): overflow moved to the **medium's** queue — two `getStatus` per round.
4. **Single-poll** (`send()` records only; the clock's active entry inlines the sole poll): overflow
   on the medium again. The trace proves the sensor→radio round is properly ack-coupled
   (`SEND…RADIOCYCLEDONE×2…SAMPLETAKEN…SEND`); the accumulation is the clock's poll opportunities
   stacking against the medium's undrained queue within the collapsed instant — under collapsed
   time, round completion is itself instantaneous, so "poll once per round" does not bound polls
   *per instant*.

## Option A: demand-driven slot clock (approved)

The unconditional constructor-started re-arm is removed. `send()` preserves the original
one-request discipline: a send while `receiverDevice` is non-null sets the observable
`sendWhileBusy` latch and does not overwrite or queue another request. The general parser does not
admit the original assertion shape, so this latch is the established fragment adaptation for that
assertion. A valid send records the one pending request and starts one active-slot attempt only when
the lifecycle is idle. `checkPendingData()` remains the only place that polls the medium. It issues
one medium attempt after the adapted 10-unit active-slot interval. While `busyWithSending` is true,
neither another slot transition nor another polling message is queued.

A successful medium response is the completion event: `receiveResult(true)` clears the request and
returns the device to idle. A busy medium response or collision result clears `busyWithSending` but
keeps the request, then schedules exactly one future active-slot opportunity after the 50-unit
interval for the other nodes. The original one-request assertion means that a second send cannot be
installed while `receiverDevice` is non-null.

The earlier adapted `transmissionTaskComplete` self-message has been removed. It had no counterpart
in the original model, where the medium result owns completion, and its collapsed `after(7)` timing
allowed duplicate completion messages to accumulate under RMC. The sender now remains occupied
through `receiveStatus(false)` and is released only by `receiveResult(true)` or `receiveResult(false)`.

**The semantic boundary, stated plainly.** The original clock wakes every slot globally, including
when the device has no data. The redesign leaves the clock quiescent when there is no pending
transmission, and a later send begins a fresh active-slot lifecycle. Absolute global slot phase is
therefore not retained. While demand exists, one medium attempt per active slot, the 10-unit active
interval, the 50-unit inactive interval, active-slot transmission gating, and retry at a future
active slot remain. This is an intentional abstraction because RMC 2.14 collapses delayed messages:
the original repeated polling can grow a queue before medium responses stabilize the state. The
adaptation changes repeated polling into one attempt per slot while preserving TDMA ownership,
slot gating, and retry behavior.

Accepted under the same standing constraint as every case study: the model must remain a meaningful
system, not a trivial one — the node still samples, buffers, defers to its slot, transmits,
retries on a busy medium, and reacts to collisions.
