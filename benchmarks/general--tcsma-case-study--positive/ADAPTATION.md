# tcsma — adaptation record

Status: **implemented** as `general--tcsma-case-study--positive`, all eight stages green including `rmc`.

Source: `examples.zip:ReLico-main/benchmarks/tcsma.rebeca`, 215 lines, the paper-named TCSMA model. The benchmark source is 189 lines; the difference is the removed never-read bookkeeping layer (see below) plus the added gating.

## Original blockers

Measured against the unmodified source (reproduced fresh before any fix):

```
translation failed: message server `User`.`sendData` takes no
parameters, so the port that would carry it has no payload
```

(`Interface.getAckFromUser` behind it — the same boundary.) And the model checker on the unmodified source: `queue overflow`, with the counter-example showing the medium flooded by the controller's unconditional `self.sendENQ() after(2)` timer while the medium is starved.

## Applied adaptation 1 — two marker parameters

`User.sendData()` and `Interface.getAckFromUser()` gain `int unit`; their send sites pass `0`. No server body reads `unit`. The same inert-marker resolution as the four preceding RQ1 benchmarks.

## Applied adaptation 2 — poll gating on round completion

The original re-arms the poll unconditionally (`self.sendENQ() after(2)` inside `sendENQ`), an uncoupled periodic producer. The fix: the controller gains two flags, `enqPending` and `dataPending`, both set when a poll is issued; `receiveData` clears one flag per consumed broadcast copy (the ENQ echo, `msg == 3`, and the data response, `msg != 3`); the next poll fires only when both are clear, and the re-arm `self.sendENQ() after(2)` is issued by whichever copy is consumed second — exactly one re-arm per round. The round structure is unchanged: poll station `next`, advance `next = next % 2 + 1`, ENQ broadcast, data pass. Under the real semantics the round is instantaneous, so the poll period is unchanged; the guard enforces one-round-in-flight instead of assuming it from timing. The same completion-coupling principle as the LeasingNRPFD boundedness fix.

Why both copies must gate (measured, not assumed): this gate's exploration selects messages non-FIFO — three minimal probes prove that a delayed self-re-arm can preempt earlier-queued dead messages (`noop`+re-arm overflows), that even delayed dead self-messages accumulate, and that a self-timer cycle sending zero-delay to a starved rebec overflows its queue. Gating on the data copy alone left the ENQ echo accumulating in the controller's queue — the measured intermediate overflow.

## Applied adaptation 3 — never-read bookkeeping removed

With the controller gated, the overflow victim moved to the medium (nine `finishedPassing()`), then to a user (ten `changeStatus`). Every accumulating message class traced to a bookkeeping flag that is **written and never read** — verified by grep for each: `ctrlSend` (2 writes, 0 reads), `passMessage` (3/0), `interfaceSent` (3/0), `speak` (3/0), `received` (3/0). Their five message servers (`finSend` twice, `finishedPassing`, `getAckFromUser`, `changeStatus`) and their send sites are removed with the flags. No observable behaviour changes: a flag nothing reads cannot be observed, and the protocol messages (poll, ENQ broadcast, data pass, per-station forwarding) are untouched. The resulting protocol core is seven servers: `sendENQ`, `receiveData` (Controller), `passMsg` (Medium), `getFromMedium`, `getFromUser` (Interface), `sendData`, `receiveData` (User).

## Result

After the three adaptations: every message arrival traces back to a gated poll, every queue holds at most one round in flight, and RMC reports **`satisfied`** for `Deadlock-Freedom and No Deadline Missed` on the 189-line adapted source. The periodic polling continues forever; no termination was introduced and no protocol message was removed.
