# TrainDoor — adaptation record

Status: **implemented** as `general--traindoor-case-study--positive`, all eight stages green including `rmc`.

Source: `examples.zip:ReLico-main/TrainDoor/TrainDoor.rebeca`, 101 lines, one of the paper's RQ1 verification benchmarks. The benchmark source is the original under a five-line header comment plus the single adaptation below.

## Original blocker

Measured against the unmodified source (reproduced fresh before any fix):

```
translation failed: message server `Checker`.`trainEvt` takes no
parameters, so the port that would carry it has no payload; whether
the target accepts a port with no value is unmeasured
```

The parameterless-external-target boundary. This model carries it four times over: `Checker.trainEvt` (sent by `Train.move`), `Checker.doorEvt` (sent by `Door.finishClose`), `Train.move` (sent by `Controller.start`) and `Door.close` (sent by `Controller.start`). The remaining parameterless servers — `Door.finishClose`, `Controller.start`, `KeepAlive.tick` — are self-send targets only, which become LF logical actions rather than ports and need nothing.

## Applied adaptation — four marker parameters

Each of the four servers above gains `int unit`, and each of the four send sites passes the literal `0`: `chk.trainEvt(0)`, `chk.doorEvt(0)`, `t.move(0) after(1)`, `d.close(0) after(1)`. No server body reads `unit`, so no value, message, guard or delay changes — in particular the door's 1-time-unit close delay and the checker's race window are untouched.

That is the entire difference from the upstream source. Everything else — classes, priorities, state, logic, timing — is byte-identical apart from the benchmark header comment.

## RMC

`satisfied`, both before the marker parameters (in the corpus RMC screen, which needs no translation) and after them. The marker parameters are observationally inert.
