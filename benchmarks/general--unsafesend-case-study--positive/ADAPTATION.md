# UnsafeSend — adaptation record

Status: **implemented** as `general--unsafesend-case-study--positive`, all eight stages green including `rmc`.

Source: `examples.zip:ReLico-main/UnsafeSend/UnsafeSend.rebeca`, 87 lines, one of the paper's RQ1 verification benchmarks — the deliberately unsafe member of the SafeSend/UnsafeSend pair, where the client sends `0`, the server takes the error path, and the Checker's violation latch fires. The benchmark source is the original under a four-line header comment plus the single adaptation below.

## Original blocker

Measured against the unmodified source (reproduced fresh before any fix):

```
translation failed: message server `Checker`.`errorIn` takes no
parameters, so the port that would carry it has no payload; whether
the target accepts a port with no value is unmeasured
```

The parameterless-external-target boundary — the same refusal as SafeSend's `Checker.errorIn`, AircraftDoor's and Factorial's `KeepAlive.kick`. The other parameterless servers here are self-send targets only (`self.start()`, `self.err()`, `self.latch()`, `self.kick()`, `self.tick()`), which become LF logical actions rather than ports and need nothing.

## Applied adaptation — one marker parameter

`Checker.errorIn()` gains `int unit`; its single external send site, `chk.errorIn()` in `Server.err`, passes the literal `0`. No server body reads `unit`, so no value, message, guard or delay changes — in particular the violation latch's 1-time-unit delay and its firing sequence are untouched.

That is the entire difference from the upstream source. Everything else — classes, priorities, state, logic, timing — is byte-identical apart from the benchmark header comment.

## RMC

`satisfied`, both before the marker parameter (in the corpus RMC screen, which needs no translation) and after it. The marker parameter is observationally inert.
