# SafeSend — adaptation record

Status: **implemented** as `general--safesend-case-study--positive`, all eight stages green including `rmc`.

Source: `examples.zip:ReLico-main/SafeSend/SafeSend.rebeca`, 99 lines, one of the paper's RQ1 verification benchmarks. The benchmark source is the original under a four-line header comment plus the single adaptation below.

## Original blocker

Measured against the unmodified source (reproduced fresh before any fix):

```
translation failed: message server `Checker`.`errorIn` takes no
parameters, so the port that would carry it has no payload; whether
the target accepts a port with no value is unmeasured
```

The parameterless-external-target boundary — the same refusal that blocked AircraftDoor and Factorial (`KeepAlive.kick`). The other parameterless servers here are self-send targets only (`self.start()`, `self.err()`, `self.tick()`), which become LF logical actions rather than ports and need nothing.

## Applied adaptation — one marker parameter

`Checker.errorIn()` gains `int unit`; its single external send site, `chk.errorIn()` in `Server.err`, passes the literal `0`. No server body reads `unit`, so no value, message, guard or delay changes.

That is the entire difference from the upstream source. Everything else — classes, priorities, state, logic, timing — is byte-identical apart from the benchmark header comment.

## RMC

`satisfied`, both before the marker parameter (in the corpus RMC screen, which needs no translation) and after it. The marker parameter is observationally inert.
