# Factorial — adaptation record

Status: **implemented** as `general--factorial-case-study--positive`, all eight stages green including `rmc`.

Source: `examples.zip:ReLico-main/Factorial/Factorial.rebeca`, 84 lines, one of the paper's RQ1 verification benchmarks. The benchmark source is the original under a four-line header comment plus the single adaptation below.

## Original blocker

Measured against the unmodified source (reproduced fresh before any fix):

```
translation failed: message server `KeepAlive`.`kick` takes no
parameters, so the port that would carry it has no payload; whether
the target accepts a port with no value is unmeasured
```

The parameterless-external-target boundary — the same refusal that blocked AircraftDoor, TrafficLight, Subway and the tcsma model. Self-sends to parameterless servers (here `self.start()` in `Source`) are unaffected: they become LF logical actions, not ports.

## Applied adaptation — one marker parameter

`KeepAlive.kick()` gains `int unit`; its single external send site, `ka.kick()` in `Source.start`, passes the literal `0`. No server body reads `unit`, so no value, message, guard or delay changes.

That is the entire difference from the upstream source. Everything else — classes, priorities, state, logic, timing — is byte-identical apart from the benchmark header comment.

## RMC

`satisfied`, both before the marker parameter (in the corpus RMC screen, which needs no translation) and after it. The marker parameter is observationally inert.
