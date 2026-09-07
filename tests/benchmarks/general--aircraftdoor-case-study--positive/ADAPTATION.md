# AircraftDoor — adaptation record

Status: **implemented** as `general--aircraftdoor-case-study--positive`, all eight stages green including `rmc`.

Source: `examples.zip:ReLico-main/AircraftDoor/AircraftDoor.rebeca`, 110 lines, one of the paper's RQ1 verification benchmarks. The benchmark source is the original under a four-line header comment plus the single adaptation below.

## Original blocker

Measured against the unmodified source (reproduced fresh before any fix):

```
translation failed: message server `KeepAlive`.`kick` takes no
parameters, so the port that would carry it has no payload; whether
the target accepts a port with no value is unmeasured
```

The known parameterless-external-target boundary, the same refusal that blocked TrafficLight, Subway and the tcsma model in the tier-2 runs, and that the suite has resolved with marker parameters three times before.

## Applied adaptation — one marker parameter

`KeepAlive.kick()` gains `int unit`; its single external send site, `ka.kick()` in `Controller.start`, passes the literal `0`. No server body reads `unit`, so no value, message, guard or delay changes: the parameter exists so the LF port carrying the send has a value type.

That is the entire difference from the upstream source. Everything else — classes, priorities, state, logic, timing — is byte-identical apart from the benchmark header comment.

## RMC

`satisfied`, both before the marker parameter (in the corpus RMC screen, which needs no translation) and after it, on the translated source. The marker parameter is observationally inert.
