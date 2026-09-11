# ASPIN - adaptation record

Status: **complete** - the approved adaptation set passes the full benchmark pipeline.

Source: `examples.zip:ReLico-main/ASPIN.rebeca`, a 4x4 torus network-on-chip model with one
`Manager`, sixteen `Router` instances, and one packet routed from `r00` to `r23`.

## Property boundary

The archive contains no ASPIN `.property` file. This fixture evaluates translation and runtime
behavior. It does not introduce or encode a property assertion.

## Forced fragment adaptations

### Finite arrays

The four-entry `bufNum`, `full`, `enable`, and `outMutex` arrays are flattened into four scalar
fields each. The constructor loop is expanded, and accesses by `directionS` or `directionD` become
four-way branches. Directions are always literals 0-3 or values forwarded unchanged from those
literals, so each branch selects the same original array cell.

### Integer width

`byte` coordinates, parameters, and buffer entries are widened to `int`, and two `(byte)` casts are
removed. Reachable coordinates are 0-3 and buffer counts are 0-2, so byte truncation and overflow
are unreachable and behavior is preserved.

### Sender identity

The general bridge rejects implicit `sender` reads because LF routing must be static. ASPIN's torus
topology is fully static. Each acknowledgement therefore carries the direction that identifies its
sender in the receiver's local namespace. `get_Ack` uses that tag to release the same directional
mutex. `give_Ack` uses its existing `msgSender` field; initial neighbor sends now populate that field
with the receiver-local incoming direction, and self-retries retain it. No sender distinction is
removed.

### Deadline boundary

The bridge supports `after` but not `deadline`, and it has no statement-form `delay` primitive.
The full-buffer retry retains its original `after(2)` and drops `deadline(3)`; this preserves every
execution in which the deadline is met. The original failure monitor used two messages with
`after(1) deadline(3)` whose `delay(5)` bodies intentionally force a model-checker deadline miss if
the packet has not arrived by time 250. That operational checker failure is represented by a
persistent `deadlineViolation` latch set by `checkPoint`.

This is the smallest executable abstraction that retains the failure observation: deleting the
monitor would erase it, while adding traffic, termination, or a new timing protocol would change
routing behavior. The latch does not gate any protocol action. Because no property is part of this
fixture, the pipeline records translation and runtime behavior rather than asserting the latch.

### Parameterless external sends

`Manager.reset` and `Router.reStart` gain an inert `int unit` parameter because they are external
send targets and LF ports require a payload type. Their bodies do not read it. Parameterless
self-only servers remain unchanged.

No other behavior is intentionally changed. The 4x4 torus bindings, XY routing order, one-packet
scenario, buffer accounting, mutex protocol, acknowledgement flow, retries, packet identifier, and
10/26/250/700 timing values are retained.

## Validation

RMC 2.14 reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`, reaching 942 states and
3,907 transitions. The general parser bridge, all three Lean exports, `lfc 0.11.0`, and the generated
runtime also pass without any further semantic adaptation.
