# `general--fan-in--positive`

This positive benchmark belongs to the **general** family. It is a purpose-built capability
fixture for fan-in route construction: three sender instances of one class reaching a single
message server on another actor. Fan-in was previously exercised only incidentally through the
actor-priority fixture's two-station contention; this fixture isolates the topology.

## Capability

Three `Sensor` instances, carrying distinct instance priorities 1, 2, and 3 and constructor
seeds 10, 20, and 30, each send `gateway.collect(reading)`. The generated LF program carries
three connections into three per-site input ports on the receiving reactor,
`sensorFirst.collectToGateway -> gateway0.collectToGatewayFromSensorFirst` and its siblings,
which is the per-site port shape many-to-one routing requires. All three deliveries land at one
tag; their order is realized by the senders' distinct instance priorities, the level-1 priority
mechanism, so delivery is deterministic and `latest` records the priority-ordered winner.

## Measurement-forced shapes

Two shapes match the `general--actor-priority--positive` fixture's precedent and are forced by
measurement rather than chosen. The gateway, not the sensors, drives the rounds, and the next
`poll` fires only after all three sensors have answered, counted in `resolved`: free-running
periodic senders overflow the receiving queue under some RMC interleaving, because RMC collapses
the self-rearm delay and lets a sender enqueue faster than the receiver drains. And every
externally sent message server carries a parameter, `request(int round)` and
`collect(int value)`, because the translator refuses a parameterless external target.

## Source provenance

Adapted from the frontend fixture `frontend/fixtures/general/fan-in.rebeca`, preserving that
fixture's objective — several sender instances reaching one receiver with a payload — while
making the model live and finite-state for the mandatory RMC stage. The frontend fixture's
sensors send once and quiesce; this source's gateway-driven request/acknowledge pacing is the
liveness scaffolding around the unchanged capability. The parser JSON is recorded from a real
exporter run of this adapted source and reviewed; the frontend anchor document, which corresponds
to the original source, stays untouched. The mutual known-rebec references between `Sensor` and
`Gateway` follow the accepted `general--pingpong-case-study--positive` topology precedent.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

## Evidence

- source: the commented Timed Rebeca model above;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness, not a claim
  about a particular runtime ordering;
- parser JSON: recorded from a real exporter run and reviewed;
- decoded DTR AST, translated LF AST, LF source, and the formal witness over this benchmark's
  pin module `Relico/Tests/GeneralFanIn.lean`, which pins the three connections, their per-site
  input ports, and the priority-ordered instance list;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target;
- runtime: the generated binary runs in fast mode to the 5 msec logical-time timeout and exits
  0.

## Keep-alive

This model never terminates on its own; the runtime stage's fast-mode timeout is the bounded-run
policy.
