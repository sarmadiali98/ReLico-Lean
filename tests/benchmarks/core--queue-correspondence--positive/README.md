# `core--queue-correspondence--positive`

This positive benchmark exercises core queue correspondence with two
indistinguishable recurring pending occurrences of the same local message
server.

The constructor schedules `tick()` twice with the same `after(1)` delay.
Each `tick()` reaction schedules one successor `tick()` with `after(1)`, so
the model retains a recurring duplicate-occurrence setting rather than
terminating after the initial queue drains.

## Evidence

- source: two same-server `tick()` sends at the same initial logical delay,
  with one successor send produced by each `tick()` reaction;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. This is a
  safety/model-checking witness and is not presented as a proof of a
  particular queue ordering;
- parser JSON and decoded DTR AST: the source sends are represented through
  the frontend route;
- formal witness: 23 obligations across `Correspondence`,
  `DirectLFBagQueueCorrespondence`, and `ForwardSimulation`;
- translated LF AST and LF source: downstream translation/generation
  evidence;
- `lfc`: successful LF/C++ compilation evidence.

The formal scope includes ordinary state/queue correspondence, zero-delay
pending correspondence, reordered bag/queue correspondence, duplicate
source/target removal, and forward matching for assignment and self-send.

Runtime evidence is intentionally excluded. No runtime queue-order claim is
made.
