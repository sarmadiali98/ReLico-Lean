# `core--priority-selection--positive`

This positive benchmark exercises core message-server priority selection with
two recurring local message servers. The source declares `low` with
`@priority(1)` and `high` with `@priority(2)`.

The constructor schedules both `low()` and `high()` with the same `after(1)`
delay, creating simultaneous priority-bearing pending messages. Each message
server then reschedules itself with `after(1)`, so the source continues to
exercise the two-server priority-selection setting.

## Evidence

- source: two local message servers, `low @priority(1)` and
  `high @priority(2)`, scheduled at the same initial delay and recurring;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. This is a
  safety/model-checking witness and is not presented as proof of a particular
  selected runtime ordering;
- parser JSON: both message servers and priority values `1` and `2` are
  represented;
- decoded DTR AST: the two message servers retain priorities `some 1` and
  `some 2`;
- formal witness: 54 DirectLF selection obligations pass across
  `DirectLFSelectionAppend`, `DirectLFSelectionCompatibility`, and
  `DirectLFSelectionRemoval`, including priority-eligibility compatibility,
  append compatibility, removal, and permutation evidence;
- translated LF AST: the corresponding message reactions retain priorities
  `some 1` and `some 2`;
- generated LF source: downstream generation witness;
- `lfc`: successful LF/C++ compilation witness.

Runtime is intentionally excluded from this benchmark. No runtime
scheduling-order claim is made.
