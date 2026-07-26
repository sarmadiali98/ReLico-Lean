# Zero-delay scheduling and local priority

Status: accepted

Date: 2026-07-26

## Scope

The verified priority-sensitive fragment supports local message-server
priorities within one reactive class.

Actor-instance priorities and global cross-actor priorities are outside the
verified core.

The general DTR and generated-LF semantics continue to support zero-delay
self-sends and zero-delay logical-action scheduling. The additional
positive-delay condition applies specifically to execution-correlation
results that preserve local priority scheduling.

## Confirmed mismatch

Consider two pending occurrences at the same DTR logical time.

- An older occurrence targets a lower-priority message server.
- Execution of another handler creates a new higher-priority occurrence
  using a zero-delay self-send.

After that send, DTR compares both pending occurrences at the same logical
time. Local message-server priority selects the newly created
higher-priority occurrence.

The generated LF execution places the older occurrence at the current
complete tag and the zero-delay occurrence at the next microstep.

Consequently:

```text
DTR:
  old-low @ t
  new-high @ t
  selects new-high

LF:
  old-low @ (t, m)
  new-high @ (t, m + 1)
  selects old-low

The difference is between the newly created occurrence and an occurrence
that was already pending. It is not a disagreement about whether a handler
must execute before the event it creates.

The regression module:

Relico.Tests.ZeroDelayPriorityMismatch

mechanically establishes that:

the new high-priority DTR message is priority eligible;
the old low-priority LF action is reaction-priority eligible;
the new high-priority LF action is not eligible;
the source and target queues satisfy the existing queue-correspondence
relation;
the source queue shape is produced by a zero-delay DTR send;
the target queue shape is produced by the corresponding zero-delay LF
schedule.
Consequence for correctness claims

Weak bisimulation may hide internal statement execution, scheduler
administration, and microstep advancement. It cannot equate different
observable message-consumption or reaction-firing orders.

Therefore, unrestricted zero-delay local-priority preservation is false for
the current mapping.

The existing positive-delay theorem is retained as a valid conservative
result:

strictly positive priority-sensitive sends
→ generated pending actions remain at microstep zero
→ same-time source competitors have the same target tag
→ local priority order is preserved

Zero-delay models remain supported when no priority-sensitive overtaking
claim is required.

Equal-priority ties

Stable normalization currently retains declaration order among equal
explicit priorities and among unannotated message servers.

Whether this is compatible with the intended source semantics remains a
separate proof-scope decision. The final verified fragment must either:

require priority values that uniquely order competing message servers;
prove equal-priority handlers commute observationally;
preserve source tie nondeterminism in the target; or
explicitly define declaration order as part of the supported source
fragment.

No unrestricted equal-priority execution-space claim is made at this
checkpoint.
