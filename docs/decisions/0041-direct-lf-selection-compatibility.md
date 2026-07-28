# Direct-LF selection compatibility

Status: **PAPER DRIFT APPROVED**

Decision: adopt an explicit selection-compatibility condition for the
supported fragment of the direct DTR-to-LF translation.

## Context

DTR dispatch first minimizes metric arrival time and then applies
message-server priority among all pending messages at that time.

LF dispatch first minimizes the complete tag, consisting of metric time and
microstep, and applies reaction declaration order only among actions at the
same complete tag.

Consequently, a same-time LF occurrence at an earlier microstep can overtake a
higher-priority DTR message represented at a later microstep.

## Approved condition

For corresponding pending occurrences at the same DTR arrival time:

- equal LF microsteps defer priority to generated reaction declaration order;
- if one LF occurrence has an earlier microstep, its corresponding DTR message
  server must strictly precede the other under normalized DTR priority.

The condition is quantified over occurrence alignments and is invariant under
permutation of the concrete list representations.

## Scope

The condition:

- is an explicit premise of the direct correctness theorem;
- preserves the ordinary DTR pending-message bag;
- preserves ordinary LF complete-tag semantics;
- keeps LF microsteps entirely on the LF side;
- preserves weak bisimulation as the principal result.

The condition does not introduce source ghost microsteps or modify either
operational semantics.

## Rejected alternatives

- source-side ghost microsteps;
- replacing weak bisimulation with a weaker correctness notion;
- silently excluding all zero-delay sends;
- silently redesigning the generated LF scheduler.
